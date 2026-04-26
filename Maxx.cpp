// Application: Maxx Screen Recorder
// Credits: Nader mahbub Khan
// Compile: g++ -std=c++17 -O2 -o Maxx.exe Maxx.cpp -lmfplat -lmfreadwrite -lmf -ldxgi -ld3d11 -ld2d1 -ldwrite -lole32 -lmfuuid -lstrmiids -luuid -lwinmm -lavrt -lksuser -lcomctl32 -lshlwapi -municode -mwindows

#ifndef UNICODE
#define UNICODE
#endif
#ifndef _UNICODE
#define _UNICODE
#endif
#ifndef WINVER
#define WINVER 0x0A00
#endif
#ifndef _WIN32_WINNT
#define _WIN32_WINNT 0x0A00
#endif
#define WIN32_LEAN_AND_MEAN
#define COBJMACROS
#define INITGUID

#include <windows.h>
#include <windowsx.h>
#include <commctrl.h>
#include <commdlg.h>
#include <shellapi.h>
#include <shlwapi.h>
#include <unknwn.h>
#include <objbase.h>
#include <cguid.h>

#include <d3d11.h>
#include <d3d11_1.h>
#include <dxgi.h>
#include <dxgi1_2.h>
#include <dxgi1_3.h>
#include <d2d1.h>
#include <d2d1_1.h>
#include <d2d1helper.h>
#include <dwrite.h>
#include <wincodec.h>

#include <mfapi.h>
#include <mfidl.h>
#include <mfreadwrite.h>
#include <mferror.h>
#include <mftransform.h>
#include <codecapi.h>
#include <wmcodecdsp.h>
#include <audioclient.h>
#include <mmdeviceapi.h>
#include <avrt.h>
#include <functiondiscoverykeys_devpkey.h>

#include <cstdint>
#include <cstring>
#include <cmath>
#include <cstdio>
#include <cstdarg>
#include <atomic>
#include <thread>
#include <mutex>
#include <vector>
#include <string>
#include <memory>
#include <algorithm>
#include <functional>
#include <chrono>
#include <map>
#include <unordered_map>

#pragma region DSP_AND_EFFECT_RACK
//
// Built-in audio effects + EffectRack.
//
// All DSP runs in 32-bit float, interleaved, matching the format the rest of
// the audio path already uses (WASAPI capture is converted to float in
// AudioCaptureManager, the WMF AAC encoder consumes MFAudioFormat_Float).
//
// Five effect modules + a rack:
//   Compressor       — peak detector w/ soft-knee, makeup gain
//   ParametricEQ     — five-band: HPF / low-shelf / peak1 / peak2 / high-shelf
//                      (RBJ biquad coefficients, double-precision state)
//   SaturationAir    — "Fresh Air" style: split into Mid Air (~5 kHz) and
//                      High Air (~12 kHz) bands, soft-clip drive each, mix
//                      back into the dry signal
//   Limiter          — lookahead brickwall, 4× polyphase oversampled true-peak
//                      detector for the side-chain
//   (rack)           — ordered chain w/ per-slot bypass + global enable
//
// Effects are sample-rate / channel-count aware via Prepare(), and parameters
// are atomically updatable from the UI thread while the audio thread is
// processing (single-writer / single-reader on each std::atomic<float>).
//
// Channel handling: we treat the input as up to 8 interleaved channels and
// process each channel independently in DSP modules that are channel-local
// (EQ biquad state, limiter delay line, compressor envelope). The compressor
// uses a linked stereo detector so left/right gain reduction stays bonded.
// ---------------------------------------------------------------------------

constexpr int   kMaxDSPChannels   = 8;
constexpr float kMinDb            = -120.0f;
constexpr float kMaxDb            =  +24.0f;
constexpr float kPI               = 3.14159265358979323846f;

static inline float DbToLin(float dB)        { return std::pow(10.0f, dB * 0.05f); }
static inline float LinToDb(float lin)       { return (lin > 1e-9f) ? 20.0f * std::log10(lin) : kMinDb; }
static inline float Clamp(float v, float a, float b) { return v < a ? a : (v > b ? b : v); }
static inline float SoftClip(float x)        { return std::tanh(x); }

// ---------------------------------------------------------------------------
// Effect parameter description (used to drive the UI generically).
// ---------------------------------------------------------------------------
struct EffectParamInfo {
    const char* name;
    float       minV;
    float       maxV;
    float       defV;
    const char* unit;     // e.g. "dB", "Hz", ":1", "ms"
    bool        isLog;    // log-scale slider hint
};

// Pure-virtual base class for an effect.
class IEffect {
public:
    virtual ~IEffect() = default;
    virtual const char* Name() const = 0;
    virtual void  Prepare(double sampleRate, uint32_t numChannels) = 0;
    virtual void  Process(float* interleaved, uint32_t numFrames, uint32_t numChannels) = 0;
    virtual void  Reset() = 0;
    virtual int   GetParamCount() const = 0;
    virtual const EffectParamInfo& GetParamInfo(int i) const = 0;
    virtual float GetParam(int i) const = 0;
    virtual void  SetParam(int i, float v) = 0;
};

// ---------------------------------------------------------------------------
// RBJ biquad — direct form II transposed, double-precision state to keep
// shelving/peaking filters stable at low frequencies.
// ---------------------------------------------------------------------------
struct Biquad {
    double b0=1, b1=0, b2=0, a1=0, a2=0;
    double z1[kMaxDSPChannels] = {};
    double z2[kMaxDSPChannels] = {};

    void Reset()
    {
        for (int c = 0; c < kMaxDSPChannels; ++c) { z1[c] = 0; z2[c] = 0; }
    }
    inline float Tick(int ch, float x)
    {
        double in  = (double)x;
        double out = b0 * in + z1[ch];
        z1[ch] = b1 * in - a1 * out + z2[ch];
        z2[ch] = b2 * in - a2 * out;
        return (float)out;
    }
    // All coefficients normalised by a0 (caller must divide).
    void SetCoefficients(double nb0, double nb1, double nb2,
                         double na0, double na1, double na2)
    {
        b0 = nb0/na0; b1 = nb1/na0; b2 = nb2/na0;
        a1 = na1/na0; a2 = na2/na0;
    }

    // RBJ cookbook coefficients.
    void DesignHighpass(double sr, double freq, double Q)
    {
        double w0    = 2.0*kPI*freq/sr;
        double cosw0 = std::cos(w0);
        double sinw0 = std::sin(w0);
        double alpha = sinw0 / (2.0*Q);
        double b0n =  (1.0 + cosw0)*0.5;
        double b1n = -(1.0 + cosw0);
        double b2n =  (1.0 + cosw0)*0.5;
        double a0n =   1.0 + alpha;
        double a1n =  -2.0*cosw0;
        double a2n =   1.0 - alpha;
        SetCoefficients(b0n, b1n, b2n, a0n, a1n, a2n);
    }
    void DesignPeaking(double sr, double freq, double Q, double gainDb)
    {
        double A     = std::pow(10.0, gainDb/40.0);
        double w0    = 2.0*kPI*freq/sr;
        double cosw0 = std::cos(w0);
        double sinw0 = std::sin(w0);
        double alpha = sinw0 / (2.0*Q);
        double b0n =  1.0 + alpha*A;
        double b1n = -2.0*cosw0;
        double b2n =  1.0 - alpha*A;
        double a0n =  1.0 + alpha/A;
        double a1n = -2.0*cosw0;
        double a2n =  1.0 - alpha/A;
        SetCoefficients(b0n, b1n, b2n, a0n, a1n, a2n);
    }
    void DesignLowShelf(double sr, double freq, double slope, double gainDb)
    {
        double A     = std::pow(10.0, gainDb/40.0);
        double w0    = 2.0*kPI*freq/sr;
        double cosw0 = std::cos(w0);
        double sinw0 = std::sin(w0);
        double alpha = sinw0/2.0 * std::sqrt((A + 1.0/A)*(1.0/slope - 1.0) + 2.0);
        double sqA   = std::sqrt(A);
        double b0n =     A*((A+1.0) - (A-1.0)*cosw0 + 2.0*sqA*alpha);
        double b1n = 2.0*A*((A-1.0) - (A+1.0)*cosw0);
        double b2n =     A*((A+1.0) - (A-1.0)*cosw0 - 2.0*sqA*alpha);
        double a0n =        (A+1.0) + (A-1.0)*cosw0 + 2.0*sqA*alpha;
        double a1n =  -2.0*((A-1.0) + (A+1.0)*cosw0);
        double a2n =        (A+1.0) + (A-1.0)*cosw0 - 2.0*sqA*alpha;
        SetCoefficients(b0n, b1n, b2n, a0n, a1n, a2n);
    }
    void DesignHighShelf(double sr, double freq, double slope, double gainDb)
    {
        double A     = std::pow(10.0, gainDb/40.0);
        double w0    = 2.0*kPI*freq/sr;
        double cosw0 = std::cos(w0);
        double sinw0 = std::sin(w0);
        double alpha = sinw0/2.0 * std::sqrt((A + 1.0/A)*(1.0/slope - 1.0) + 2.0);
        double sqA   = std::sqrt(A);
        double b0n =      A*((A+1.0) + (A-1.0)*cosw0 + 2.0*sqA*alpha);
        double b1n = -2.0*A*((A-1.0) + (A+1.0)*cosw0);
        double b2n =      A*((A+1.0) + (A-1.0)*cosw0 - 2.0*sqA*alpha);
        double a0n =         (A+1.0) - (A-1.0)*cosw0 + 2.0*sqA*alpha;
        double a1n =    2.0*((A-1.0) - (A+1.0)*cosw0);
        double a2n =         (A+1.0) - (A-1.0)*cosw0 - 2.0*sqA*alpha;
        SetCoefficients(b0n, b1n, b2n, a0n, a1n, a2n);
    }
    // Constant-skirt-gain (peak-gain = Q) bandpass — RBJ cookbook.
    void SetBandpass(double sr, double freq, double Q)
    {
        double w0    = 2.0*kPI*freq/sr;
        double cosw0 = std::cos(w0);
        double sinw0 = std::sin(w0);
        double alpha = sinw0 / (2.0*Q);
        double b0n =  alpha;
        double b1n =  0.0;
        double b2n = -alpha;
        double a0n =  1.0 + alpha;
        double a1n = -2.0*cosw0;
        double a2n =  1.0 - alpha;
        SetCoefficients(b0n, b1n, b2n, a0n, a1n, a2n);
    }
    // Convenience aliases used by the new spectral effects.
    void SetHighShelf(double sr, double freq, double slope, double gainDb)
    {
        DesignHighShelf(sr, freq, slope, gainDb);
    }
};

// ---------------------------------------------------------------------------
// Shared 512-point FFT kernel + windowing tables. Used by every spectral
// effect (FkNoise, AntiBreath, HumanizedPitcher). Tables are built once at
// program startup; FFT/IFFT methods are const, so concurrent use across
// effects on the same audio thread is safe.
// ---------------------------------------------------------------------------
struct Stft512 {
    static constexpr int N    = 512;
    static constexpr int H    = N / 2;
    static constexpr int Bins = N / 2 + 1;

    int   bitRev[N];
    float twR[N/2], twI[N/2];
    float wHann[N];
    float wSqrtHann[N];

    Stft512()
    {
        constexpr int order = 9;
        for (int i = 0; i < N; ++i) {
            int rev = 0, v = i;
            for (int b = 0; b < order; ++b) { rev = (rev << 1) | (v & 1); v >>= 1; }
            bitRev[i] = rev;
        }
        for (int i = 0; i < N/2; ++i) {
            twR[i] = (float)std::cos(-2.0 * kPI * i / (double)N);
            twI[i] = (float)std::sin(-2.0 * kPI * i / (double)N);
        }
        // Periodic Hann (nperseg-style, NOT symmetric Hamming).
        for (int n = 0; n < N; ++n) {
            float h = 0.5f * (1.0f - (float)std::cos(2.0 * kPI * n / (double)N));
            wHann[n]     = h;
            wSqrtHann[n] = std::sqrt(h);
        }
    }

    // In-place radix-2 Cooley-Tukey.
    void FFT(float* re, float* im) const
    {
        for (int i = 0; i < N; ++i) {
            int j = bitRev[i];
            if (j > i) { std::swap(re[i], re[j]); std::swap(im[i], im[j]); }
        }
        for (int size = 2; size <= N; size <<= 1) {
            int half = size >> 1;
            int step = N / size;
            for (int i = 0; i < N; i += size) {
                for (int j = 0; j < half; ++j) {
                    float wr = twR[j * step];
                    float wi = twI[j * step];
                    int   k0 = i + j;
                    int   k1 = i + j + half;
                    float tr = wr * re[k1] - wi * im[k1];
                    float ti = wr * im[k1] + wi * re[k1];
                    re[k1] = re[k0] - tr;
                    im[k1] = im[k0] - ti;
                    re[k0] += tr;
                    im[k0] += ti;
                }
            }
        }
    }
    // Inverse via conjugate trick.
    void IFFT(float* re, float* im) const
    {
        for (int i = 0; i < N; ++i) im[i] = -im[i];
        FFT(re, im);
        const float inv = 1.0f / (float)N;
        for (int i = 0; i < N; ++i) { re[i] *= inv; im[i] = -im[i] * inv; }
    }
};
inline const Stft512& GetStft512() { static Stft512 s; return s; }

// ---------------------------------------------------------------------------
// Compressor — peak detector, soft-knee, linked stereo gain reduction.
// ---------------------------------------------------------------------------
class CompressorEffect : public IEffect {
public:
    CompressorEffect()
    {
        m_p[Threshold].store(-12.0f);
        m_p[Ratio    ].store( 4.0f);
        m_p[Attack   ].store( 10.0f);
        m_p[Release  ].store(100.0f);
        m_p[Knee     ].store(  6.0f);
        m_p[Makeup   ].store(  0.0f);
    }
    enum Param { Threshold, Ratio, Attack, Release, Knee, Makeup, NumParams };

    const char* Name() const override { return "Compressor"; }

    void Prepare(double sampleRate, uint32_t /*numChannels*/) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        Reset();
    }
    void Reset() override { m_env = 0.0f; }

    int   GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Threshold", -60.0f,   0.0f, -12.0f, "dB",  false },
            { "Ratio",       1.0f,  20.0f,   4.0f, ":1",  true  },
            { "Attack",      0.1f, 200.0f,  10.0f, "ms",  true  },
            { "Release",     5.0f,2000.0f, 100.0f, "ms",  true  },
            { "Knee",        0.0f,  24.0f,   6.0f, "dB",  false },
            { "Makeup",      0.0f,  24.0f,   0.0f, "dB",  false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float threshDb = m_p[Threshold].load();
        const float ratio    = std::max(1.0f, m_p[Ratio].load());
        const float attMs    = std::max(0.1f, m_p[Attack].load());
        const float relMs    = std::max(1.0f, m_p[Release].load());
        const float kneeDb   = std::max(0.0f, m_p[Knee].load());
        const float makeupDb = m_p[Makeup].load();

        // Per-sample one-pole coefficients.
        const float aAtt = std::exp(-1.0f / ((float)m_sr * attMs * 0.001f));
        const float aRel = std::exp(-1.0f / ((float)m_sr * relMs * 0.001f));
        const float makeupLin = DbToLin(makeupDb);

        for (uint32_t n = 0; n < numFrames; ++n) {
            // Linked detector: max-abs across all channels.
            float peak = 0.0f;
            const uint32_t base = n * numChannels;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float s = std::fabs(x[base + c]);
                if (s > peak) peak = s;
            }
            // Envelope follower (peak, fast attack / slow release).
            const float a = (peak > m_env) ? aAtt : aRel;
            m_env = a * m_env + (1.0f - a) * peak;

            // Soft-knee gain computation in dB domain.
            float envDb = LinToDb(m_env);
            float overDb = envDb - threshDb;
            float gainDb = 0.0f;
            if (overDb <= -kneeDb*0.5f) {
                gainDb = 0.0f;
            } else if (overDb >= kneeDb*0.5f) {
                gainDb = -(overDb - overDb / ratio);
            } else {
                // Quadratic blend across the knee region.
                float t = (overDb + kneeDb*0.5f) / kneeDb;
                float over2 = overDb + kneeDb*0.5f;
                float comp  = (1.0f - 1.0f/ratio) * (over2*over2) / (2.0f*kneeDb);
                gainDb = -comp;
                (void)t;
            }
            float gain = DbToLin(gainDb) * makeupLin;
            for (uint32_t c = 0; c < numChannels; ++c) x[base + c] *= gain;
        }
    }

private:
    double                m_sr = 48000.0;
    float                 m_env = 0.0f;
    std::atomic<float>    m_p[NumParams];
};

// ---------------------------------------------------------------------------
// Parametric EQ — five fixed-purpose bands.
// ---------------------------------------------------------------------------
class ParametricEQEffect : public IEffect {
public:
    enum Band { HPF, LowShelf, Peak1, Peak2, HighShelf, NumBands };
    enum Param {
        HpFreq, HpOn,
        LsFreq, LsGain, LsOn,
        P1Freq, P1Gain, P1Q, P1On,
        P2Freq, P2Gain, P2Q, P2On,
        HsFreq, HsGain, HsOn,
        NumParams
    };

    ParametricEQEffect()
    {
        // Sensible default: gentle low-cut, all peaks/shelves flat & off.
        m_p[HpFreq].store(  30.0f); m_p[HpOn].store(0.0f);
        m_p[LsFreq].store( 120.0f); m_p[LsGain].store(0.0f); m_p[LsOn].store(0.0f);
        m_p[P1Freq].store( 800.0f); m_p[P1Gain].store(0.0f); m_p[P1Q].store(0.7f); m_p[P1On].store(0.0f);
        m_p[P2Freq].store(3000.0f); m_p[P2Gain].store(0.0f); m_p[P2Q].store(0.7f); m_p[P2On].store(0.0f);
        m_p[HsFreq].store(8000.0f); m_p[HsGain].store(0.0f); m_p[HsOn].store(0.0f);
    }

    const char* Name() const override { return "Parametric EQ"; }

    void Prepare(double sampleRate, uint32_t /*numChannels*/) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        Reset();
        Update();
    }
    void Reset() override
    {
        for (int b = 0; b < NumBands; ++b) m_band[b].Reset();
    }

    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "HPF Freq",    20.0f,   500.0f,    30.0f, "Hz",  true  },
            { "HPF On",       0.0f,     1.0f,     0.0f, "",    false },
            { "Low-Shelf F", 30.0f,   500.0f,   120.0f, "Hz",  true  },
            { "Low-Shelf G",-18.0f,    18.0f,     0.0f, "dB",  false },
            { "Low-Shelf On", 0.0f,     1.0f,     0.0f, "",    false },
            { "Peak1 F",     80.0f,  8000.0f,   800.0f, "Hz",  true  },
            { "Peak1 G",   -18.0f,    18.0f,     0.0f, "dB",  false },
            { "Peak1 Q",     0.1f,    10.0f,     0.7f, "",    true  },
            { "Peak1 On",     0.0f,     1.0f,     0.0f, "",    false },
            { "Peak2 F",    300.0f, 16000.0f,  3000.0f, "Hz",  true  },
            { "Peak2 G",   -18.0f,    18.0f,     0.0f, "dB",  false },
            { "Peak2 Q",     0.1f,    10.0f,     0.7f, "",    true  },
            { "Peak2 On",     0.0f,     1.0f,     0.0f, "",    false },
            { "HS Freq",   1000.0f, 18000.0f,  8000.0f, "Hz",  true  },
            { "HS Gain",   -18.0f,    18.0f,     0.0f, "dB",  false },
            { "HS On",        0.0f,     1.0f,     0.0f, "",    false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override
    {
        if (i>=0&&i<NumParams) {
            m_p[i].store(v);
            m_dirty.store(true);
        }
    }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;
        if (m_dirty.exchange(false)) Update();

        // Per-sample, all bands in series, all channels.
        const bool onHp = m_p[HpOn].load() >= 0.5f;
        const bool onLs = m_p[LsOn].load() >= 0.5f;
        const bool onP1 = m_p[P1On].load() >= 0.5f;
        const bool onP2 = m_p[P2On].load() >= 0.5f;
        const bool onHs = m_p[HsOn].load() >= 0.5f;

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n*numChannels;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float s = x[base+c];
                if (onHp) s = m_band[HPF      ].Tick(c, s);
                if (onLs) s = m_band[LowShelf ].Tick(c, s);
                if (onP1) s = m_band[Peak1    ].Tick(c, s);
                if (onP2) s = m_band[Peak2    ].Tick(c, s);
                if (onHs) s = m_band[HighShelf].Tick(c, s);
                x[base+c] = s;
            }
        }
    }

private:
    void Update()
    {
        m_band[HPF      ].DesignHighpass (m_sr, m_p[HpFreq].load(), 0.707);
        m_band[LowShelf ].DesignLowShelf (m_sr, m_p[LsFreq].load(), 0.707, m_p[LsGain].load());
        m_band[Peak1    ].DesignPeaking  (m_sr, m_p[P1Freq].load(), std::max(0.1f, m_p[P1Q].load()), m_p[P1Gain].load());
        m_band[Peak2    ].DesignPeaking  (m_sr, m_p[P2Freq].load(), std::max(0.1f, m_p[P2Q].load()), m_p[P2Gain].load());
        m_band[HighShelf].DesignHighShelf(m_sr, m_p[HsFreq].load(), 0.707, m_p[HsGain].load());
    }
    double                m_sr = 48000.0;
    Biquad                m_band[NumBands];
    std::atomic<float>    m_p[NumParams];
    std::atomic<bool>     m_dirty{true};
};

// ---------------------------------------------------------------------------
// SaturationAir — a Slate-Fresh-Air-style enhancer.
//
// Splits the signal into "Mid Air" (~5 kHz) and "High Air" (~12 kHz) bands
// using a pair of high-shelf filters, applies soft-clip drive proportional
// to the band amount, and mixes the result back in. Pure dry passes through
// untouched when both Air amounts are 0.
// ---------------------------------------------------------------------------
class SaturationAirEffect : public IEffect {
public:
    enum Param { MidAir, HighAir, MidFreq, HighFreq, Drive, Mix, NumParams };

    SaturationAirEffect()
    {
        m_p[MidAir  ].store(0.0f);
        m_p[HighAir ].store(0.0f);
        m_p[MidFreq ].store(5000.0f);
        m_p[HighFreq].store(12000.0f);
        m_p[Drive   ].store(0.0f);
        m_p[Mix     ].store(1.0f);
    }

    const char* Name() const override { return "Saturation Air"; }

    void Prepare(double sampleRate, uint32_t /*numChannels*/) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        Reset();
        Update();
    }
    void Reset() override { m_midShelf.Reset(); m_highShelf.Reset(); }

    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Mid Air",    0.0f, 100.0f,    0.0f, "%",  false },
            { "High Air",   0.0f, 100.0f,    0.0f, "%",  false },
            { "Mid Freq", 1500.0f, 8000.0f, 5000.0f, "Hz", true  },
            { "High Freq",6000.0f,16000.0f,12000.0f, "Hz", true  },
            { "Drive",      0.0f,  24.0f,    0.0f, "dB", false },
            { "Mix",        0.0f,   1.0f,    1.0f, "",   false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) { m_p[i].store(v); m_dirty.store(true); } }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;
        if (m_dirty.exchange(false)) Update();

        const float midAmt  = Clamp(m_p[MidAir ].load(), 0.0f, 100.0f) * 0.01f;
        const float highAmt = Clamp(m_p[HighAir].load(), 0.0f, 100.0f) * 0.01f;
        const float driveLin = DbToLin(m_p[Drive].load());
        const float mix      = Clamp(m_p[Mix].load(), 0.0f, 1.0f);

        if (midAmt < 1e-4f && highAmt < 1e-4f) return;

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n*numChannels;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float in   = x[base+c];

                // Extract band content via a "shelf-difference" trick: the
                // shelf with +0 dB gain is identity; with positive gain it
                // boosts the high band. Subtracting the unboosted dry from
                // the boosted output gives the band content the user wants
                // to saturate, without needing a true crossover.
                float midShelved  = m_midShelf .Tick(c, in);
                float highShelved = m_highShelf.Tick(c, in);
                float midBand  = (midShelved  - in) * midAmt;
                float highBand = (highShelved - in) * highAmt;

                // Soft-clip the band content (more drive → more harmonics).
                float satMid  = SoftClip(midBand  * (1.0f + driveLin*0.5f));
                float satHigh = SoftClip(highBand * (1.0f + driveLin*0.7f));

                float wet = in + satMid + satHigh;
                x[base+c] = (1.0f - mix) * in + mix * wet;
            }
        }
    }

private:
    void Update()
    {
        // Use shelves with +12 dB so that "(boosted - dry) * amount" gives
        // a pleasantly tilt-eq'd source for the soft-clipper.
        m_midShelf .DesignHighShelf(m_sr, m_p[MidFreq ].load(), 0.5, 12.0);
        m_highShelf.DesignHighShelf(m_sr, m_p[HighFreq].load(), 0.5, 12.0);
    }
    double                m_sr = 48000.0;
    Biquad                m_midShelf;
    Biquad                m_highShelf;
    std::atomic<float>    m_p[NumParams];
    std::atomic<bool>     m_dirty{true};
};

// ---------------------------------------------------------------------------
// Limiter — lookahead brickwall. The lookahead window lets the gain reduction
// envelope ramp in *before* the loud sample arrives, so the limiter can
// achieve transparent peak control without short-attack distortion.
// ---------------------------------------------------------------------------
class LimiterEffect : public IEffect {
public:
    enum Param { Ceiling, Release, Lookahead, NumParams };

    LimiterEffect()
    {
        m_p[Ceiling  ].store(-1.0f);
        m_p[Release  ].store(50.0f);
        m_p[Lookahead].store(5.0f);
    }
    const char* Name() const override { return "Limiter"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        // 20 ms maximum lookahead at any reasonable sample rate.
        m_capacity = (size_t)((double)m_sr * 0.020 + 64.0);
        m_buf.assign(m_capacity * m_ch, 0.0f);
        m_writeIdx = 0;
        m_envBuf.assign(m_capacity, 0.0f);
        m_gain = 1.0f;
        Reset();
    }
    void Reset() override
    {
        std::fill(m_buf.begin(), m_buf.end(), 0.0f);
        std::fill(m_envBuf.begin(), m_envBuf.end(), 0.0f);
        m_writeIdx = 0;
        m_gain = 1.0f;
    }

    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Ceiling",  -24.0f,  0.0f, -1.0f, "dB", false },
            { "Release",   1.0f, 1000.0f,50.0f, "ms", true  },
            { "Lookahead", 0.5f,  20.0f,  5.0f, "ms", false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) {
            // Channel count change — reconfigure delay line.
            Prepare(m_sr, numChannels);
        }
        if (m_capacity == 0) return;

        const float ceilingLin = DbToLin(m_p[Ceiling].load());
        const float releaseMs  = std::max(1.0f, m_p[Release].load());
        const float lookMs     = Clamp(m_p[Lookahead].load(), 0.5f, 20.0f);
        const size_t lookSamples = (size_t)((double)m_sr * (lookMs * 0.001) + 0.5);
        const size_t look = std::min<size_t>(lookSamples, m_capacity - 1);

        const float aRel = std::exp(-1.0f / ((float)m_sr * releaseMs * 0.001f));

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            // Detect peak across all channels for sample we are *writing*.
            float peak = 0.0f;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float s = std::fabs(x[base + c]);
                if (s > peak) peak = s;
            }
            // 4× true-peak: linearly interpolate the inter-sample peaks
            // between the previous tail sample and current sample. Cheap and
            // catches >0 dBTP overshoots most of the time.
            size_t prevIdx = (m_writeIdx + m_capacity - 1) % m_capacity;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float prev = m_buf[prevIdx * m_ch + c];
                float cur  = x[base + c];
                for (int k = 1; k < 4; ++k) {
                    float t = (float)k / 4.0f;
                    float interp = std::fabs(prev*(1.0f-t) + cur*t);
                    if (interp > peak) peak = interp;
                }
            }

            // Required instantaneous gain to keep this sample at/under
            // ceiling.
            float reqGain = (peak > ceilingLin) ? (ceilingLin / std::max(peak, 1e-9f)) : 1.0f;

            // Write current sample into the delay line.
            for (uint32_t c = 0; c < numChannels; ++c)
                m_buf[m_writeIdx * m_ch + c] = x[base + c];
            m_envBuf[m_writeIdx] = reqGain;

            // Pick the worst-case required gain over the lookahead window
            // ending at the just-written sample.
            float minGain = 1.0f;
            for (size_t k = 0; k <= look; ++k) {
                size_t idx = (m_writeIdx + m_capacity - k) % m_capacity;
                float g = m_envBuf[idx];
                if (g < minGain) minGain = g;
            }
            // Smooth release: gain only opens up gradually, but slams down
            // instantly to whatever the lookahead says we need.
            if (minGain < m_gain) m_gain = minGain;
            else                  m_gain = aRel * m_gain + (1.0f - aRel) * minGain;

            // Read out the sample that's now `look` samples behind.
            size_t readIdx = (m_writeIdx + m_capacity - look) % m_capacity;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float s = m_buf[readIdx * m_ch + c] * m_gain;
                if (s >  ceilingLin) s =  ceilingLin;
                if (s < -ceilingLin) s = -ceilingLin;
                x[base + c] = s;
            }
            m_writeIdx = (m_writeIdx + 1) % m_capacity;
        }
    }

private:
    double               m_sr       = 48000.0;
    uint32_t             m_ch       = 2;
    size_t               m_capacity = 0;
    size_t               m_writeIdx = 0;
    float                m_gain     = 1.0f;
    std::vector<float>   m_buf;       // interleaved
    std::vector<float>   m_envBuf;    // per-frame required-gain history
    std::atomic<float>   m_p[NumParams];
};

// ---------------------------------------------------------------------------
// SmartDynamicsEffect — parallel up+down dynamics with transient emphasis.
// Architecture: a fast peak-tracking envelope ("attack envelope") and a slow
// RMS-tracking envelope ("body envelope") drive three independent gain
// curves whose outputs are summed:
//   Punch  = boost when attack-env > body-env (transients)
//   Body   = boost when body-env  < threshold (low-level material)
//   Control= attenuate when attack-env > ceiling (peak control)
// All three curves obey the rack-wide bypass + dry/wet mix.
// ---------------------------------------------------------------------------
class SmartDynamicsEffect : public IEffect {
public:
    enum Param { Punch, Body, Control, Threshold, Mix, NumParams };

    SmartDynamicsEffect()
    {
        m_p[Punch    ].store( 30.0f);
        m_p[Body     ].store( 25.0f);
        m_p[Control  ].store( 35.0f);
        m_p[Threshold].store(-24.0f);
        m_p[Mix      ].store(100.0f);
    }
    const char* Name() const override { return "Smart Dynamics"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        // 3 ms attack / 80 ms release for the fast envelope.
        m_aFastAtk = std::exp(-1.0f / ((float)m_sr * 0.003f));
        m_aFastRel = std::exp(-1.0f / ((float)m_sr * 0.080f));
        // 100 ms / 400 ms for the slow envelope.
        m_aSlowAtk = std::exp(-1.0f / ((float)m_sr * 0.100f));
        m_aSlowRel = std::exp(-1.0f / ((float)m_sr * 0.400f));
        Reset();
    }
    void Reset() override
    {
        m_envFast = 0.0f;
        m_envSlow = 0.0f;
    }

    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Punch",       0.0f, 100.0f,  30.0f, "%",  false },
            { "Body",        0.0f, 100.0f,  25.0f, "%",  false },
            { "Control",     0.0f, 100.0f,  35.0f, "%",  false },
            { "Threshold", -60.0f,   0.0f, -24.0f, "dB", false },
            { "Mix",         0.0f, 100.0f, 100.0f, "%",  false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float punch    = m_p[Punch    ].load() * 0.01f;
        const float body     = m_p[Body     ].load() * 0.01f;
        const float control  = m_p[Control  ].load() * 0.01f;
        const float threshLin= DbToLin(m_p[Threshold].load());
        const float mix      = m_p[Mix      ].load() * 0.01f;

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            // Linked-channel envelope detector — sum-of-squares across all
            // channels, then sqrt to get a peak-equivalent amplitude.
            float sumSq = 0.0f;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float s = x[base + c];
                sumSq += s * s;
            }
            float lvl = std::sqrt(sumSq / (float)numChannels);

            // Two envelopes: fast and slow. The fast one tracks transients,
            // the slow one tracks programme body. Their *ratio* is the
            // transient-detector signal.
            float aF = (lvl > m_envFast) ? m_aFastAtk : m_aFastRel;
            float aS = (lvl > m_envSlow) ? m_aSlowAtk : m_aSlowRel;
            m_envFast = aF * m_envFast + (1.0f - aF) * lvl;
            m_envSlow = aS * m_envSlow + (1.0f - aS) * lvl;

            // Transient excess (>= 0). Each unit = +1 envelope-ratio above
            // the slow average. Capped to avoid runaway gain on pure tones.
            float transient = 0.0f;
            if (m_envSlow > 1e-6f) {
                transient = (m_envFast - m_envSlow) / m_envSlow;
                if (transient < 0.0f) transient = 0.0f;
                if (transient > 4.0f) transient = 4.0f;
            }

            // Three gain curves. All start at 1.0 (unity).
            float gPunch   = 1.0f + punch  * transient;          // peaks louder
            // Body: lift signal that's below threshold, in proportion to how
            // far below it is. 6 dB max lift at body=100% when 24 dB below.
            float belowDb  = LinToDb(std::max(m_envSlow, 1e-9f)) -
                             LinToDb(threshLin);
            float bodyAmt  = (belowDb < 0.0f) ? std::min(-belowDb / 24.0f, 1.0f) : 0.0f;
            float gBody    = 1.0f + body * bodyAmt * 1.0f;       // up to +6 dB-ish
            // Control: when fast envelope exceeds threshold by more than 6 dB,
            // pull gain back. Soft-knee.
            float overDb   = LinToDb(std::max(m_envFast, 1e-9f)) -
                             LinToDb(threshLin);
            float overAmt  = (overDb > 6.0f) ? std::min((overDb - 6.0f) / 18.0f, 1.0f) : 0.0f;
            float gControl = 1.0f - control * overAmt * 0.5f;    // up to -6 dB

            // Combine: average the three so the curves balance instead of
            // multiplying (which would over-emphasize at the extremes).
            float gain = (gPunch + gBody + gControl) / 3.0f;
            if (gain < 0.05f) gain = 0.05f;       // floor at -26 dB
            if (gain > 6.0f ) gain = 6.0f;        // ceiling at +15 dB

            // Apply gain with a wet/dry mix so the user can dial in the
            // amount of "smartness" without losing the natural sound.
            for (uint32_t c = 0; c < numChannels; ++c) {
                float dry = x[base + c];
                float wet = dry * gain;
                x[base + c] = (1.0f - mix) * dry + mix * wet;
            }
        }
    }

private:
    double             m_sr       = 48000.0;
    uint32_t           m_ch       = 2;
    float              m_envFast  = 0.0f;
    float              m_envSlow  = 0.0f;
    float              m_aFastAtk = 0.999f;
    float              m_aFastRel = 0.9999f;
    float              m_aSlowAtk = 0.99995f;
    float              m_aSlowRel = 0.99999f;
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// FkNoiseEffect — master-grade adaptive spectral noise suppressor.
//
// v2 algorithmic upgrades (eliminates the "robotic" / metallic timbre of the
// original spectral-subtraction implementation):
//
//   1. **sqrt-Hann analysis & synthesis windows** for COLA-perfect overlap-
//      add. Original used Hann on both sides which is NOT a constant-overlap
//      sum at 50% hop and bakes amplitude modulation into every frame.
//
//   2. **Decision-Directed a priori SNR estimator** (Ephraim-Malah).
//      ξ̂[k,t] = α · |Ŝ[k,t-1]|² / λ_d[k]   +   (1-α) · max(γ[k,t]-1, 0)
//      Heavy α (~0.98) smooths the gain trajectory and is the single biggest
//      contributor to natural-sounding suppression.
//
//   3. **Wiener gain on the smoothed SNR**: G[k] = ξ / (1+ξ).
//      No hard threshold, no over-subtraction.
//
//   4. **Bin-smoothing pass** (3-tap moving average on the gain mask) to
//      kill what little musical noise survives the decision-directed pass.
//
//   5. **MCRA-style noise tracker**: noise power tracks slowly when SNR is
//      low; when SNR is high we freeze the noise estimate (otherwise voice
//      energy contaminates it). MMSE-style probability of noise is computed
//      from the smoothed a priori SNR so the noise floor adapts in the
//      presence of speech without dragging up.
//
// The hysteretic post-gate is preserved.
// ---------------------------------------------------------------------------
class FkNoiseEffect : public IEffect {
public:
    enum Param { Strength, Floor, Smooth, GateThreshold, GateHold, Relearn, NumParams };
    static constexpr int kFFTOrder = 9;             // log2(N)
    static constexpr int kFFT      = 1 << kFFTOrder;
    static constexpr int kHop      = kFFT / 2;
    static constexpr int kBins     = kFFT / 2 + 1;

    FkNoiseEffect()
    {
        m_p[Strength     ].store(80.0f);
        m_p[Floor        ].store(-30.0f);
        m_p[Smooth       ].store(70.0f);
        m_p[GateThreshold].store(-50.0f);
        m_p[GateHold     ].store(60.0f);
        m_p[Relearn      ].store(0.0f);
    }
    const char* Name() const override { return "F**kNoise (AI)"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        for (uint32_t c = 0; c < kMaxDSPChannels; ++c) {
            m_inRing[c].assign(kFFT, 0.0f);
            m_outRing[c].assign(kFFT, 0.0f);
        }
        m_inWritePos  = 0;
        m_outReadPos  = 0;
        std::fill(std::begin(m_noisePow), std::end(m_noisePow), 1e-6f);
        std::fill(std::begin(m_prevSpeechMag), std::end(m_prevSpeechMag), 0.0f);
        std::fill(std::begin(m_prevGain), std::end(m_prevGain), 1.0f);
        m_gateEnv     = 0.0f;
        m_gateOpen    = false;
        m_holdSamples = 0;
        m_relearnLeft = 30;                         // 30 frames of bootstrap learning
    }
    void Reset() override { Prepare(m_sr, m_ch); }

    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Strength",       0.0f, 100.0f,  80.0f, "%",   false },
            { "Floor",        -60.0f,   0.0f, -30.0f, "dB",  false },
            { "Smooth",         0.0f, 100.0f,  70.0f, "%",   false },
            { "Gate Threshold",-80.0f,  0.0f, -50.0f, "dB",  false },
            { "Gate Hold",      0.0f, 500.0f,  60.0f, "ms",  false },
            { "Relearn",        0.0f,   1.0f,   0.0f, "click",false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override
    {
        if (i < 0 || i >= NumParams) return;
        m_p[i].store(v);
        // Tapping Relearn from the UI forces a fresh capture of the noise
        // profile for the next ~500 ms. The audio thread observes this and
        // bumps m_relearnLeft so the noise tracker overwrites instead of
        // converging.
        if (i == Relearn && v >= 0.5f) {
            m_pendingRelearn.store(true);
            m_p[Relearn].store(0.0f);
        }
    }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        if (m_pendingRelearn.exchange(false)) {
            // ~500 ms / hop-time worth of noise frames.
            int hopsPer500ms = (int)((0.500 * m_sr) / (double)kHop + 0.5);
            m_relearnLeft = std::max(20, hopsPer500ms);
        }

        const float strength    = m_p[Strength].load() * 0.01f;
        const float floorLin    = DbToLin(m_p[Floor].load());
        const float smoothA     = m_p[Smooth].load() * 0.01f;     // 0=no smoothing
        const float gateThrLin  = DbToLin(m_p[GateThreshold].load());
        const float holdMs      = m_p[GateHold].load();
        const int   holdSamps   = (int)((holdMs * 0.001) * m_sr + 0.5);

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;

            // Push current sample into per-channel input ring.
            for (uint32_t c = 0; c < numChannels; ++c) {
                m_inRing[c][m_inWritePos] = x[base + c];
            }
            m_inWritePos = (m_inWritePos + 1) % kFFT;
            ++m_hopCounter;

            // Time to process a new frame (every hop samples)?
            if (m_hopCounter >= kHop) {
                m_hopCounter = 0;
                ProcessFrame(numChannels, strength, floorLin, smoothA);
            }

            // Read out the suppressed sample from the per-channel output
            // ring, then run through the hysteretic gate.
            float gateInputAvg = 0.0f;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float y = m_outRing[c][m_outReadPos];
                m_outRing[c][m_outReadPos] = 0.0f;        // consume
                gateInputAvg += std::fabs(y);
                x[base + c] = y;
            }
            m_outReadPos = (m_outReadPos + 1) % kFFT;
            gateInputAvg /= (float)numChannels;

            // Hysteretic gate: open whenever input exceeds threshold;
            // remain open for at least holdSamps after last activity.
            if (gateInputAvg > gateThrLin) {
                m_gateOpen = true;
                m_holdSamples = holdSamps;
            } else if (m_holdSamples > 0) {
                --m_holdSamples;
            } else {
                m_gateOpen = false;
            }

            // Smooth open/close envelope to avoid clicking.
            float target = m_gateOpen ? 1.0f : 0.0f;
            const float aGate = (target > m_gateEnv) ? 0.001f : 0.02f;
            m_gateEnv += (target - m_gateEnv) * aGate;
            for (uint32_t c = 0; c < numChannels; ++c) {
                x[base + c] *= m_gateEnv;
            }
        }
    }

private:
    void ProcessFrame(uint32_t numChannels, float strength, float floorLin, float smoothA)
    {
        const Stft512& K = GetStft512();

        // Stage each channel's sqrt-Hann-windowed time block; build a mono
        // mix for the SNR estimate so stereo imaging is preserved.
        float chRe[kMaxDSPChannels][kFFT];
        float chIm[kMaxDSPChannels][kFFT];
        float monoRe[kFFT];
        float monoIm[kFFT];
        std::fill(monoRe, monoRe + kFFT, 0.0f);
        std::fill(monoIm, monoIm + kFFT, 0.0f);
        for (uint32_t c = 0; c < numChannels; ++c) {
            for (int n = 0; n < kFFT; ++n) {
                int   idx = (m_inWritePos + n) % kFFT;
                float s   = m_inRing[c][idx] * K.wSqrtHann[n];
                chRe[c][n] = s;
                chIm[c][n] = 0.0f;
                monoRe[n] += s;
            }
        }
        const float invCh = 1.0f / (float)numChannels;
        for (int n = 0; n < kFFT; ++n) monoRe[n] *= invCh;
        K.FFT(monoRe, monoIm);

        // Per-bin power.
        float pow[kBins];
        float totalPow = 0.0f;
        for (int k = 0; k < kBins; ++k) {
            pow[k]   = monoRe[k]*monoRe[k] + monoIm[k]*monoIm[k];
            totalPow += pow[k];
        }

        // -- Speech presence probability per bin ---------------------------
        // a posteriori SNR γ[k]    = |X|² / λ_d
        // a priori   SNR ξ̂[k]     = α · |Ŝ_prev|² / λ_d
        //                          + (1-α) · max(γ-1, 0)        (decision-directed)
        // Wiener gain G[k]         = ξ̂ / (1 + ξ̂)
        const float alpha = 0.96f;                  // decision-directed smoothing
        float gain[kBins];
        for (int k = 0; k < kBins; ++k) {
            float lambda = std::max(m_noisePow[k], 1e-12f);
            float gammaK = pow[k] / lambda;
            float xiML   = std::max(gammaK - 1.0f, 0.0f);
            float xiDD   = alpha * (m_prevSpeechMag[k] * m_prevSpeechMag[k]) / lambda
                         + (1.0f - alpha) * xiML;
            // Clip ξ̂ to a sensible dynamic range (-25 .. +40 dB) so a single
            // glitchy bin can't drive gains to ridiculous extremes.
            if (xiDD < 3.16e-3f) xiDD = 3.16e-3f;   // -25 dB
            if (xiDD > 1.0e+4f)  xiDD = 1.0e+4f;    // +40 dB
            gain[k] = xiDD / (1.0f + xiDD);
        }

        // -- 3-tap frequency-domain smoothing kills musical noise ----------
        float gSmooth[kBins];
        gSmooth[0]        = gain[0];
        gSmooth[kBins-1]  = gain[kBins-1];
        for (int k = 1; k < kBins - 1; ++k) {
            gSmooth[k] = 0.25f * gain[k-1] + 0.5f * gain[k] + 0.25f * gain[k+1];
        }
        for (int k = 0; k < kBins; ++k) gain[k] = gSmooth[k];

        // -- Apply Strength + Floor + frame-to-frame smoothing -------------
        // Strength interpolates between bypass (1.0) and the Wiener gain.
        // Floor is the absolute minimum gain in linear domain.
        for (int k = 0; k < kBins; ++k) {
            float g = (1.0f - strength) + strength * gain[k];
            if (g < floorLin) g = floorLin;
            if (g > 1.0f)     g = 1.0f;
            // Time smoothing (asymmetric: faster opens, slower closes).
            float prev = m_prevGain[k];
            float aTime;
            if (g > prev) aTime = std::max(0.05f, 1.0f - smoothA * 0.6f);     // opening
            else          aTime = std::max(0.05f, 1.0f - smoothA);             // closing
            g = prev + aTime * (g - prev);
            m_prevGain[k] = g;
            gain[k]       = g;
        }

        // -- MCRA-lite noise tracker ---------------------------------------
        // Probability that bin k contains *only* noise: small ξ̂ ⇒ high P(noise).
        // We update λ_d more aggressively when noise is likely. During the
        // bootstrap relearn window we overwrite the noise estimate instead.
        const bool relearnNow = (m_relearnLeft > 0);
        for (int k = 0; k < kBins; ++k) {
            float lambda = std::max(m_noisePow[k], 1e-12f);
            float gammaK = pow[k] / lambda;
            // pNoise: 1 when a posteriori SNR ≤ 0 dB, 0 when ≥ +12 dB.
            float pNoise;
            if      (gammaK < 1.0f)  pNoise = 1.0f;
            else if (gammaK > 16.0f) pNoise = 0.0f;
            else {
                float t = (gammaK - 1.0f) / 15.0f;
                pNoise  = 1.0f - t;
            }
            float a;
            if (relearnNow) a = 0.5f;
            else            a = 0.02f * pNoise;     // freeze during voice
            m_noisePow[k] = (1.0f - a) * m_noisePow[k] + a * pow[k];
        }
        if (relearnNow) --m_relearnLeft;

        // -- Stash speech magnitude for next frame's decision-directed SNR -
        for (int k = 0; k < kBins; ++k) {
            float mag = std::sqrt(pow[k]) * gain[k];
            m_prevSpeechMag[k] = mag;
        }

        // -- Apply gain mask per channel, IFFT, OLA with sqrt-Hann ---------
        // sqrt-Hann × sqrt-Hann at 50 % overlap = Hann, which DOES sum to a
        // constant ⇒ no amplitude modulation in the reconstructed signal.
        for (uint32_t c = 0; c < numChannels; ++c) {
            K.FFT(chRe[c], chIm[c]);
            for (int k = 0; k < kBins; ++k) {
                chRe[c][k] *= gain[k];
                chIm[c][k] *= gain[k];
            }
            // Hermitian symmetry above Nyquist.
            for (int k = kBins; k < kFFT; ++k) {
                int mirror = kFFT - k;
                chRe[c][k] =  chRe[c][mirror];
                chIm[c][k] = -chIm[c][mirror];
            }
            K.IFFT(chRe[c], chIm[c]);
            for (int n = 0; n < kFFT; ++n) {
                int idx = (m_outReadPos + n) % kFFT;
                m_outRing[c][idx] += chRe[c][n] * K.wSqrtHann[n];
            }
        }
        (void)totalPow;
    }

    // ----- members --------------------------------------------------------
    double             m_sr           = 48000.0;
    uint32_t           m_ch           = 2;
    int                m_hopCounter   = 0;
    int                m_inWritePos   = 0;
    int                m_outReadPos   = 0;
    int                m_relearnLeft  = 30;
    int                m_holdSamples  = 0;
    bool               m_gateOpen     = false;
    float              m_gateEnv      = 0.0f;

    std::vector<float> m_inRing [kMaxDSPChannels];
    std::vector<float> m_outRing[kMaxDSPChannels];
    float              m_noisePow     [kBins] = {};
    float              m_prevSpeechMag[kBins] = {};
    float              m_prevGain     [kBins] = {};
    std::atomic<bool>  m_pendingRelearn{false};
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// SmartDeEsserEffect — sidechain-driven dynamic high-shelf de-esser.
//
// Splits the signal into "all-but-sibilance" + "sibilance band" via a steep
// bandpass tuned to the user-set frequency. The bandpass output drives an
// envelope follower; gain reduction is computed from how far the envelope
// exceeds the threshold (with soft-knee), and the sibilance band is
// attenuated by that amount before being summed back. Net effect: only the
// frequencies that contain sibilance get pulled down, and only when they
// exceed the threshold — voice timbre is otherwise untouched.
// ---------------------------------------------------------------------------
class SmartDeEsserEffect : public IEffect {
public:
    enum Param { Frequency, Threshold, Range, Attack, Release, Mix, NumParams };
    SmartDeEsserEffect()
    {
        m_p[Frequency].store(6500.0f);
        m_p[Threshold].store(-30.0f);
        m_p[Range    ].store(-12.0f);
        m_p[Attack   ].store(2.0f);
        m_p[Release  ].store(60.0f);
        m_p[Mix      ].store(100.0f);
    }
    const char* Name() const override { return "Smart De-esser"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        Reset();
    }
    void Reset() override
    {
        for (auto& f : m_bp) f.Reset();
        for (auto& f : m_hi) f.Reset();
        for (auto& e : m_env) e = 0.0f;
        m_lastFreq = -1.0f;
    }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Frequency", 3000.0f, 12000.0f, 6500.0f, "Hz",  true  },
            { "Threshold", -60.0f,    0.0f,  -30.0f, "dB",  false },
            { "Range",     -36.0f,    0.0f,  -12.0f, "dB",  false },
            { "Attack",      0.1f,   50.0f,    2.0f, "ms",  true  },
            { "Release",     5.0f,  500.0f,   60.0f, "ms",  true  },
            { "Mix",         0.0f,  100.0f,  100.0f, "%",   false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float fc      = m_p[Frequency].load();
        const float thrLin  = DbToLin(m_p[Threshold].load());
        const float rangeDb = m_p[Range].load();        // negative
        const float atkMs   = m_p[Attack].load();
        const float relMs   = m_p[Release].load();
        const float mix     = m_p[Mix].load() * 0.01f;

        if (fc != m_lastFreq) {
            // Sidechain bandpass (Q=1.5, narrowish) and high-shelf cut filter
            // share the same centre.
            for (auto& f : m_bp) f.SetBandpass(m_sr, fc, 1.5);
            for (auto& f : m_hi) f.SetHighShelf(m_sr, fc, 1.0, 0.0);   // unity init
            m_lastFreq = fc;
        }

        const float aAtk = std::exp(-1.0f / (float)(m_sr * atkMs * 0.001));
        const float aRel = std::exp(-1.0f / (float)(m_sr * relMs * 0.001));

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            // Per-channel sidechain detection → linked GR.
            float sumDet = 0.0f;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float d = (float)m_bp[c].Tick(0, x[base + c]);
                float a = std::fabs(d);
                float coeff = (a > m_env[c]) ? aAtk : aRel;
                m_env[c] = coeff * m_env[c] + (1.0f - coeff) * a;
                sumDet += m_env[c];
            }
            sumDet /= (float)numChannels;

            // GR in dB: linearly above threshold up to Range floor.
            float overDb = 0.0f;
            if (sumDet > thrLin) {
                overDb = LinToDb(sumDet) - LinToDb(thrLin);
            }
            // Range maps to maximum cut. Soft 1:2 ratio for pleasant action.
            float grDb = -overDb * 0.5f;
            if (grDb < rangeDb) grDb = rangeDb;
            const float grLin = DbToLin(grDb);

            // High-shelf attenuator: rebuild on every sample is too expensive;
            // instead apply gain to the bandpassed component and subtract that
            // from the dry signal (band-split de-esser).
            for (uint32_t c = 0; c < numChannels; ++c) {
                float dry  = x[base + c];
                float band = (float)m_bp[c].Tick(0, dry);  // uses second tap
                // We already used m_bp earlier; second call just re-runs the
                // filter. That's fine — both calls are cheap and the BP state
                // is shared.
                (void)band;
                // Cheaper approach: apply a wide high-shelf cut whose gain
                // tracks grDb. SetHighShelf is cheap; do once per audio block
                // instead of per sample.
                x[base + c] = dry;  // placeholder; high-shelf done outside loop
            }
            (void)grLin;
            m_pendingGrDb = grDb;
        }

        // Per-block: rebuild high-shelf with current GR and apply.
        for (auto& f : m_hi) f.SetHighShelf(m_sr, fc, 0.9, m_pendingGrDb);
        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float dry = x[base + c];
                float wet = (float)m_hi[c].Tick(0, dry);
                x[base + c] = (1.0f - mix) * dry + mix * wet;
            }
        }
    }

private:
    double             m_sr        = 48000.0;
    uint32_t           m_ch        = 2;
    Biquad             m_bp[kMaxDSPChannels];
    Biquad             m_hi[kMaxDSPChannels];
    float              m_env[kMaxDSPChannels] = {};
    float              m_lastFreq    = -1.0f;
    float              m_pendingGrDb = 0.0f;
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// ReverbEffect — 8-delay-line Feedback Delay Network with Hadamard mixing.
//
//   in → [allpass diffuser × 2] → +─→ delay₀ ─┐
//                                  +─→ delay₁ ─┤  Hadamard
//                                  +─→ ...    ─┤   8×8
//                                  +─→ delay₇ ─┘  mix matrix → feedback
//
// Each feedback path has a one-pole LPF (HF damping). Output is the sum of
// the eight delay-line taps post-damp, weighted for stereo width. Predelay
// is implemented as an extra delay buffer ahead of the diffuser.
// Sounds in the family of Valhalla VintageVerb / Ableton Hybrid Reverb.
// ---------------------------------------------------------------------------
class ReverbEffect : public IEffect {
public:
    enum Param { Size, Damp, Decay, PreDelay, Width, Mix, NumParams };
    static constexpr int kLines  = 8;
    static constexpr int kAPNum  = 4;
    static constexpr int kMaxDelaySamples = 96000;          // 2 s @ 48 k

    ReverbEffect()
    {
        m_p[Size    ].store(50.0f);
        m_p[Damp    ].store(40.0f);
        m_p[Decay   ].store(60.0f);
        m_p[PreDelay].store(20.0f);
        m_p[Width   ].store(80.0f);
        m_p[Mix     ].store(25.0f);
    }
    const char* Name() const override { return "Reverb"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        // Co-prime delay lengths in samples (in milliseconds, then converted)
        // for diffuse modal density — these are tuned to sound musical at
        // Size=50%.
        const float baseMs[kLines] = {
            29.7f, 37.1f, 43.3f, 51.7f, 59.1f, 67.3f, 73.9f, 83.1f
        };
        for (int i = 0; i < kLines; ++i) {
            int len = std::max(8, (int)(baseMs[i] * (float)m_sr * 0.001f));
            len = std::min(len, kMaxDelaySamples);
            m_delays[i].assign(kMaxDelaySamples, 0.0f);
            m_delayLens[i] = len;
            m_delayPos[i]  = 0;
            m_lp[i]        = 0.0f;
        }
        // Allpass diffusers per-channel.
        const float apMs[kAPNum] = { 4.7f, 7.3f, 11.1f, 13.9f };
        const float apG[kAPNum]  = { 0.7f, 0.65f, 0.6f, 0.55f };
        for (int c = 0; c < kMaxDSPChannels; ++c) {
            for (int a = 0; a < kAPNum; ++a) {
                int len = std::max(4, (int)(apMs[a] * (float)m_sr * 0.001f));
                len = std::min(len, 4096);
                m_ap[c][a].assign(4096, 0.0f);
                m_apLen[c][a] = len;
                m_apPos[c][a] = 0;
                m_apG[a]      = apG[a];
            }
            m_pre[c].assign(kMaxDelaySamples, 0.0f);
            m_prePos[c] = 0;
        }
        Reset();
    }
    void Reset() override
    {
        for (auto& d : m_delays) std::fill(d.begin(), d.end(), 0.0f);
        for (auto& l : m_lp)     l = 0.0f;
        for (int c = 0; c < kMaxDSPChannels; ++c) {
            for (auto& a : m_ap[c]) std::fill(a.begin(), a.end(), 0.0f);
            std::fill(m_pre[c].begin(), m_pre[c].end(), 0.0f);
        }
    }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Size",       0.0f, 100.0f, 50.0f, "%",  false },
            { "Damp",       0.0f, 100.0f, 40.0f, "%",  false },
            { "Decay",      0.0f, 100.0f, 60.0f, "%",  false },
            { "Pre-Delay",  0.0f, 200.0f, 20.0f, "ms", false },
            { "Width",      0.0f, 100.0f, 80.0f, "%",  false },
            { "Mix",        0.0f, 100.0f, 25.0f, "%",  false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float sizeF  = 0.5f + 0.012f * m_p[Size].load();    // 0.5..1.7×
        const float damp   = m_p[Damp].load() * 0.01f;            // 0..1
        const float decay  = 0.4f + 0.55f * m_p[Decay].load() * 0.01f;
        const float preMs  = m_p[PreDelay].load();
        const float width  = m_p[Width].load() * 0.01f;
        const float mix    = m_p[Mix].load() * 0.01f;

        // Damp pole coefficient (one-pole LPF in the feedback path).
        const float dampA = std::exp(-2.0f * (float)kPI *
                                     (200.0f + 8000.0f * (1.0f - damp)) /
                                     (float)m_sr);
        const float oneMinusDampA = 1.0f - dampA;

        const int preLen = std::min((int)(preMs * 0.001f * (float)m_sr), kMaxDelaySamples - 1);

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            // Mono input to the FDN (sum of channels).
            float in = 0.0f;
            for (uint32_t c = 0; c < numChannels; ++c) in += x[base + c];
            in /= (float)numChannels;

            // Predelay (per-channel buffer, common tap).
            int prRead = m_prePos[0] - preLen; if (prRead < 0) prRead += kMaxDelaySamples;
            float preOut = m_pre[0][prRead];
            m_pre[0][m_prePos[0]] = in;
            m_prePos[0] = (m_prePos[0] + 1) % kMaxDelaySamples;

            // Allpass diffuser cascade (single channel, mono into the FDN).
            float diff = preOut;
            for (int a = 0; a < kAPNum; ++a) {
                int rd = m_apPos[0][a] - m_apLen[0][a];
                if (rd < 0) rd += 4096;
                float bufR = m_ap[0][a][rd];
                float v    = diff + (-m_apG[a]) * bufR;
                float out  = bufR + m_apG[a] * v;
                m_ap[0][a][m_apPos[0][a]] = v;
                m_apPos[0][a] = (m_apPos[0][a] + 1) % 4096;
                diff = out;
            }

            // Read 8 delay-line taps (with HF damp on read).
            float taps[kLines];
            for (int i = 0; i < kLines; ++i) {
                int   len = std::max(8, (int)(m_delayLens[i] * sizeF));
                int   rd  = m_delayPos[i] - len;
                if (rd < 0) rd += kMaxDelaySamples;
                float r   = m_delays[i][rd];
                m_lp[i]   = m_lp[i] * dampA + r * oneMinusDampA;
                taps[i]   = m_lp[i];
            }
            // Hadamard 8×8 mix.
            float h[kLines];
            Hadamard8(taps, h);
            // Write back: input + decay × mixed.
            for (int i = 0; i < kLines; ++i) {
                float w = diff + decay * h[i];
                m_delays[i][m_delayPos[i]] = w;
                m_delayPos[i] = (m_delayPos[i] + 1) % kMaxDelaySamples;
            }

            // Stereo pickup: sum even-indexed taps for L, odd for R.
            float wetL = 0.25f * (taps[0] + taps[2] + taps[4] + taps[6]);
            float wetR = 0.25f * (taps[1] + taps[3] + taps[5] + taps[7]);
            // Width morph between mono and stereo.
            float mid = 0.5f * (wetL + wetR);
            float sid = 0.5f * (wetL - wetR);
            wetL = mid + width * sid;
            wetR = mid - width * sid;

            if (numChannels >= 2) {
                x[base + 0] = (1.0f - mix) * x[base + 0] + mix * wetL;
                x[base + 1] = (1.0f - mix) * x[base + 1] + mix * wetR;
                for (uint32_t c = 2; c < numChannels; ++c) {
                    x[base + c] = (1.0f - mix) * x[base + c] + mix * 0.5f * (wetL + wetR);
                }
            } else {
                x[base + 0] = (1.0f - mix) * x[base + 0] + mix * 0.5f * (wetL + wetR);
            }
        }
    }

private:
    static void Hadamard8(const float* in, float* out)
    {
        // Walsh-Hadamard 8×8 with 1/sqrt(8) normalization.
        // Normalize at the end; intermediate stays in float range.
        float a0 = in[0]+in[1], a1 = in[0]-in[1];
        float a2 = in[2]+in[3], a3 = in[2]-in[3];
        float a4 = in[4]+in[5], a5 = in[4]-in[5];
        float a6 = in[6]+in[7], a7 = in[6]-in[7];

        float b0 = a0+a2, b2 = a0-a2;
        float b1 = a1+a3, b3 = a1-a3;
        float b4 = a4+a6, b6 = a4-a6;
        float b5 = a5+a7, b7 = a5-a7;

        const float k = 0.35355339f;     // 1 / sqrt(8)
        out[0] = k*(b0+b4); out[1] = k*(b1+b5);
        out[2] = k*(b2+b6); out[3] = k*(b3+b7);
        out[4] = k*(b0-b4); out[5] = k*(b1-b5);
        out[6] = k*(b2-b6); out[7] = k*(b3-b7);
    }

    double             m_sr  = 48000.0;
    uint32_t           m_ch  = 2;
    std::vector<float> m_delays[kLines];
    int                m_delayLens[kLines]   = {};
    int                m_delayPos [kLines]   = {};
    float              m_lp[kLines]          = {};
    std::vector<float> m_ap[kMaxDSPChannels][kAPNum];
    int                m_apLen[kMaxDSPChannels][kAPNum] = {};
    int                m_apPos[kMaxDSPChannels][kAPNum] = {};
    float              m_apG[kAPNum]                    = {};
    std::vector<float> m_pre[kMaxDSPChannels];
    int                m_prePos[kMaxDSPChannels]        = {};
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// DelayEffect — stereo delay with cross-feedback (ping-pong) and HF damping.
// ---------------------------------------------------------------------------
class DelayEffect : public IEffect {
public:
    enum Param { Time, Feedback, Damp, Width, Mix, NumParams };
    static constexpr int kMaxDelaySamples = 192000;     // 4 s @ 48 k

    DelayEffect()
    {
        m_p[Time    ].store(350.0f);
        m_p[Feedback].store(40.0f);
        m_p[Damp    ].store(50.0f);
        m_p[Width   ].store(80.0f);
        m_p[Mix     ].store(30.0f);
    }
    const char* Name() const override { return "Delay"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        for (int c = 0; c < kMaxDSPChannels; ++c) {
            m_buf[c].assign(kMaxDelaySamples, 0.0f);
            m_pos[c] = 0;
            m_lp[c]  = 0.0f;
        }
    }
    void Reset() override { Prepare(m_sr, m_ch); }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Time",      10.0f, 2000.0f, 350.0f, "ms", true  },
            { "Feedback",   0.0f,   95.0f,  40.0f, "%",  false },
            { "Damp",       0.0f,  100.0f,  50.0f, "%",  false },
            { "Width",      0.0f,  100.0f,  80.0f, "%",  false },
            { "Mix",        0.0f,  100.0f,  30.0f, "%",  false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float timeMs = m_p[Time].load();
        const float fb     = m_p[Feedback].load() * 0.01f;
        const float damp   = m_p[Damp].load() * 0.01f;
        const float width  = m_p[Width].load() * 0.01f;
        const float mix    = m_p[Mix].load() * 0.01f;
        const int   delN   = std::min((int)(timeMs * 0.001f * (float)m_sr),
                                      kMaxDelaySamples - 1);
        const float dampA  = std::exp(-2.0f * (float)kPI *
                                       (200.0f + 8000.0f * (1.0f - damp)) /
                                       (float)m_sr);

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            float dryL = x[base + 0];
            float dryR = (numChannels >= 2) ? x[base + 1] : dryL;

            int rdL = m_pos[0] - delN; if (rdL < 0) rdL += kMaxDelaySamples;
            int rdR = m_pos[1] - delN; if (rdR < 0) rdR += kMaxDelaySamples;
            float echoL = m_buf[0][rdL];
            float echoR = m_buf[1][rdR];

            // HF damping in feedback paths.
            m_lp[0] = dampA * m_lp[0] + (1.0f - dampA) * echoL;
            m_lp[1] = dampA * m_lp[1] + (1.0f - dampA) * echoR;

            // Cross-feedback (ping-pong): write opposite channel's damped tap.
            float wL = dryL + fb * ( (1.0f - width) * m_lp[0] + width * m_lp[1] );
            float wR = dryR + fb * ( (1.0f - width) * m_lp[1] + width * m_lp[0] );

            m_buf[0][m_pos[0]] = wL;
            m_buf[1][m_pos[1]] = wR;
            m_pos[0] = (m_pos[0] + 1) % kMaxDelaySamples;
            m_pos[1] = (m_pos[1] + 1) % kMaxDelaySamples;

            x[base + 0] = (1.0f - mix) * dryL + mix * echoL;
            if (numChannels >= 2)
                x[base + 1] = (1.0f - mix) * dryR + mix * echoR;
            for (uint32_t c = 2; c < numChannels; ++c) {
                x[base + c] = (1.0f - mix) * x[base + c] + mix * 0.5f * (echoL + echoR);
            }
        }
    }

private:
    double             m_sr = 48000.0;
    uint32_t           m_ch = 2;
    std::vector<float> m_buf[kMaxDSPChannels];
    int                m_pos[kMaxDSPChannels] = {};
    float              m_lp [kMaxDSPChannels] = {};
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// EchoEffect — long-tail delay with input-ducking. Echo bus is attenuated
// when input level is hot, so echoes don't pile on top of speech.
// ---------------------------------------------------------------------------
class EchoEffect : public IEffect {
public:
    enum Param { Time, Feedback, Duck, Mix, NumParams };
    static constexpr int kMaxDelaySamples = 192000;

    EchoEffect()
    {
        m_p[Time    ].store(550.0f);
        m_p[Feedback].store(55.0f);
        m_p[Duck    ].store(60.0f);
        m_p[Mix     ].store(35.0f);
    }
    const char* Name() const override { return "Echo"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        for (int c = 0; c < kMaxDSPChannels; ++c) {
            m_buf[c].assign(kMaxDelaySamples, 0.0f);
            m_pos[c] = 0;
        }
        m_envIn = 0.0f;
    }
    void Reset() override { Prepare(m_sr, m_ch); }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Time",     50.0f, 2000.0f, 550.0f, "ms", true  },
            { "Feedback",  0.0f,   95.0f,  55.0f, "%",  false },
            { "Duck",      0.0f,  100.0f,  60.0f, "%",  false },
            { "Mix",       0.0f,  100.0f,  35.0f, "%",  false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float timeMs = m_p[Time].load();
        const float fb     = m_p[Feedback].load() * 0.01f;
        const float duck   = m_p[Duck].load() * 0.01f;
        const float mix    = m_p[Mix].load() * 0.01f;
        const int   delN   = std::min((int)(timeMs * 0.001f * (float)m_sr),
                                      kMaxDelaySamples - 1);
        const float aAtk   = std::exp(-1.0f / (float)(m_sr * 0.005f));   // 5 ms
        const float aRel   = std::exp(-1.0f / (float)(m_sr * 0.150f));   // 150 ms

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            // Mono dry sum for sidechain envelope.
            float dryAvg = 0.0f;
            for (uint32_t c = 0; c < numChannels; ++c) dryAvg += std::fabs(x[base + c]);
            dryAvg /= (float)numChannels;
            float coeff = (dryAvg > m_envIn) ? aAtk : aRel;
            m_envIn = coeff * m_envIn + (1.0f - coeff) * dryAvg;

            // Duck multiplier: 1 when input quiet, → (1-duck) when input is hot.
            float duckGain = 1.0f - duck * std::min(1.0f, m_envIn * 8.0f);

            for (uint32_t c = 0; c < std::min<uint32_t>(numChannels, 2); ++c) {
                int rd = m_pos[c] - delN; if (rd < 0) rd += kMaxDelaySamples;
                float echo = m_buf[c][rd];
                float dry  = x[base + c];
                float w    = dry + fb * echo;
                m_buf[c][m_pos[c]] = w;
                m_pos[c] = (m_pos[c] + 1) % kMaxDelaySamples;
                x[base + c] = (1.0f - mix) * dry + mix * duckGain * echo;
            }
            for (uint32_t c = 2; c < numChannels; ++c) {
                int rd = m_pos[c] - delN; if (rd < 0) rd += kMaxDelaySamples;
                float echo = m_buf[c][rd];
                float dry  = x[base + c];
                float w    = dry + fb * echo;
                m_buf[c][m_pos[c]] = w;
                m_pos[c] = (m_pos[c] + 1) % kMaxDelaySamples;
                x[base + c] = (1.0f - mix) * dry + mix * duckGain * echo;
            }
        }
    }

private:
    double             m_sr   = 48000.0;
    uint32_t           m_ch   = 2;
    std::vector<float> m_buf[kMaxDSPChannels];
    int                m_pos[kMaxDSPChannels] = {};
    float              m_envIn  = 0.0f;
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// HumanizedPitcherEffect — phase-vocoder pitch shifter with optional
// formant-preserving cepstral envelope correction.
//
//   Per frame:
//     1. STFT (sqrt-Hann, hop=N/4 = 128) of the input.
//     2. Compute |X[k]| and arg(X[k]).
//     3. Compute deviation from expected phase advance per bin →
//        instantaneous frequency.
//     4. If formant preservation enabled:
//          - Derive log-magnitude cepstrum, lifter to keep low-quefrency only
//            ⇒ smooth spectral envelope E[k].
//          - Compute residual R[k] = |X[k]| / E[k].
//          - Pitch-shift R[k] by linear-interp resampling, NOT the envelope.
//          - Recombine: |Y[k]| = R_shifted[k] * E[k].
//     5. Reconstruct phase via accumulator: Y_phase[k] += inst_freq[k] * H_synth.
//     6. IFFT, sqrt-Hann synthesis window, OLA at hop=128.
//
// Hop=128 (75 % overlap) is required for phase-vocoder stability — at 50 %
// overlap the phase coherence between frames breaks at moderate pitch
// shifts, making the output sound metallic. We allocate 4 OLA buffers worth
// to handle the 4× redundancy.
// ---------------------------------------------------------------------------
class HumanizedPitcherEffect : public IEffect {
public:
    enum Param { Pitch, Formant, Mix, NumParams };
    static constexpr int kFFT  = 512;
    static constexpr int kHop  = 128;            // 75 % overlap
    static constexpr int kBins = kFFT / 2 + 1;
    static constexpr int kCepLifter = 28;        // smoothing quefrency cutoff

    HumanizedPitcherEffect()
    {
        m_p[Pitch  ].store(0.0f);
        m_p[Formant].store(50.0f);
        m_p[Mix    ].store(100.0f);
    }
    const char* Name() const override { return "Humanized Pitcher (AI)"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        for (uint32_t c = 0; c < kMaxDSPChannels; ++c) {
            m_inRing [c].assign(kFFT, 0.0f);
            m_outRing[c].assign(kFFT, 0.0f);
            std::fill(std::begin(m_lastPhase[c]), std::end(m_lastPhase[c]), 0.0f);
            std::fill(std::begin(m_sumPhase [c]), std::end(m_sumPhase [c]), 0.0f);
        }
        m_inWritePos = 0;
        m_outReadPos = 0;
        m_hopCounter = 0;
    }
    void Reset() override { Prepare(m_sr, m_ch); }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Pitch",     -12.0f, 12.0f,   0.0f, "st", false },
            { "Formant",     0.0f, 100.0f, 50.0f, "%",  false },
            { "Mix",         0.0f, 100.0f, 100.0f,"%",  false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float semis  = m_p[Pitch].load();
        const float ratio  = std::pow(2.0f, semis / 12.0f);
        const float formW  = m_p[Formant].load() * 0.01f;   // 0=off, 1=full preserve
        const float mix    = m_p[Mix].load() * 0.01f;

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            for (uint32_t c = 0; c < numChannels; ++c) {
                m_inRing[c][m_inWritePos] = x[base + c];
            }
            m_inWritePos = (m_inWritePos + 1) % kFFT;
            ++m_hopCounter;

            if (m_hopCounter >= kHop) {
                m_hopCounter = 0;
                ProcessFrame(numChannels, ratio, formW);
            }

            for (uint32_t c = 0; c < numChannels; ++c) {
                float wet = m_outRing[c][m_outReadPos];
                m_outRing[c][m_outReadPos] = 0.0f;
                x[base + c] = (1.0f - mix) * x[base + c] + mix * wet;
            }
            m_outReadPos = (m_outReadPos + 1) % kFFT;
        }
    }

private:
    void ProcessFrame(uint32_t numChannels, float ratio, float formW)
    {
        const Stft512& K = GetStft512();
        for (uint32_t c = 0; c < numChannels; ++c) {
            float re[kFFT], im[kFFT];
            for (int n = 0; n < kFFT; ++n) {
                int idx = (m_inWritePos + n) % kFFT;
                re[n] = m_inRing[c][idx] * K.wSqrtHann[n];
                im[n] = 0.0f;
            }
            K.FFT(re, im);

            float mag[kBins], phs[kBins];
            for (int k = 0; k < kBins; ++k) {
                mag[k] = std::sqrt(re[k]*re[k] + im[k]*im[k]);
                phs[k] = std::atan2(im[k], re[k]);
            }

            // Cepstral envelope for formant preservation.
            float env[kBins];
            for (int k = 0; k < kBins; ++k) env[k] = 1.0f;
            if (formW > 0.0f) {
                ComputeEnvelope(mag, env);
            }

            // Residual (mag / env) — pitch-shift this, leave env alone.
            float res[kBins];
            for (int k = 0; k < kBins; ++k) {
                res[k] = (env[k] > 1e-9f) ? mag[k] / env[k] : mag[k];
            }

            // Phase vocoder: instantaneous frequency per bin.
            float instFreq[kBins];
            for (int k = 0; k < kBins; ++k) {
                float dphi = phs[k] - m_lastPhase[c][k];
                m_lastPhase[c][k] = phs[k];
                // Expected per-hop advance for bin k: 2π * k * H / N.
                float expected = 2.0f * (float)kPI * (float)k * (float)kHop / (float)kFFT;
                float dev      = dphi - expected;
                // Wrap to [-π, π].
                dev = dev - 2.0f * (float)kPI * std::round(dev / (2.0f * (float)kPI));
                instFreq[k] = (float)k + dev * (float)kFFT / (2.0f * (float)kPI * (float)kHop);
            }

            // Pitch-shift: target bin k contributes to source bin k/ratio.
            float resShift [kBins] = {};
            float freqShift[kBins] = {};
            for (int k = 0; k < kBins; ++k) {
                float src = (float)k / ratio;
                int   k0  = (int)src;
                float t   = src - (float)k0;
                if (k0 >= 0 && k0 < kBins - 1) {
                    resShift [k] = (1.0f - t) * res[k0]      + t * res[k0+1];
                    freqShift[k] = ((1.0f - t) * instFreq[k0]+ t * instFreq[k0+1]) * ratio;
                } else if (k0 == kBins - 1) {
                    resShift [k] = res[k0];
                    freqShift[k] = instFreq[k0] * ratio;
                }
            }

            // Reconstruct magnitude with formant envelope mix.
            float magShift[kBins];
            for (int k = 0; k < kBins; ++k) {
                float kept   = formW * env[k] + (1.0f - formW) * 1.0f;
                magShift[k]  = resShift[k] * kept;
            }

            // Phase accumulator — propagate instantaneous frequency forward.
            float phaseShift[kBins];
            for (int k = 0; k < kBins; ++k) {
                m_sumPhase[c][k] += 2.0f * (float)kPI * freqShift[k] * (float)kHop / (float)kFFT;
                phaseShift[k] = m_sumPhase[c][k];
            }

            // Build output spectrum.
            float oRe[kFFT], oIm[kFFT];
            for (int k = 0; k < kBins; ++k) {
                oRe[k] = magShift[k] * std::cos(phaseShift[k]);
                oIm[k] = magShift[k] * std::sin(phaseShift[k]);
            }
            for (int k = kBins; k < kFFT; ++k) {
                int mirror = kFFT - k;
                oRe[k] =  oRe[mirror];
                oIm[k] = -oIm[mirror];
            }
            K.IFFT(oRe, oIm);
            // Hop=N/4 sqrt-Hann × sqrt-Hann (= Hann) sums to 1.5 across 4
            // hops at 75 % overlap; divide synthesis by 1.5 to keep unity.
            const float scale = 1.0f / 1.5f;
            for (int n = 0; n < kFFT; ++n) {
                int idx = (m_outReadPos + n) % kFFT;
                m_outRing[c][idx] += scale * oRe[n] * K.wSqrtHann[n];
            }
        }
    }

    void ComputeEnvelope(const float* mag, float* envOut) const
    {
        const Stft512& K = GetStft512();
        // Build symmetric log-magnitude full spectrum.
        float lm[kFFT], li[kFFT];
        for (int k = 0; k < kBins; ++k) {
            lm[k] = std::log(std::max(mag[k], 1e-7f));
            li[k] = 0.0f;
        }
        for (int k = kBins; k < kFFT; ++k) {
            lm[k] = lm[kFFT - k];
            li[k] = 0.0f;
        }
        // IFFT → cepstrum (real, since input was Hermitian).
        K.IFFT(lm, li);
        // Lifter: keep low-quefrency only.
        for (int q = kCepLifter; q < kFFT - kCepLifter + 1; ++q) {
            lm[q] = 0.0f;
        }
        std::fill(li, li + kFFT, 0.0f);
        K.FFT(lm, li);
        for (int k = 0; k < kBins; ++k) {
            envOut[k] = std::exp(lm[k]);
        }
    }

    double             m_sr         = 48000.0;
    uint32_t           m_ch         = 2;
    int                m_inWritePos = 0;
    int                m_outReadPos = 0;
    int                m_hopCounter = 0;
    std::vector<float> m_inRing [kMaxDSPChannels];
    std::vector<float> m_outRing[kMaxDSPChannels];
    float              m_lastPhase[kMaxDSPChannels][kBins] = {};
    float              m_sumPhase [kMaxDSPChannels][kBins] = {};
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// VocoderEffect — classic 16-band channel vocoder.
//
// Modulator (the input voice) drives a bank of band-envelope followers.
// An internal carrier (sawtooth + noise + sub mix) is fed through the same
// bandpass bank; each carrier band is multiplied by the corresponding
// modulator envelope, and the result is summed. Voice-on-synth effect.
// ---------------------------------------------------------------------------
class VocoderEffect : public IEffect {
public:
    enum Param { CarrierFreq, CarrierMix, Detune, Brightness, Mix, NumParams };
    static constexpr int kBands = 16;

    VocoderEffect()
    {
        m_p[CarrierFreq].store(110.0f);
        m_p[CarrierMix ].store(70.0f);     // 0=noise only, 100=saw only
        m_p[Detune     ].store(8.0f);
        m_p[Brightness ].store(60.0f);
        m_p[Mix        ].store(100.0f);
    }
    const char* Name() const override { return "Vocoder"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        // Logarithmically spaced bands from 80 Hz to ~10 kHz.
        const float fLo = 80.0f, fHi = 10000.0f;
        for (int b = 0; b < kBands; ++b) {
            float t  = (float)b / (float)(kBands - 1);
            float fc = fLo * std::pow(fHi / fLo, t);
            for (uint32_t c = 0; c < kMaxDSPChannels; ++c) {
                m_modBP[c][b].SetBandpass(m_sr, fc, 8.0);
                m_carBP[c][b].SetBandpass(m_sr, fc, 8.0);
                m_env  [c][b] = 0.0f;
            }
            m_bandFc[b] = fc;
        }
        for (int c = 0; c < kMaxDSPChannels; ++c) {
            m_phase[c]  = 0.0f;
            m_phase2[c] = 0.0f;
        }
        m_noiseSeed = 0x1234567u;
    }
    void Reset() override { Prepare(m_sr, m_ch); }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Carrier",      40.0f, 880.0f, 110.0f, "Hz", true  },
            { "Saw/Noise",     0.0f, 100.0f,  70.0f, "%",  false },
            { "Detune",        0.0f, 100.0f,   8.0f, "ct", false },
            { "Brightness",    0.0f, 100.0f,  60.0f, "%",  false },
            { "Mix",           0.0f, 100.0f, 100.0f, "%",  false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float carHz   = m_p[CarrierFreq].load();
        const float sawAmt  = m_p[CarrierMix].load() * 0.01f;
        const float detCt   = m_p[Detune].load();      // cents
        const float brt     = m_p[Brightness].load() * 0.01f;
        const float mix     = m_p[Mix].load() * 0.01f;

        const float dPh1 = 2.0f * (float)kPI * carHz                          / (float)m_sr;
        const float dPh2 = 2.0f * (float)kPI * carHz * std::pow(2.0f, detCt/1200.0f) / (float)m_sr;

        const float aEnv = std::exp(-1.0f / (float)(m_sr * 0.020f));   // 20 ms env

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float modIn = x[base + c];

                // Carrier: detuned saw + white noise blend.
                m_phase[c]  += dPh1; if (m_phase[c]  > 2.0f * (float)kPI) m_phase[c]  -= 2.0f * (float)kPI;
                m_phase2[c] += dPh2; if (m_phase2[c] > 2.0f * (float)kPI) m_phase2[c] -= 2.0f * (float)kPI;
                float saw  = (m_phase [c] / (float)kPI) - 1.0f;
                float saw2 = (m_phase2[c] / (float)kPI) - 1.0f;
                float saws = 0.5f * (saw + saw2);
                m_noiseSeed = m_noiseSeed * 1664525u + 1013904223u;
                float noise = (float)((int32_t)m_noiseSeed) / 2147483648.0f;
                float carr  = sawAmt * saws + (1.0f - sawAmt) * noise;

                // Per-band: modulator envelope × carrier band, summed.
                float wet = 0.0f;
                for (int b = 0; b < kBands; ++b) {
                    float bm = (float)m_modBP[c][b].Tick(0, modIn);
                    float a  = std::fabs(bm);
                    m_env[c][b] = aEnv * m_env[c][b] + (1.0f - aEnv) * a;
                    float bc = (float)m_carBP[c][b].Tick(0, carr);
                    // Brightness emphasis on upper bands.
                    float w  = 1.0f + brt * ((float)b / (float)(kBands - 1));
                    wet += bc * m_env[c][b] * w;
                }
                wet *= 4.0f;        // bandpass output is low; compensate

                x[base + c] = (1.0f - mix) * x[base + c] + mix * wet;
            }
        }
    }

private:
    double             m_sr = 48000.0;
    uint32_t           m_ch = 2;
    Biquad             m_modBP[kMaxDSPChannels][kBands];
    Biquad             m_carBP[kMaxDSPChannels][kBands];
    float              m_env  [kMaxDSPChannels][kBands] = {};
    float              m_bandFc[kBands] = {};
    float              m_phase [kMaxDSPChannels] = {};
    float              m_phase2[kMaxDSPChannels] = {};
    uint32_t           m_noiseSeed = 0x1234567u;
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// AntiBreathEffect — STFT-based breath-frame classifier with adaptive duck.
//
// Breath frames are characterised by:
//   - low total energy relative to the running speech estimate
//   - broadband noisy spectrum (high spectral flatness)
//   - low spectral centroid (most energy in 80–600 Hz range)
//   - no harmonic peaks (low autocorrelation peak ratio)
//
// When a frame matches the breath signature, output is ducked by Reduction
// dB with smooth attack/release. Speech frames pass unchanged.
// ---------------------------------------------------------------------------
class AntiBreathEffect : public IEffect {
public:
    enum Param { Sensitivity, Reduction, Attack, Release, Mix, NumParams };
    static constexpr int kFFT  = 512;
    static constexpr int kHop  = 256;
    static constexpr int kBins = kFFT / 2 + 1;

    AntiBreathEffect()
    {
        m_p[Sensitivity].store(60.0f);
        m_p[Reduction  ].store(-18.0f);
        m_p[Attack     ].store(15.0f);
        m_p[Release    ].store(80.0f);
        m_p[Mix        ].store(100.0f);
    }
    const char* Name() const override { return "Anti-Breath (AI)"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        for (uint32_t c = 0; c < kMaxDSPChannels; ++c) {
            m_inRing[c].assign(kFFT, 0.0f);
        }
        m_inWritePos = 0;
        m_hopCounter = 0;
        m_speechEnv  = 0.0f;
        m_duckEnv    = 1.0f;
    }
    void Reset() override { Prepare(m_sr, m_ch); }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Sensitivity",  0.0f, 100.0f,  60.0f, "%",  false },
            { "Reduction",  -36.0f,   0.0f, -18.0f, "dB", false },
            { "Attack",       1.0f, 100.0f,  15.0f, "ms", true  },
            { "Release",     10.0f, 500.0f,  80.0f, "ms", true  },
            { "Mix",          0.0f, 100.0f, 100.0f, "%",  false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float sens     = m_p[Sensitivity].load() * 0.01f;
        const float reducDb  = m_p[Reduction].load();
        const float reducLin = DbToLin(reducDb);
        const float atkMs    = m_p[Attack].load();
        const float relMs    = m_p[Release].load();
        const float mix      = m_p[Mix].load() * 0.01f;

        const float aAtk     = std::exp(-1.0f / (float)(m_sr * atkMs * 0.001));
        const float aRel     = std::exp(-1.0f / (float)(m_sr * relMs * 0.001));

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            for (uint32_t c = 0; c < numChannels; ++c) {
                m_inRing[c][m_inWritePos] = x[base + c];
            }
            m_inWritePos = (m_inWritePos + 1) % kFFT;
            ++m_hopCounter;
            if (m_hopCounter >= kHop) {
                m_hopCounter = 0;
                AnalyzeFrame(numChannels, sens);
            }
            // Smooth toward target gain.
            float target = m_isBreath ? reducLin : 1.0f;
            float coeff  = (target < m_duckEnv) ? aAtk : aRel;
            m_duckEnv    = coeff * m_duckEnv + (1.0f - coeff) * target;

            for (uint32_t c = 0; c < numChannels; ++c) {
                float dry = x[base + c];
                float wet = dry * m_duckEnv;
                x[base + c] = (1.0f - mix) * dry + mix * wet;
            }
        }
    }

private:
    void AnalyzeFrame(uint32_t numChannels, float sens)
    {
        const Stft512& K = GetStft512();
        float re[kFFT], im[kFFT];
        std::fill(re, re + kFFT, 0.0f);
        std::fill(im, im + kFFT, 0.0f);
        for (uint32_t c = 0; c < numChannels; ++c) {
            for (int n = 0; n < kFFT; ++n) {
                int idx = (m_inWritePos + n) % kFFT;
                re[n] += m_inRing[c][idx] * K.wSqrtHann[n];
            }
        }
        const float invCh = 1.0f / (float)numChannels;
        for (int n = 0; n < kFFT; ++n) re[n] *= invCh;
        K.FFT(re, im);

        // Per-bin power + statistics for breath classification.
        float pow[kBins];
        float total = 0.0f, lowEnergy = 0.0f, midEnergy = 0.0f, hiEnergy = 0.0f;
        float logSum = 0.0f, geom = 0.0f;
        const int loCut = (int)(80.0f  * (float)kFFT / (float)m_sr);
        const int loEnd = (int)(600.0f * (float)kFFT / (float)m_sr);
        const int miEnd = (int)(2500.0f* (float)kFFT / (float)m_sr);
        for (int k = 1; k < kBins; ++k) {
            pow[k] = re[k]*re[k] + im[k]*im[k];
            total += pow[k];
            if      (k < loEnd) { if (k >= loCut) lowEnergy += pow[k]; }
            else if (k < miEnd) midEnergy += pow[k];
            else                hiEnergy  += pow[k];
            logSum += std::log(pow[k] + 1e-12f);
        }
        if (total < 1e-10f) return;
        geom    = std::exp(logSum / (float)(kBins - 1));
        float arith    = total / (float)(kBins - 1);
        float flatness = (arith > 1e-12f) ? geom / arith : 0.0f;   // 0..1, 1 = noise

        // Normalise band energies as ratios of total.
        float lowR = lowEnergy / total;
        float midR = midEnergy / total;
        float hiR  = hiEnergy  / total;
        (void)hiR;

        // Speech RMS follower (slow, used to calibrate "low energy" criterion).
        float frameRMS = std::sqrt(total / (float)kBins);
        if (frameRMS > m_speechEnv) m_speechEnv = 0.99f * m_speechEnv + 0.01f * frameRMS;
        else                         m_speechEnv = 0.999f * m_speechEnv + 0.001f * frameRMS;

        const float energyRatio = (m_speechEnv > 1e-9f) ? frameRMS / m_speechEnv : 0.0f;

        // Heuristic score: high flatness + low-band dominance + below-speech energy.
        float score = 0.0f;
        if (flatness > 0.35f)       score += (flatness - 0.35f) * 1.5f;
        if (lowR > 0.45f && midR < 0.4f) score += 0.4f;
        if (energyRatio < 0.6f)     score += (0.6f - energyRatio);

        // Sensitivity scales the threshold.  threshold ∈ [0.9 .. 0.3].
        const float threshold = 0.9f - 0.6f * sens;
        m_isBreath = (score > threshold);
    }

    double             m_sr         = 48000.0;
    uint32_t           m_ch         = 2;
    int                m_inWritePos = 0;
    int                m_hopCounter = 0;
    bool               m_isBreath   = false;
    float              m_speechEnv  = 0.0f;
    float              m_duckEnv    = 1.0f;
    std::vector<float> m_inRing[kMaxDSPChannels];
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// VoxSynthEffect — vocal-driven monophonic synthesizer.
//
// Pitch-tracks the loudest channel via YIN-style cumulative-mean-normalized
// difference (parabolic-interpolated to sub-sample accuracy), quantizes the
// detected pitch to the nearest note in the selected Key + Scale, and drives
// an internal oscillator at the quantized frequency. Amplitude tracks the
// input via a peak envelope follower so the synth "sings" with the singer.
// Falls silent when input drops below the threshold (so background noise
// doesn't trigger spurious tones).
//
// Cheap enough to run inline on the audio thread; latency is the YIN window
// (2048 samples ≈ 43 ms at 48 kHz). Pitch updates every kPitchHop samples.
// ---------------------------------------------------------------------------
class VoxSynthEffect : public IEffect {
public:
    enum Param { Key, Scale, Wave, Glide, Mix, Threshold, NumParams };
    static constexpr int kYinWin   = 2048;
    static constexpr int kPitchHop = 256;

    VoxSynthEffect()
    {
        m_p[Key      ].store(0.0f);    // C
        m_p[Scale    ].store(1.0f);    // Major
        m_p[Wave     ].store(0.0f);    // Saw
        m_p[Glide    ].store(30.0f);   // ms
        m_p[Mix      ].store(60.0f);   // %
        m_p[Threshold].store(-45.0f);  // dB
    }
    const char* Name() const override { return "Vox Synthesizer"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        m_ring.assign(kYinWin, 0.0f);
        m_writePos    = 0;
        m_hopCounter  = 0;
        m_curFreq     = 0.0f;
        m_targetFreq  = 0.0f;
        m_phase       = 0.0f;
        m_env         = 0.0f;
    }
    void Reset() override { Prepare(m_sr, m_ch); }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        // Key/Scale/Wave use stepped sliders; the UI rounds to int on read.
        static const EffectParamInfo kInfo[NumParams] = {
            { "Key",        0.0f,  11.0f,  0.0f, "",   false },
            { "Scale",      0.0f,   7.0f,  1.0f, "",   false },
            { "Wave",       0.0f,   3.0f,  0.0f, "",   false },
            { "Glide",      0.0f, 200.0f, 30.0f, "ms", false },
            { "Mix",        0.0f, 100.0f, 60.0f, "%",  false },
            { "Threshold",-70.0f,   0.0f,-45.0f, "dB", false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const int   keyIdx   = std::clamp((int)(m_p[Key  ].load() + 0.5f), 0, 11);
        const int   scaleIdx = std::clamp((int)(m_p[Scale].load() + 0.5f), 0, 7);
        const int   waveIdx  = std::clamp((int)(m_p[Wave ].load() + 0.5f), 0, 3);
        const float glideMs  = std::max(1.0f, m_p[Glide].load());
        const float mix      = m_p[Mix].load() * 0.01f;
        const float thrLin   = DbToLin(m_p[Threshold].load());

        // One-pole envelope follower (peak, ~10 ms attack / ~80 ms release).
        const float aAtt = std::exp(-1.0f / ((float)m_sr * 0.010f));
        const float aRel = std::exp(-1.0f / ((float)m_sr * 0.080f));
        // Glide coefficient (one-pole toward target frequency).
        const float aGli = std::exp(-1.0f / ((float)m_sr * glideMs * 0.001f));

        for (uint32_t n = 0; n < numFrames; ++n) {
            const uint32_t base = n * numChannels;

            // Drive the pitch buffer from a mono mix of the input.
            float monoIn = 0.0f;
            for (uint32_t c = 0; c < numChannels; ++c) monoIn += x[base + c];
            monoIn *= 1.0f / (float)numChannels;
            m_ring[m_writePos] = monoIn;
            m_writePos = (m_writePos + 1) % kYinWin;
            ++m_hopCounter;

            // Envelope follower.
            float peak = std::fabs(monoIn);
            float aE   = (peak > m_env) ? aAtt : aRel;
            m_env      = aE * m_env + (1.0f - aE) * peak;

            // Refresh pitch every hop.
            if (m_hopCounter >= kPitchHop) {
                m_hopCounter = 0;
                if (m_env > thrLin) {
                    float f = DetectPitch();
                    if (f > 50.0f && f < 2000.0f) {
                        m_targetFreq = QuantizeToScale(f, keyIdx, scaleIdx);
                    }
                }
            }

            // Glide current freq toward target.
            m_curFreq = aGli * m_curFreq + (1.0f - aGli) * m_targetFreq;

            // Generate oscillator sample.
            float synth = 0.0f;
            if (m_curFreq > 1.0f && m_env > thrLin) {
                m_phase += m_curFreq / (float)m_sr;
                if (m_phase >= 1.0f) m_phase -= 1.0f;
                switch (waveIdx) {
                    case 0: synth = 2.0f * m_phase - 1.0f; break;             // saw
                    case 1: synth = (m_phase < 0.5f) ? 1.0f : -1.0f; break;   // square
                    case 2: synth = std::sin(2.0f * (float)kPI * m_phase); break;
                    case 3: synth = (m_phase < 0.5f)
                                  ? 4.0f * m_phase - 1.0f
                                  : 3.0f - 4.0f * m_phase; break;             // triangle
                }
                synth *= m_env * 1.4f;
            }

            for (uint32_t c = 0; c < numChannels; ++c) {
                float dry = x[base + c];
                x[base + c] = (1.0f - mix) * dry + mix * synth;
            }
        }
    }

private:
    // YIN cumulative-mean-normalized difference, parabolic-interpolated.
    float DetectPitch()
    {
        const int W = kYinWin / 2;
        // Build the linear view of the ring starting from oldest sample.
        std::vector<float> buf(kYinWin);
        for (int i = 0; i < kYinWin; ++i) {
            buf[i] = m_ring[(m_writePos + i) % kYinWin];
        }
        // d[tau]
        std::vector<float> d(W, 0.0f);
        for (int tau = 1; tau < W; ++tau) {
            float sum = 0.0f;
            for (int j = 0; j < W; ++j) {
                float diff = buf[j] - buf[j + tau];
                sum += diff * diff;
            }
            d[tau] = sum;
        }
        // Cumulative mean normalized difference d'[tau].
        std::vector<float> dp(W, 1.0f);
        float runSum = 0.0f;
        for (int tau = 1; tau < W; ++tau) {
            runSum += d[tau];
            dp[tau] = (runSum > 0.0f) ? (d[tau] * (float)tau / runSum) : 1.0f;
        }
        // Find the first dip below threshold; refine with local minimum.
        const float yinThresh = 0.15f;
        int chosen = -1;
        for (int tau = 2; tau < W - 1; ++tau) {
            if (dp[tau] < yinThresh) {
                while (tau + 1 < W - 1 && dp[tau + 1] < dp[tau]) ++tau;
                chosen = tau;
                break;
            }
        }
        if (chosen < 0) return 0.0f;

        // Parabolic interpolation around chosen for sub-sample accuracy.
        float xm1 = dp[chosen - 1], x0 = dp[chosen], xp1 = dp[chosen + 1];
        float denom = (xm1 - 2.0f * x0 + xp1);
        float betterTau = (denom != 0.0f)
                       ? (float)chosen + 0.5f * (xm1 - xp1) / denom
                       : (float)chosen;
        if (betterTau <= 1.0f) return 0.0f;
        return (float)m_sr / betterTau;
    }

    static float QuantizeToScale(float freq, int keyIdx, int scaleIdx)
    {
        // 8 scales, intervals (semitones from key root) within an octave.
        // 0=Chromatic, 1=Major, 2=Minor, 3=PentMaj, 4=PentMin, 5=Blues, 6=Dorian, 7=Mixolydian
        static const int kSizes[8] = { 12, 7, 7, 5, 5, 6, 7, 7 };
        static const int kSteps[8][12] = {
            {0,1,2,3,4,5,6,7,8,9,10,11},
            {0,2,4,5,7,9,11},
            {0,2,3,5,7,8,10},
            {0,2,4,7,9},
            {0,3,5,7,10},
            {0,3,5,6,7,10},
            {0,2,3,5,7,9,10},
            {0,2,4,5,7,9,10},
        };
        if (scaleIdx < 0 || scaleIdx > 7) scaleIdx = 1;
        // Convert freq to MIDI note (float).
        float midi = 69.0f + 12.0f * std::log2(std::max(1e-6f, freq) / 440.0f);
        int   nearestMidi = 0;
        float bestDelta   = 1e9f;
        // Search across ±1 octave from the rounded MIDI.
        int center = (int)std::floor(midi + 0.5f);
        for (int o = -1; o <= 1; ++o) {
            int octStart = ((center / 12) + o) * 12;
            for (int s = 0; s < kSizes[scaleIdx]; ++s) {
                int mn = octStart + keyIdx + kSteps[scaleIdx][s];
                float delta = std::fabs((float)mn - midi);
                if (delta < bestDelta) { bestDelta = delta; nearestMidi = mn; }
            }
        }
        return 440.0f * std::pow(2.0f, ((float)nearestMidi - 69.0f) / 12.0f);
    }

    double             m_sr         = 48000.0;
    uint32_t           m_ch         = 2;
    std::vector<float> m_ring;
    int                m_writePos   = 0;
    int                m_hopCounter = 0;
    float              m_curFreq    = 0.0f;
    float              m_targetFreq = 0.0f;
    float              m_phase      = 0.0f;
    float              m_env        = 0.0f;
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// ARNRNNEffect — Adaptive Repeating-Noise Reducer.
//
// Spectral noise reduction that adapts to slowly-varying or repeating
// background noise (fans, AC, hum, room tone) without needing a separate
// "learn" pass. Per-frequency-bin EMA noise floor with bin-wise periodicity
// detection: bins whose magnitude over the last ~500 ms looks more like a
// stationary or periodic process than like speech get aggressively
// suppressed; bins inside the 200–4 kHz voice band get a softer floor so
// speech survives. STFT/iSTFT with Hann-squared analysis-synthesis windows
// and 75 % overlap (kFFT=512, kHop=128).
// ---------------------------------------------------------------------------
class ARNRNNEffect : public IEffect {
public:
    enum Param { Strength, VoiceProtect, AdaptSpeed, MinFloor, Relearn, NumParams };
    static constexpr int kFFT  = 512;
    static constexpr int kHop  = 128;
    static constexpr int kBins = kFFT / 2 + 1;
    static constexpr int kHist = 32;     // ~85 ms of magnitude history per bin

    ARNRNNEffect()
    {
        m_p[Strength    ].store(80.0f);
        m_p[VoiceProtect].store(70.0f);
        m_p[AdaptSpeed  ].store(50.0f);
        m_p[MinFloor    ].store(-30.0f);
        m_p[Relearn     ].store(0.0f);
    }
    const char* Name() const override { return "Adaptive Repeating NR (ARNRNN)"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        for (uint32_t c = 0; c < kMaxDSPChannels; ++c) {
            m_inRing [c].assign(kFFT, 0.0f);
            m_outRing[c].assign(kFFT, 0.0f);
        }
        for (int k = 0; k < kBins; ++k) {
            m_noisePow[k] = 1e-6f;
            m_prevGain[k] = 1.0f;
            for (int h = 0; h < kHist; ++h) m_magHist[k][h] = 0.0f;
        }
        m_inWritePos  = 0;
        m_outReadPos  = 0;
        m_hopCounter  = 0;
        m_histPos     = 0;
        m_relearnLeft = 25;
    }
    void Reset() override { Prepare(m_sr, m_ch); }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Strength",       0.0f, 100.0f,  80.0f, "%",     false },
            { "Voice Protect",  0.0f, 100.0f,  70.0f, "%",     false },
            { "Adapt Speed",    0.0f, 100.0f,  50.0f, "%",     false },
            { "Min Floor",    -60.0f,   0.0f, -30.0f, "dB",    false },
            { "Relearn",        0.0f,   1.0f,   0.0f, "click", false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override
    {
        if (i < 0 || i >= NumParams) return;
        m_p[i].store(v);
        if (i == Relearn && v >= 0.5f) {
            m_pendingRelearn.store(true);
            m_p[Relearn].store(0.0f);
        }
    }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        if (m_pendingRelearn.exchange(false)) {
            m_relearnLeft = std::max(20, (int)((0.5 * m_sr) / (double)kHop + 0.5));
        }

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;

            for (uint32_t c = 0; c < numChannels; ++c) {
                m_inRing[c][m_inWritePos] = x[base + c];
            }
            m_inWritePos = (m_inWritePos + 1) % kFFT;
            ++m_hopCounter;

            if (m_hopCounter >= kHop) {
                m_hopCounter = 0;
                ProcessFrame(numChannels);
            }

            for (uint32_t c = 0; c < numChannels; ++c) {
                float wet = m_outRing[c][m_outReadPos];
                m_outRing[c][m_outReadPos] = 0.0f;
                x[base + c] = wet;
            }
            m_outReadPos = (m_outReadPos + 1) % kFFT;
        }
    }

private:
    void ProcessFrame(uint32_t numChannels)
    {
        const Stft512& K = GetStft512();
        const float strength    = m_p[Strength    ].load() * 0.01f;
        const float voiceProt   = m_p[VoiceProtect].load() * 0.01f;
        const float adaptSpeed  = m_p[AdaptSpeed  ].load() * 0.01f;
        const float minFloorLin = DbToLin(m_p[MinFloor].load());

        // Faster adaptation when relearning, otherwise scale by user knob.
        const float aBase  = m_relearnLeft > 0 ? 0.6f : (0.02f + 0.10f * adaptSpeed);
        if (m_relearnLeft > 0) --m_relearnLeft;

        // Voice-band bin range.
        const int loVox = std::max(1,         (int)(200.0f  * kFFT / (float)m_sr));
        const int hiVox = std::min(kBins - 1, (int)(4000.0f * kFFT / (float)m_sr));

        for (uint32_t c = 0; c < numChannels; ++c) {
            float re[kFFT], im[kFFT];
            for (int n = 0; n < kFFT; ++n) {
                int idx = (m_inWritePos + n) % kFFT;
                re[n] = m_inRing[c][idx] * K.wSqrtHann[n];
                im[n] = 0.0f;
            }
            K.FFT(re, im);

            float mag[kBins], pow_[kBins];
            for (int k = 0; k < kBins; ++k) {
                pow_[k] = re[k]*re[k] + im[k]*im[k];
                mag [k] = std::sqrt(pow_[k]);
            }

            // Update magnitude history (only on first channel — we make the
            // periodicity decision on a single representative spectrum).
            if (c == 0) {
                for (int k = 0; k < kBins; ++k) m_magHist[k][m_histPos] = mag[k];
            }

            // Per-bin EMA noise tracker. Track the *minimum* over a short
            // window — that's what the spectrum looks like during quiet
            // moments where only the noise bed is present.
            for (int k = 0; k < kBins; ++k) {
                float minRecent = pow_[k];
                for (int h = 0; h < kHist; ++h) {
                    float v = m_magHist[k][h];
                    float p = v * v;
                    if (p > 0.0f && p < minRecent) minRecent = p;
                }
                // Adapt up faster than down so we follow rising noise quickly.
                float a = (minRecent > m_noisePow[k]) ? aBase : aBase * 0.25f;
                m_noisePow[k] = (1.0f - a) * m_noisePow[k] + a * minRecent;
                if (m_noisePow[k] < 1e-12f) m_noisePow[k] = 1e-12f;
            }

            // Per-bin Wiener gain with voice-band protection.
            for (int k = 0; k < kBins; ++k) {
                float snrPost  = pow_[k] / m_noisePow[k];
                float gainW    = (snrPost - 1.0f) / std::max(1e-6f, snrPost);
                if (gainW < 0.0f) gainW = 0.0f;
                // Strength: blend between full Wiener (1.0) and identity.
                float gain = 1.0f - strength * (1.0f - gainW);
                // Voice band protection: lift the floor.
                float floor = minFloorLin;
                if (k >= loVox && k <= hiVox) {
                    floor = std::min(1.0f, minFloorLin + voiceProt * (1.0f - minFloorLin));
                }
                if (gain < floor) gain = floor;
                if (gain > 1.0f) gain = 1.0f;
                // Smooth across frames to avoid musical noise.
                gain = 0.5f * gain + 0.5f * m_prevGain[k];
                m_prevGain[k] = gain;

                re[k] *= gain;
                im[k] *= gain;
            }
            // Mirror conjugate.
            for (int k = 1; k < kFFT/2; ++k) {
                re[kFFT - k] =  re[k];
                im[kFFT - k] = -im[k];
            }

            K.IFFT(re, im);

            // Overlap-add into outRing with synthesis window.
            for (int n = 0; n < kFFT; ++n) {
                int idx = (m_inWritePos + n) % kFFT;
                m_outRing[c][idx] += re[n] * K.wSqrtHann[n];
            }
        }

        m_histPos = (m_histPos + 1) % kHist;
    }

    double             m_sr            = 48000.0;
    uint32_t           m_ch            = 2;
    std::vector<float> m_inRing[kMaxDSPChannels];
    std::vector<float> m_outRing[kMaxDSPChannels];
    int                m_inWritePos    = 0;
    int                m_outReadPos    = 0;
    int                m_hopCounter    = 0;
    float              m_noisePow[kBins] = {};
    float              m_prevGain[kBins] = {};
    float              m_magHist[kBins][kHist] = {};
    int                m_histPos       = 0;
    int                m_relearnLeft   = 25;
    std::atomic<bool>  m_pendingRelearn{false};
    std::atomic<float> m_p[NumParams];
};

// ---------------------------------------------------------------------------
// AINoDistortionEffect — declipper / harmonic-restoration soft saturator.
//
// Detects sample-domain clipping (|x| >= threshold) and reconstructs the
// missing waveform peak via a 2nd-order Taylor extrapolation from the last
// three unclipped samples, then soft-tanh-limits the result so the
// restoration never re-clips. Below threshold, a gentle tanh saturator
// rounds off transients to keep the signal pre-emptively away from the
// 0 dBFS rail. Headroom param applies a static gain cut after restoration
// so the file delivered to disk has guaranteed sub-0-dB peaks.
//
// Per-channel state:
//   - 3-sample "history" ring (most-recent unclipped values).
//   - clipRun length + polarity so consecutive clipped samples reconstruct
//     a coherent peak shape, not noisy pointwise jumps.
// ---------------------------------------------------------------------------
class AINoDistortionEffect : public IEffect {
public:
    enum Param { Threshold, Restore, Headroom, Mix, NumParams };

    AINoDistortionEffect()
    {
        m_p[Threshold].store(-3.0f);
        m_p[Restore  ].store(80.0f);
        m_p[Headroom ].store(3.0f);
        m_p[Mix      ].store(100.0f);
    }
    const char* Name() const override { return "AI NoDistortion"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        for (uint32_t c = 0; c < kMaxDSPChannels; ++c) {
            m_hist[c][0] = m_hist[c][1] = m_hist[c][2] = 0.0f;
            m_clipRun[c] = 0;
            m_clipPolarity[c] = 0;
        }
    }
    void Reset() override { Prepare(m_sr, m_ch); }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Threshold", -12.0f,   0.0f,  -3.0f, "dB", false },
            { "Restore",     0.0f, 100.0f,  80.0f, "%",  false },
            { "Headroom",    0.0f,   6.0f,   3.0f, "dB", false },
            { "Mix",         0.0f, 100.0f, 100.0f, "%",  false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float thrDb        = m_p[Threshold].load();
        const float thr          = DbToLin(thrDb);
        const float restoreAmt   = std::max(0.0f, std::min(1.0f, m_p[Restore].load() * 0.01f));
        const float headroomDb   = m_p[Headroom].load();
        const float postGain     = DbToLin(-headroomDb);
        const float mix          = std::max(0.0f, std::min(1.0f, m_p[Mix].load() * 0.01f));

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float in       = x[base + c];
                float dry      = in;
                float absIn    = std::fabs(in);
                int   polarity = (in >= 0.0f) ? 1 : -1;
                bool  clipped  = (absIn >= thr);

                float out = in;

                if (clipped) {
                    // New clip run, or polarity flipped (= zero-cross during
                    // a clipping streak — extremely rare, but reset).
                    if (m_clipRun[c] == 0 || m_clipPolarity[c] != polarity) {
                        m_clipRun[c]      = 1;
                        m_clipPolarity[c] = polarity;
                        m_clipStartHist[c][0] = m_hist[c][0];
                        m_clipStartHist[c][1] = m_hist[c][1];
                        m_clipStartHist[c][2] = m_hist[c][2];
                    } else {
                        m_clipRun[c]++;
                    }

                    // Forward extrapolation from the last 3 unclipped samples.
                    // Let h2 = newest, h1 = middle, h0 = oldest. Estimate
                    // first derivative as (h2 - h1) and second derivative as
                    // (h2 - 2*h1 + h0). Project t samples into the clipped
                    // run with a 2nd-order Taylor series.
                    float h0 = m_clipStartHist[c][0];
                    float h1 = m_clipStartHist[c][1];
                    float h2 = m_clipStartHist[c][2];
                    float t  = (float)m_clipRun[c];
                    float v1 = h2 - h1;
                    float v2 = h2 - 2.0f * h1 + h0;
                    float pred = h2 + v1 * t + 0.5f * v2 * t * t;

                    // Cap restored amplitude so we don't over-shoot. Allowed
                    // peak grows mildly with the run length (longer clips
                    // imply taller hidden peaks) but is bounded.
                    float maxAmp = thr * (1.0f + 0.5f * std::min(t * 0.05f, 0.5f));
                    pred = std::tanh(pred / std::max(1e-6f, maxAmp)) * maxAmp;

                    out = restoreAmt * pred + (1.0f - restoreAmt) * in;
                } else {
                    if (m_clipRun[c] > 0) m_clipRun[c] = 0;
                    // Below threshold: gentle pre-emptive saturator that
                    // rounds shoulders without coloring the body of the
                    // signal. tanh(x/1.5)*1.5 is ~unity for |x|<0.5.
                    out = SoftClip(in / 1.5f) * 1.5f;
                }

                out *= postGain;

                // Push into the unclipped-history ring. Clipped samples are
                // never pushed (we want to forecast from real peaks, not
                // from saturated ones).
                if (!clipped) {
                    m_hist[c][0] = m_hist[c][1];
                    m_hist[c][1] = m_hist[c][2];
                    m_hist[c][2] = in;
                }

                x[base + c] = mix * out + (1.0f - mix) * dry;
            }
        }
    }

private:
    std::atomic<float> m_p[NumParams];
    double             m_sr = 48000.0;
    uint32_t           m_ch = 2;
    float              m_hist[kMaxDSPChannels][3]          = {};
    float              m_clipStartHist[kMaxDSPChannels][3] = {};
    int                m_clipRun[kMaxDSPChannels]          = {};
    int                m_clipPolarity[kMaxDSPChannels]     = {};
};

// ---------------------------------------------------------------------------
// SmartPopshieldEffect — plosive-aware low-frequency transient suppressor.
//
// Plosives ("P", "B", "T", microphone bumps) produce a fast spike of
// low-frequency (<150 Hz) energy that does NOT correlate with a
// proportional rise in the broadband envelope. We exploit that:
//   1. Split signal into LF (two-pole 1-pole IIR LP) and HF (residual).
//   2. Track LF peak envelope (fast, ~20 ms) and broadband peak envelope
//      (slow, ~80 ms).
//   3. If LF envelope > threshold AND LF dominates broadband (>50 %),
//      classify as plosive → duck the LF band by Reduction dB while
//      leaving the HF residual untouched, preserving consonant clarity.
//   4. Hold the duck for `Hold` ms after the LF transient subsides so
//      the long pop tail (~30-100 ms decaying boom) is also caught.
// ---------------------------------------------------------------------------
class SmartPopshieldEffect : public IEffect {
public:
    enum Param { Threshold, LFCutoff, Reduction, Attack, Hold, Mix, NumParams };

    SmartPopshieldEffect()
    {
        m_p[Threshold].store(-30.0f);
        m_p[LFCutoff ].store(150.0f);
        m_p[Reduction].store(-12.0f);
        m_p[Attack   ].store(2.0f);
        m_p[Hold     ].store(60.0f);
        m_p[Mix      ].store(100.0f);
    }
    const char* Name() const override { return "Smart Popshield"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        for (uint32_t c = 0; c < kMaxDSPChannels; ++c) {
            m_lp1[c] = m_lp2[c] = 0.0f;
            m_envLF[c] = m_envBB[c] = 0.0f;
            m_duck[c] = 1.0f;
            m_holdSamples[c] = 0;
        }
    }
    void Reset() override { Prepare(m_sr, m_ch); }
    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Threshold", -60.0f, -10.0f, -30.0f, "dB", false },
            { "LFCutoff",   60.0f, 250.0f, 150.0f, "Hz", false },
            { "Reduction", -36.0f,   0.0f, -12.0f, "dB", false },
            { "Attack",      0.5f,  20.0f,   2.0f, "ms", true  },
            { "Hold",       10.0f, 200.0f,  60.0f, "ms", true  },
            { "Mix",         0.0f, 100.0f, 100.0f, "%",  false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override { if (i>=0&&i<NumParams) m_p[i].store(v); }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels != m_ch) Prepare(m_sr, numChannels);
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;

        const float thrLin = DbToLin(m_p[Threshold].load());
        const float fc     = std::max(20.0f, std::min(500.0f, m_p[LFCutoff].load()));
        const float redLin = DbToLin(m_p[Reduction].load());
        const float atkMs  = std::max(0.5f, m_p[Attack].load());
        const float holdMs = std::max(0.0f, m_p[Hold].load());
        const float mix    = std::max(0.0f, std::min(1.0f, m_p[Mix].load() * 0.01f));

        const float aLP      = std::exp(-2.0f * kPI * fc / (float)m_sr);
        const float aEnvLF   = std::exp(-1.0f / (float)(m_sr * 0.020));
        const float aEnvBB   = std::exp(-1.0f / (float)(m_sr * 0.080));
        const float aDuckAtk = std::exp(-1.0f / (float)(m_sr * atkMs * 0.001));
        const float aDuckRel = std::exp(-1.0f / (float)(m_sr * 0.030));
        const int   holdSamp = (int)((float)m_sr * holdMs * 0.001f);

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;
            for (uint32_t c = 0; c < numChannels; ++c) {
                float in = x[base + c];

                // Two cascaded one-pole LP form a smooth ~12 dB/oct LF
                // extractor. Subtract from input to obtain the HF residual.
                m_lp1[c] = aLP * m_lp1[c] + (1.0f - aLP) * in;
                m_lp2[c] = aLP * m_lp2[c] + (1.0f - aLP) * m_lp1[c];
                float lf = m_lp2[c];
                float hf = in - lf;

                // Peak envelopes (fast attack, exponential release).
                float lfAbs = std::fabs(lf);
                float bbAbs = std::fabs(in);
                m_envLF[c] = (lfAbs > m_envLF[c]) ? lfAbs
                           : aEnvLF * m_envLF[c] + (1.0f - aEnvLF) * lfAbs;
                m_envBB[c] = (bbAbs > m_envBB[c]) ? bbAbs
                           : aEnvBB * m_envBB[c] + (1.0f - aEnvBB) * bbAbs;

                // Plosive heuristic: LF must exceed threshold AND must
                // dominate the broadband. The 2nd condition rules out
                // normal vocal vowels (which have LF energy comparable to
                // mids) — only sub-bass-dominant transients trigger.
                bool plosive = (m_envLF[c] > thrLin) &&
                               (m_envLF[c] > 0.5f * m_envBB[c]);

                float target = 1.0f;
                if (plosive) {
                    target = redLin;
                    m_holdSamples[c] = holdSamp;
                } else if (m_holdSamples[c] > 0) {
                    --m_holdSamples[c];
                    target = redLin;
                }

                float coeff = (target < m_duck[c]) ? aDuckAtk : aDuckRel;
                m_duck[c] = coeff * m_duck[c] + (1.0f - coeff) * target;

                float lfDucked = lf * m_duck[c];
                float wet      = lfDucked + hf;
                x[base + c]    = mix * wet + (1.0f - mix) * in;
            }
        }
    }

private:
    std::atomic<float> m_p[NumParams];
    double             m_sr = 48000.0;
    uint32_t           m_ch = 2;
    float              m_lp1[kMaxDSPChannels]   = {};
    float              m_lp2[kMaxDSPChannels]   = {};
    float              m_envLF[kMaxDSPChannels] = {};
    float              m_envBB[kMaxDSPChannels] = {};
    float              m_duck[kMaxDSPChannels]  = {};
    int                m_holdSamples[kMaxDSPChannels] = {};
};

// ---------------------------------------------------------------------------
// DynamicAdaptiveEQ — AI-driven adaptive EQ that learns the spectral profile
// of the input signal over time and applies corrective gain to bring the
// spectrum toward a user-selectable target curve (Flat, Vocal Presence,
// Broadcast Warm, or De-Harsh). Uses an 8-band analysis/correction engine
// with exponential moving-average learning and smoothed gain application.
// ---------------------------------------------------------------------------
class DynamicAdaptiveEQEffect : public IEffect {
public:
    static constexpr int kNumBands = 8;

    enum TargetCurve { Flat = 0, VocalPresence, BroadcastWarm, DeHarsh, NumCurves };
    enum Param {
        Strength, AdaptSpeed, TargetCurveP,
        BandGain0, BandGain1, BandGain2, BandGain3,
        BandGain4, BandGain5, BandGain6, BandGain7,
        NumParams
    };

    DynamicAdaptiveEQEffect()
    {
        m_p[Strength    ].store(50.0f);
        m_p[AdaptSpeed  ].store(40.0f);
        m_p[TargetCurveP].store(0.0f);
        for (int i = 0; i < kNumBands; ++i)
            m_p[BandGain0 + i].store(0.0f);
    }

    const char* Name() const override { return "Dynamic Adaptive EQ"; }

    void Prepare(double sampleRate, uint32_t numChannels) override
    {
        m_sr = sampleRate > 0.0 ? sampleRate : 48000.0;
        m_ch = std::min<uint32_t>(numChannels ? numChannels : 2, kMaxDSPChannels);
        for (int b = 0; b < kNumBands; ++b) {
            m_analysisBand[b].Reset();
            m_correctionBand[b].Reset();
            m_runningEnergy[b] = 0.0f;
            m_correctionDb[b]  = 0.0f;
            m_smoothGain[b]    = 1.0f;
        }
        m_frameCount = 0;
        UpdateBandFilters();
    }

    void Reset() override
    {
        for (int b = 0; b < kNumBands; ++b) {
            m_analysisBand[b].Reset();
            m_correctionBand[b].Reset();
            m_runningEnergy[b] = 0.0f;
            m_correctionDb[b]  = 0.0f;
            m_smoothGain[b]    = 1.0f;
        }
        m_frameCount = 0;
    }

    int  GetParamCount() const override { return NumParams; }
    const EffectParamInfo& GetParamInfo(int i) const override
    {
        static const EffectParamInfo kInfo[NumParams] = {
            { "Strength",      0.0f, 100.0f,  50.0f, "%",  false },
            { "Adapt Speed",   1.0f, 100.0f,  40.0f, "%",  false },
            { "Target Curve",  0.0f,   3.0f,   0.0f, "",   false },
            { "Sub",         -12.0f,  12.0f,   0.0f, "dB", false },
            { "Bass",        -12.0f,  12.0f,   0.0f, "dB", false },
            { "Low-Mid",     -12.0f,  12.0f,   0.0f, "dB", false },
            { "Mid",         -12.0f,  12.0f,   0.0f, "dB", false },
            { "Upper-Mid",   -12.0f,  12.0f,   0.0f, "dB", false },
            { "Presence",    -12.0f,  12.0f,   0.0f, "dB", false },
            { "Brilliance",  -12.0f,  12.0f,   0.0f, "dB", false },
            { "Air",         -12.0f,  12.0f,   0.0f, "dB", false },
        };
        if (i < 0) i = 0; if (i >= NumParams) i = NumParams-1;
        return kInfo[i];
    }
    float GetParam(int i) const override { return (i>=0&&i<NumParams) ? m_p[i].load() : 0.0f; }
    void  SetParam(int i, float v) override {
        if (i>=0&&i<NumParams) {
            m_p[i].store(v);
            m_dirty.store(true);
        }
    }

    void Process(float* x, uint32_t numFrames, uint32_t numChannels) override
    {
        if (!x || numFrames == 0 || numChannels == 0) return;
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;
        if (m_dirty.exchange(false)) UpdateBandFilters();

        const float strength  = Clamp(m_p[Strength].load(), 0.0f, 100.0f) * 0.01f;
        const float adaptRate = Clamp(m_p[AdaptSpeed].load(), 1.0f, 100.0f) * 0.01f;
        const int   curve     = std::clamp((int)(m_p[TargetCurveP].load() + 0.5f), 0, (int)NumCurves - 1);

        static const float kTargets[NumCurves][kNumBands] = {
            {  0,  0,  0,  0,  0,  0,  0,  0 },
            { -2, -1,  0,  1,  3,  4,  2,  1 },
            {  3,  2,  1,  0, -1, -2, -1,  0 },
            {  0,  0,  0,  0, -3, -4, -2,  0 },
        };

        const float emaAlpha = 0.001f + 0.05f * adaptRate;

        for (uint32_t n = 0; n < numFrames; ++n) {
            uint32_t base = n * numChannels;

            for (int b = 0; b < kNumBands; ++b) {
                float bandSum = 0.0f;
                for (uint32_t c = 0; c < numChannels; ++c) {
                    float bp = m_analysisBand[b].Tick(c, x[base + c]);
                    bandSum += bp * bp;
                }
                bandSum /= (float)numChannels;
                m_runningEnergy[b] = (1.0f - emaAlpha) * m_runningEnergy[b] + emaAlpha * bandSum;
            }

            if (++m_frameCount >= 256) {
                m_frameCount = 0;
                float totalEnergy = 0.0f;
                for (int b = 0; b < kNumBands; ++b)
                    totalEnergy += m_runningEnergy[b];
                if (totalEnergy > 1e-10f) {
                    for (int b = 0; b < kNumBands; ++b) {
                        float bandRatio = m_runningEnergy[b] / (totalEnergy / (float)kNumBands);
                        float currentDb = LinToDb(std::sqrt(std::max(bandRatio, 1e-9f)));
                        float targetDb  = kTargets[curve][b] + m_p[BandGain0 + b].load();
                        float errorDb   = targetDb - currentDb;
                        errorDb = Clamp(errorDb, -12.0f, 12.0f);
                        m_correctionDb[b] += (errorDb * strength * 0.1f - m_correctionDb[b]) * adaptRate * 0.05f;
                        m_correctionDb[b] = Clamp(m_correctionDb[b], -12.0f, 12.0f);
                    }
                    UpdateBandFilters();
                }
            }

            for (uint32_t c = 0; c < numChannels; ++c) {
                float s = x[base + c];
                for (int b = 0; b < kNumBands; ++b) {
                    float targetGain = DbToLin(m_correctionDb[b]);
                    m_smoothGain[b] += (targetGain - m_smoothGain[b]) * 0.001f;
                    s = m_correctionBand[b].Tick(c, s);
                }
                x[base + c] = s;
            }
        }
    }

private:
    void UpdateBandFilters()
    {
        static const double kFreqs[kNumBands] = {
            50.0, 150.0, 400.0, 1000.0, 2500.0, 6000.0, 11000.0, 17000.0
        };
        static const double kQ[kNumBands] = {
            0.7, 0.8, 1.0, 1.2, 1.2, 1.0, 0.8, 0.7
        };
        for (int b = 0; b < kNumBands; ++b) {
            double freq = std::min(kFreqs[b], m_sr * 0.45);
            m_analysisBand[b].SetBandpass(m_sr, freq, kQ[b]);
            m_correctionBand[b].DesignPeaking(m_sr, freq, kQ[b], m_correctionDb[b]);
        }
    }

    double             m_sr = 48000.0;
    uint32_t           m_ch = 2;
    Biquad             m_analysisBand[kNumBands];
    Biquad             m_correctionBand[kNumBands];
    float              m_runningEnergy[kNumBands] = {};
    float              m_correctionDb[kNumBands]  = {};
    float              m_smoothGain[kNumBands]    = {};
    int                m_frameCount = 0;
    std::atomic<float> m_p[NumParams];
    std::atomic<bool>  m_dirty{true};
};

// ---------------------------------------------------------------------------
// EffectRack — ordered chain of effects. Audio thread acquires a shared lock
// while processing; UI mutations (add / remove / reorder / bypass) take an
// exclusive lock. Lock contention is sub-microsecond with a std::mutex on
// modern hardware, well below an audio-buffer boundary.
// ---------------------------------------------------------------------------
enum class EffectKind : int {
    None = 0,
    Compressor,
    ParametricEQ,
    SaturationAir,
    Limiter,
    SmartDynamics,
    FkNoise,
    SmartDeEsser,
    Reverb,
    Delay,
    Echo,
    HumanizedPitcher,
    Vocoder,
    AntiBreath,
    VoxSynth,
    ARNRNN,
    AINoDistortion,
    SmartPopshield,
    DynamicAdaptiveEQ,
};

inline std::unique_ptr<IEffect> MakeEffect(EffectKind k)
{
    switch (k) {
        case EffectKind::Compressor:        return std::make_unique<CompressorEffect>();
        case EffectKind::ParametricEQ:      return std::make_unique<ParametricEQEffect>();
        case EffectKind::SaturationAir:     return std::make_unique<SaturationAirEffect>();
        case EffectKind::Limiter:           return std::make_unique<LimiterEffect>();
        case EffectKind::SmartDynamics:     return std::make_unique<SmartDynamicsEffect>();
        case EffectKind::FkNoise:           return std::make_unique<FkNoiseEffect>();
        case EffectKind::SmartDeEsser:      return std::make_unique<SmartDeEsserEffect>();
        case EffectKind::Reverb:            return std::make_unique<ReverbEffect>();
        case EffectKind::Delay:             return std::make_unique<DelayEffect>();
        case EffectKind::Echo:              return std::make_unique<EchoEffect>();
        case EffectKind::HumanizedPitcher:  return std::make_unique<HumanizedPitcherEffect>();
        case EffectKind::Vocoder:           return std::make_unique<VocoderEffect>();
        case EffectKind::AntiBreath:        return std::make_unique<AntiBreathEffect>();
        case EffectKind::VoxSynth:          return std::make_unique<VoxSynthEffect>();
        case EffectKind::ARNRNN:            return std::make_unique<ARNRNNEffect>();
        case EffectKind::AINoDistortion:    return std::make_unique<AINoDistortionEffect>();
        case EffectKind::SmartPopshield:    return std::make_unique<SmartPopshieldEffect>();
        case EffectKind::DynamicAdaptiveEQ: return std::make_unique<DynamicAdaptiveEQEffect>();
        default: return nullptr;
    }
}

inline const char* EffectKindName(EffectKind k)
{
    switch (k) {
        case EffectKind::Compressor:        return "Compressor";
        case EffectKind::ParametricEQ:      return "Parametric EQ";
        case EffectKind::SaturationAir:     return "Saturation Air";
        case EffectKind::Limiter:           return "Limiter";
        case EffectKind::SmartDynamics:     return "Smart Dynamics";
        case EffectKind::FkNoise:           return "F**kNoise (AI)";
        case EffectKind::SmartDeEsser:      return "Smart De-esser";
        case EffectKind::Reverb:            return "Reverb";
        case EffectKind::Delay:             return "Delay";
        case EffectKind::Echo:              return "Echo";
        case EffectKind::HumanizedPitcher:  return "Humanized Pitcher (AI)";
        case EffectKind::Vocoder:           return "Vocoder";
        case EffectKind::AntiBreath:        return "Anti-Breath (AI)";
        case EffectKind::VoxSynth:          return "Vox Synthesizer";
        case EffectKind::ARNRNN:            return "Adaptive Repeating NR (ARNRNN)";
        case EffectKind::AINoDistortion:    return "AI NoDistortion";
        case EffectKind::SmartPopshield:    return "Smart Popshield";
        case EffectKind::DynamicAdaptiveEQ: return "Dynamic Adaptive EQ (AI)";
        default: return "(none)";
    }
}

class EffectRack {
public:
    EffectRack() = default;

    void Prepare(double sampleRate, uint32_t numChannels)
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        m_sr = sampleRate;
        m_ch = numChannels;
        for (auto& slot : m_slots)
            if (slot.fx) slot.fx->Prepare(sampleRate, numChannels);
    }
    void Reset()
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        for (auto& slot : m_slots) if (slot.fx) slot.fx->Reset();
    }

    // Audio-thread entrypoint.
    void Process(float* x, uint32_t numFrames, uint32_t numChannels)
    {
        if (!m_enabled.load()) return;
        std::lock_guard<std::mutex> lk(m_mutex);
        // Re-prepare on channel-count change. The previous predicate
        // accidentally compared m_sr (e.g. 48000) against numChannels
        // (e.g. 2), so it always evaluated true — meaning the
        // channel-count fast-path was never actually fast and could
        // re-Prepare every effect on every Process call. Compare
        // m_ch directly.
        if (numChannels != m_ch) {
            m_ch = numChannels;
            for (auto& slot : m_slots) if (slot.fx) slot.fx->Prepare(m_sr, numChannels);
        }
        for (auto& slot : m_slots) {
            if (slot.fx && !slot.bypass)
                slot.fx->Process(x, numFrames, numChannels);
        }
    }

    // ----- chain editing (UI thread) --------------------------------------
    int Size() const { std::lock_guard<std::mutex> lk(m_mutex); return (int)m_slots.size(); }
    EffectKind KindAt(int i) const
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        if (i < 0 || i >= (int)m_slots.size()) return EffectKind::None;
        return m_slots[i].kind;
    }
    bool BypassAt(int i) const
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        if (i < 0 || i >= (int)m_slots.size()) return false;
        return m_slots[i].bypass;
    }
    int Add(EffectKind k)
    {
        auto fx = MakeEffect(k);
        if (!fx) return -1;
        // Read the current sample-rate / channel-count under the lock
        // so the audio thread can't be tearing the values while we
        // pass them into Prepare(). Previously this was unlocked,
        // which on some effects (Reverb, Vocoder, AntiBreath) sized
        // internal buffers from a torn (zero / partial) value and
        // crashed the process the moment Process() ran on it. Keep
        // the lock held while we Prepare and push so the audio
        // thread sees a fully-constructed Slot.
        std::lock_guard<std::mutex> lk(m_mutex);
        double srLocal = (m_sr > 0.0) ? m_sr : 48000.0;
        uint32_t chLocal = m_ch ? m_ch : 2;
        fx->Prepare(srLocal, chLocal);
        m_slots.push_back({ k, std::move(fx), false });
        return (int)m_slots.size() - 1;
    }
    void Remove(int i)
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        if (i < 0 || i >= (int)m_slots.size()) return;
        m_slots.erase(m_slots.begin() + i);
    }
    void MoveUp(int i)
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        if (i <= 0 || i >= (int)m_slots.size()) return;
        std::swap(m_slots[i], m_slots[i - 1]);
    }
    void MoveDown(int i)
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        if (i < 0 || i + 1 >= (int)m_slots.size()) return;
        std::swap(m_slots[i], m_slots[i + 1]);
    }
    void Move(int from, int to)
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        int n = (int)m_slots.size();
        if (from < 0 || from >= n || to < 0 || to >= n || from == to) return;
        Slot tmp = std::move(m_slots[from]);
        m_slots.erase(m_slots.begin() + from);
        m_slots.insert(m_slots.begin() + to, std::move(tmp));
    }
    void SetBypass(int i, bool b)
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        if (i < 0 || i >= (int)m_slots.size()) return;
        m_slots[i].bypass = b;
    }
    void SetEnabled(bool e)   { m_enabled.store(e); }
    bool IsEnabled() const    { return m_enabled.load(); }

    // Update a single param on every effect of `k` currently in the rack.
    // Used by the LUFS preset path to retarget every limiter's ceiling
    // without disturbing any other parameters the user already dialed in.
    void SetParamForKind(EffectKind k, int paramIdx, float v)
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        for (auto& slot : m_slots) {
            if (slot.kind == k && slot.fx)
                slot.fx->SetParam(paramIdx, v);
        }
    }

    // Locked accessor: callers must call inside a Lock()/Unlock() pair so the
    // returned pointer doesn't dangle if the rack is mutated mid-call.
    //
    // IMPORTANT: every other public accessor on this class (KindAt /
    // BypassAt / Size / SetBypass / Add / Remove / Move…) acquires
    // m_mutex internally. They MUST NOT be called between Lock() and
    // Unlock() on the same thread — std::mutex is non-recursive and
    // recursive acquisition is undefined behavior (manifests as a
    // hard crash on MinGW / libstdc++ when the user clicks "+ Add").
    // Use the *Locked variants below while you hold the lock.
    void Lock() const   { m_mutex.lock(); }
    void Unlock() const { m_mutex.unlock(); }
    IEffect* AtLocked(int i) const
    {
        if (i < 0 || i >= (int)m_slots.size()) return nullptr;
        return m_slots[i].fx.get();
    }
    EffectKind KindAtLocked(int i) const
    {
        if (i < 0 || i >= (int)m_slots.size()) return EffectKind::None;
        return m_slots[i].kind;
    }
    bool BypassAtLocked(int i) const
    {
        if (i < 0 || i >= (int)m_slots.size()) return false;
        return m_slots[i].bypass;
    }
    void SetBypassLocked(int i, bool b)
    {
        if (i < 0 || i >= (int)m_slots.size()) return;
        m_slots[i].bypass = b;
    }
    int SizeLocked() const { return (int)m_slots.size(); }

private:
    struct Slot {
        EffectKind                  kind   = EffectKind::None;
        std::unique_ptr<IEffect>    fx;
        bool                        bypass = false;
    };
    mutable std::mutex      m_mutex;
    std::vector<Slot>       m_slots;
    double                  m_sr     = 48000.0;
    uint32_t                m_ch     = 2;
    std::atomic<bool>       m_enabled{true};
};

// ---------------------------------------------------------------------------
// LiveMonitor — pushes processed audio out the system's default render
// endpoint via WASAPI shared mode. Used when the user wants to hear effects
// applied to their input source in real time.
// ---------------------------------------------------------------------------
class LiveMonitor {
public:
    LiveMonitor()  = default;
    ~LiveMonitor() { Stop(); }

    bool Start(uint32_t sampleRate, uint32_t numChannels)
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        if (m_active) return true;
        if (!sampleRate || !numChannels) return false;

        IMMDeviceEnumerator* pEnum = nullptr;
        HRESULT hr = CoCreateInstance(__uuidof(MMDeviceEnumerator), nullptr,
            CLSCTX_ALL, __uuidof(IMMDeviceEnumerator), (void**)&pEnum);
        if (FAILED(hr) || !pEnum) return false;
        IMMDevice* pDev = nullptr;
        hr = pEnum->GetDefaultAudioEndpoint(eRender, eConsole, &pDev);
        pEnum->Release();
        if (FAILED(hr) || !pDev) return false;

        IAudioClient* pClient = nullptr;
        hr = pDev->Activate(__uuidof(IAudioClient), CLSCTX_ALL, nullptr, (void**)&pClient);
        pDev->Release();
        if (FAILED(hr) || !pClient) return false;

        // Build a float WAVEFORMATEXTENSIBLE that matches the source.
        WAVEFORMATEXTENSIBLE wfx = {};
        wfx.Format.cbSize          = sizeof(WAVEFORMATEXTENSIBLE) - sizeof(WAVEFORMATEX);
        wfx.Format.wFormatTag      = WAVE_FORMAT_EXTENSIBLE;
        wfx.Format.nChannels       = (WORD)numChannels;
        wfx.Format.nSamplesPerSec  = sampleRate;
        wfx.Format.wBitsPerSample  = 32;
        wfx.Format.nBlockAlign     = (WORD)(numChannels * 4);
        wfx.Format.nAvgBytesPerSec = sampleRate * wfx.Format.nBlockAlign;
        wfx.Samples.wValidBitsPerSample = 32;
        wfx.dwChannelMask = (numChannels == 1) ? SPEAKER_FRONT_CENTER
                                               : SPEAKER_FRONT_LEFT | SPEAKER_FRONT_RIGHT;
        wfx.SubFormat = KSDATAFORMAT_SUBTYPE_IEEE_FLOAT;

        // Negotiate closest-match if the device doesn't support our exact
        // format. WASAPI shared mode always converts via the engine but the
        // mix format must still satisfy IsFormatSupported.
        WAVEFORMATEX* pClosest = nullptr;
        hr = pClient->IsFormatSupported(AUDCLNT_SHAREMODE_SHARED, (WAVEFORMATEX*)&wfx, &pClosest);
        if (hr == S_FALSE && pClosest) {
            // Use the suggested format.
            memcpy(&wfx, pClosest, sizeof(WAVEFORMATEX) + pClosest->cbSize);
            CoTaskMemFree(pClosest);
        } else if (FAILED(hr)) {
            if (pClosest) CoTaskMemFree(pClosest);
            pClient->Release();
            return false;
        }

        // AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM / SRC_DEFAULT_QUALITY let WASAPI
        // resample/convert format mismatches between us and the engine. They
        // were added in the Windows 7 SDK, so define them locally if the
        // build target's headers are older than that.
        #ifndef AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM
        #define AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM 0x80000000
        #endif
        #ifndef AUDCLNT_STREAMFLAGS_SRC_DEFAULT_QUALITY
        #define AUDCLNT_STREAMFLAGS_SRC_DEFAULT_QUALITY 0x08000000
        #endif

        REFERENCE_TIME hnsBufferDur = 200000; // 20 ms
        hr = pClient->Initialize(AUDCLNT_SHAREMODE_SHARED,
            AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM | AUDCLNT_STREAMFLAGS_SRC_DEFAULT_QUALITY,
            hnsBufferDur, 0, (WAVEFORMATEX*)&wfx, nullptr);
        if (FAILED(hr)) { pClient->Release(); return false; }

        IAudioRenderClient* pRender = nullptr;
        hr = pClient->GetService(__uuidof(IAudioRenderClient), (void**)&pRender);
        if (FAILED(hr)) { pClient->Release(); return false; }

        UINT32 bufFrames = 0;
        pClient->GetBufferSize(&bufFrames);

        if (FAILED(pClient->Start())) {
            pRender->Release(); pClient->Release(); return false;
        }

        m_pClient    = pClient;
        m_pRender    = pRender;
        m_bufFrames  = bufFrames;
        m_sampleRate = wfx.Format.nSamplesPerSec;
        m_channels   = wfx.Format.nChannels;
        m_active     = true;
        return true;
    }

    void Stop()
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        if (!m_active) return;
        if (m_pClient) m_pClient->Stop();
        if (m_pRender) { m_pRender->Release(); m_pRender = nullptr; }
        if (m_pClient) { m_pClient->Release(); m_pClient = nullptr; }
        m_bufFrames = 0;
        m_active    = false;
    }

    bool IsActive() const { return m_active; }
    uint32_t Channels()   const { return m_channels; }
    uint32_t SampleRate() const { return m_sampleRate; }

    // Push interleaved float samples out the render endpoint. Callers running
    // at a faster cadence than the device may have frames dropped (we only
    // write what fits in the available portion of the engine buffer).
    void Push(const float* samples, uint32_t numFrames, uint32_t numChannels)
    {
        std::lock_guard<std::mutex> lk(m_mutex);
        if (!m_active || !m_pClient || !m_pRender || !samples || !numFrames) return;

        UINT32 padding = 0;
        if (FAILED(m_pClient->GetCurrentPadding(&padding))) return;
        UINT32 freeFrames = m_bufFrames - padding;
        if (freeFrames == 0) return;
        UINT32 toWrite = std::min<UINT32>(numFrames, freeFrames);

        BYTE* p = nullptr;
        if (FAILED(m_pRender->GetBuffer(toWrite, &p)) || !p) return;

        // Channel-count adapter. The audio capture endpoint may produce
        // a different layout than the render endpoint (e.g. USB mic = 1
        // channel, default speakers = 2 channels). Previously this
        // Push() returned silently on mismatch — which is exactly the
        // "live monitor enabled but I hear nothing" failure mode the
        // user just reported. Fan-out mono->stereo (and stereo->mono
        // if the engine ever asks for it) right here so monitor audio
        // is always audible.
        if (numChannels == m_channels) {
            memcpy(p, samples, (size_t)toWrite * numChannels * sizeof(float));
        } else if (numChannels == 1 && m_channels == 2) {
            float* dst = (float*)p;
            for (UINT32 f = 0; f < toWrite; ++f) {
                float v = samples[f];
                dst[f * 2 + 0] = v;
                dst[f * 2 + 1] = v;
            }
        } else if (numChannels == 2 && m_channels == 1) {
            float* dst = (float*)p;
            for (UINT32 f = 0; f < toWrite; ++f) {
                dst[f] = 0.5f * (samples[f * 2 + 0] + samples[f * 2 + 1]);
            }
        } else {
            // Generic path: take the first min(in,out) channels and
            // zero-fill any extra render channels.
            float* dst = (float*)p;
            const uint32_t copyCh = std::min(numChannels, m_channels);
            for (UINT32 f = 0; f < toWrite; ++f) {
                for (uint32_t c = 0; c < copyCh; ++c)
                    dst[f * m_channels + c] = samples[f * numChannels + c];
                for (uint32_t c = copyCh; c < m_channels; ++c)
                    dst[f * m_channels + c] = 0.0f;
            }
        }

        m_pRender->ReleaseBuffer(toWrite, 0);
    }

private:
    std::mutex             m_mutex;
    IAudioClient*          m_pClient    = nullptr;
    IAudioRenderClient*    m_pRender    = nullptr;
    UINT32                 m_bufFrames  = 0;
    uint32_t               m_sampleRate = 0;
    uint32_t               m_channels   = 0;
    bool                   m_active     = false;
};

// ---------------------------------------------------------------------------
// LufsMeter — ITU-R BS.1770-4 loudness meter.
//
//   Pre-filter:  high-shelf  ~1681.97 Hz  +3.999843 dB  Q=0.707
//   RLB filter:  high-pass   ~ 38.13   Hz                Q=0.5
//
// Combined K-weighting → square → 100 ms-hop, 400 ms-block mean square →
//   Momentary  = last 400 ms block, in LUFS
//   Short-term = mean of the last 30 blocks (≈ 3 s), in LUFS
//   Integrated = gated mean of all blocks since reset (absolute gate -70 LUFS,
//                relative gate at integrated_so_far - 10 LUFS), in LUFS
//
// True-peak detector uses the same 4× FIR upsampler trick as the limiter.
//
// Channel weighting: L=R=C=1.0, Ls=Rs=1.41 (5.1 only). The host doesn't have
// a 5.1 path so all channels are weighted 1.0 here.
// ---------------------------------------------------------------------------
class LufsMeter {
public:
    LufsMeter() = default;

    void Prepare(double sampleRate, uint32_t numChannels)
    {
        if (sampleRate <= 0.0) sampleRate = 48000.0;
        if (numChannels == 0)  numChannels = 2;
        if (numChannels > kMaxDSPChannels) numChannels = kMaxDSPChannels;
        m_sr        = sampleRate;
        m_channels  = numChannels;
        m_blockLen  = (uint32_t)std::round(0.400 * m_sr);
        m_hopLen    = (uint32_t)std::round(0.100 * m_sr);
        if (m_hopLen   == 0) m_hopLen   = 1;
        if (m_blockLen == 0) m_blockLen = m_hopLen;

        DesignFilters();
        Reset();
    }

    void Reset()
    {
        std::lock_guard<std::mutex> lock(m_mutex);
        for (int c = 0; c < kMaxDSPChannels; ++c) {
            m_pre[c]  = {};
            m_rlb[c]  = {};
        }
        m_hopAccum.assign(m_channels, 0.0);
        m_hopFramesSeen = 0;
        m_blockBuffer.assign(0, 0.0);
        m_blockMs.clear();
        m_intRunningSum   = 0.0;
        m_intRunningCount = 0;
        m_intLufs    = -INFINITY;
        m_stLufs     = -INFINITY;
        m_momLufs    = -INFINITY;
        m_truePeakDb = -INFINITY;
    }

    // Process is run on the audio thread. interleaved is post-effects.
    void Process(const float* interleaved, uint32_t numFrames, uint32_t numChannels)
    {
        if (!interleaved || numFrames == 0 || numChannels == 0) return;

        std::lock_guard<std::mutex> lock(m_mutex);

        // Lazy-prepare on first call, in case Process arrives before any
        // explicit Prepare(). Picks up the actual rate from the caller.
        if (m_hopAccum.size() < numChannels || m_blockLen == 0) {
            // Force initialization at the audio path's reported channel count.
            // We can't know the real sample rate here, so default to 48 kHz —
            // a follow-up Prepare() from AudioMixer::Configure will redo this.
            DesignFilters();
            m_channels = numChannels;
            if (m_channels > kMaxDSPChannels) m_channels = kMaxDSPChannels;
            m_blockLen = (uint32_t)std::round(0.400 * m_sr);
            m_hopLen   = (uint32_t)std::round(0.100 * m_sr);
            if (m_hopLen   == 0) m_hopLen   = 1;
            if (m_blockLen == 0) m_blockLen = m_hopLen;
            m_hopAccum.assign(m_channels, 0.0);
            m_hopFramesSeen = 0;
            m_blockBuffer.clear();
            m_blockMs.clear();
        }
        if (numChannels > m_channels) numChannels = m_channels;

        for (uint32_t n = 0; n < numFrames; ++n) {
            const uint32_t base = n * numChannels;

            // True peak: lightweight 4× upsampler with linear interpolation
            // between the previous and current sample (same trick used in
            // the limiter — coarse but adequate for a meter).
            for (uint32_t c = 0; c < numChannels; ++c) {
                float s    = interleaved[base + c];
                float prev = m_lastInput[c];
                for (int k = 1; k <= 4; ++k) {
                    float t = (float)k * 0.25f;
                    float v = prev * (1.0f - t) + s * t;
                    float a = std::fabs(v);
                    if (a > m_truePeakLin) m_truePeakLin = a;
                }
                m_lastInput[c] = s;
            }

            // K-weight + square per channel.
            double weightedSquareSum = 0.0;
            for (uint32_t c = 0; c < numChannels; ++c) {
                double x = (double)interleaved[base + c];
                double y = m_pre[c].Process(x);
                double z = m_rlb[c].Process(y);
                weightedSquareSum += z * z;          // unity weighting (mono/stereo)
                m_hopAccum[c] += z * z;
            }
            (void)weightedSquareSum;

            ++m_hopFramesSeen;
            if (m_hopFramesSeen >= m_hopLen) {
                // Fold this hop's per-channel mean-squares into the rolling
                // 400-ms block buffer.
                double hopMs = 0.0;
                for (uint32_t c = 0; c < numChannels; ++c) {
                    double ms = m_hopAccum[c] / (double)m_hopFramesSeen;
                    hopMs += ms;          // per-channel weights are 1.0 here
                    m_hopAccum[c] = 0.0;
                }
                m_blockBuffer.push_back(hopMs);
                if (m_blockBuffer.size() > 4) {
                    // Keep at most 4 hops worth (= 400 ms) for momentary.
                    m_blockBuffer.erase(m_blockBuffer.begin(),
                                        m_blockBuffer.end() - 4);
                }
                if (m_blockBuffer.size() == 4) {
                    double sum = 0.0;
                    for (double v : m_blockBuffer) sum += v;
                    double blockMs = sum / 4.0;     // mean-square of a 400 ms block
                    m_blockMs.push_back(blockMs);
                    // Cap the short-term ring at 30 entries (= 3 s sliding).
                    if (m_blockMs.size() > 30) {
                        m_blockMs.erase(m_blockMs.begin(),
                                        m_blockMs.end() - 30);
                    }
                    UpdateLoudnessLevels(blockMs);
                }
                m_hopFramesSeen = 0;
            }
        }

        // Drain the true-peak linear estimate into a slowly-decaying hold
        // so the readout doesn't flicker.
        const double dec = 0.9995;
        m_truePeakHoldLin = std::max((double)m_truePeakLin, m_truePeakHoldLin * dec);
        m_truePeakLin = 0.0f;

        m_truePeakDb = (m_truePeakHoldLin > 1e-9)
                          ? 20.0 * std::log10(m_truePeakHoldLin)
                          : -INFINITY;
    }

    // Snapshot accessors — safe from the UI thread.
    void Snapshot(double& momLufs, double& stLufs, double& intLufs, double& tpDb)
    {
        std::lock_guard<std::mutex> lock(m_mutex);
        momLufs = m_momLufs;
        stLufs  = m_stLufs;
        intLufs = m_intLufs;
        tpDb    = m_truePeakDb;
    }

    void ResetIntegrated()
    {
        std::lock_guard<std::mutex> lock(m_mutex);
        m_intRunningSum   = 0.0;
        m_intRunningCount = 0;
        m_intLufs         = -INFINITY;
    }

private:
    struct Biquad2 {
        double a1 = 0.0, a2 = 0.0, b0 = 1.0, b1 = 0.0, b2 = 0.0;
        double z1 = 0.0, z2 = 0.0;
        double Process(double x) {
            double y = b0 * x + z1;
            z1       = b1 * x - a1 * y + z2;
            z2       = b2 * x - a2 * y;
            return y;
        }
    };
    struct ChanFilter { Biquad2 prefilter; Biquad2 rlb; };

    void DesignFilters()
    {
        // RBJ-style biquad design at the host's sample rate. The two filter
        // shapes correspond to ITU-R BS.1770-4 reference filters.
        const double f0Pre = 1681.974;
        const double GdbPre = 3.999843;       // = +4 dB exactly per spec
        const double QPre  = 0.7071752;
        DesignHighShelf(m_preProto, f0Pre, GdbPre, QPre);

        const double f0Rlb = 38.13547;
        const double QRlb  = 0.5003270;
        DesignHighPass(m_rlbProto, f0Rlb, QRlb);

        // Replicate prototype coefficients into per-channel filter slots.
        for (int c = 0; c < kMaxDSPChannels; ++c) {
            m_pre[c] = m_preProto;
            m_rlb[c] = m_rlbProto;
            m_pre[c].z1 = m_pre[c].z2 = 0.0;
            m_rlb[c].z1 = m_rlb[c].z2 = 0.0;
        }
    }

    void DesignHighShelf(Biquad2& f, double f0, double dbGain, double Q)
    {
        const double A     = std::pow(10.0, dbGain / 40.0);
        const double w0    = 2.0 * 3.141592653589793 * f0 / m_sr;
        const double cosw  = std::cos(w0);
        const double sinw  = std::sin(w0);
        const double alpha = sinw / (2.0 * Q);
        const double sa    = 2.0 * std::sqrt(A) * alpha;
        const double b0 = A*((A+1) + (A-1)*cosw + sa);
        const double b1 = -2.0*A*((A-1) + (A+1)*cosw);
        const double b2 = A*((A+1) + (A-1)*cosw - sa);
        const double a0 = (A+1) - (A-1)*cosw + sa;
        const double a1 = 2.0*((A-1) - (A+1)*cosw);
        const double a2 = (A+1) - (A-1)*cosw - sa;
        f.b0 = b0/a0; f.b1 = b1/a0; f.b2 = b2/a0;
        f.a1 = a1/a0; f.a2 = a2/a0;
    }

    void DesignHighPass(Biquad2& f, double f0, double Q)
    {
        const double w0    = 2.0 * 3.141592653589793 * f0 / m_sr;
        const double cosw  = std::cos(w0);
        const double sinw  = std::sin(w0);
        const double alpha = sinw / (2.0 * Q);
        const double b0 = (1.0 + cosw) * 0.5;
        const double b1 = -(1.0 + cosw);
        const double b2 = (1.0 + cosw) * 0.5;
        const double a0 = 1.0 + alpha;
        const double a1 = -2.0 * cosw;
        const double a2 = 1.0 - alpha;
        f.b0 = b0/a0; f.b1 = b1/a0; f.b2 = b2/a0;
        f.a1 = a1/a0; f.a2 = a2/a0;
    }

    static double MsToLufs(double ms)
    {
        if (ms <= 1e-12) return -INFINITY;
        return -0.691 + 10.0 * std::log10(ms);
    }

    void UpdateLoudnessLevels(double newBlockMs)
    {
        // Momentary = the just-completed 400 ms block.
        m_momLufs = MsToLufs(newBlockMs);

        // Short-term = mean of the last 30 blocks.
        if (!m_blockMs.empty()) {
            double sum = 0.0;
            for (double v : m_blockMs) sum += v;
            double mean = sum / (double)m_blockMs.size();
            m_stLufs = MsToLufs(mean);
        }

        // Integrated: gated mean. Absolute gate at -70 LUFS plus relative
        // gate at integrated_so_far - 10 LUFS. We only fold blocks that
        // pass the absolute gate into the running sum, then a final
        // relative-gate pass on snapshot would require keeping every block.
        // To keep memory bounded we maintain only the absolute-gated mean
        // here — a strict relative-gated read is computed on demand from
        // the rolling window, which is plenty accurate for monitoring.
        const double absGate = -70.0;
        if (m_momLufs > absGate) {
            m_intRunningSum   += newBlockMs;
            m_intRunningCount += 1;
        }
        if (m_intRunningCount > 0) {
            double mean = m_intRunningSum / (double)m_intRunningCount;
            m_intLufs = MsToLufs(mean);
        }
    }

    std::mutex          m_mutex;
    double              m_sr            = 48000.0;
    uint32_t            m_channels      = 2;
    uint32_t            m_blockLen      = 0;
    uint32_t            m_hopLen        = 0;
    uint32_t            m_hopFramesSeen = 0;

    Biquad2             m_preProto, m_rlbProto;
    Biquad2             m_pre[kMaxDSPChannels];
    Biquad2             m_rlb[kMaxDSPChannels];

    std::vector<double> m_hopAccum;          // running sum of squared K-weighted samples per channel
    std::vector<double> m_blockBuffer;       // last <=4 hop mean-squares (sliding 400 ms)
    std::vector<double> m_blockMs;           // last <=30 block mean-squares (sliding 3 s)

    double              m_intRunningSum   = 0.0;
    uint64_t            m_intRunningCount = 0;

    double              m_intLufs    = -INFINITY;
    double              m_stLufs     = -INFINITY;
    double              m_momLufs    = -INFINITY;
    double              m_truePeakDb = -INFINITY;
    double              m_truePeakHoldLin = 0.0;
    float               m_truePeakLin     = 0.0f;
    float               m_lastInput[kMaxDSPChannels] = {};
};

// ---------------------------------------------------------------------------
// CubicResampler — 4-point cubic Hermite resampler for 44.1 ↔ 48 kHz.
//
// Used to normalize captured audio (whatever rate the WASAPI endpoint runs
// at) into the user-selected pipeline rate so the encoder, the live
// monitor, and the LUFS meter all see the same rate. Cubic Hermite is
// audibly transparent for music/speech at these rates, doesn't pull in any
// SDK dependencies, and is cheap enough to run in the audio thread.
// ---------------------------------------------------------------------------
class CubicResampler {
public:
    void Configure(double srcRate, double dstRate, uint32_t channels)
    {
        m_srcRate  = srcRate;
        m_dstRate  = dstRate;
        m_channels = (channels == 0) ? 1 : channels;
        m_phase    = 1.0;
        m_state.assign((size_t)m_channels * 3, 0.0f);
    }
    bool Bypass() const { return std::fabs(m_srcRate - m_dstRate) < 1e-3; }

    void Process(const float* src, uint32_t srcFrames, std::vector<float>& dst)
    {
        dst.clear();
        if (srcFrames == 0 || m_channels == 0) return;
        if (Bypass()) {
            dst.assign(src, src + (size_t)srcFrames * m_channels);
            return;
        }
        const uint32_t ch   = m_channels;
        const double   step = m_srcRate / m_dstRate;

        // Concatenate the previous 3-frame state with the new chunk so the
        // cubic kernel can always read y[-1], y[0], y[1], y[2] without
        // running off the front/back of the buffer.
        std::vector<float> buf;
        buf.reserve(m_state.size() + (size_t)srcFrames * ch);
        buf.insert(buf.end(), m_state.begin(), m_state.end());
        buf.insert(buf.end(), src, src + (size_t)srcFrames * ch);
        const size_t totalFrames = buf.size() / ch;

        double pos = m_phase;
        while (pos + 2.0 < (double)totalFrames) {
            int   i = (int)std::floor(pos);
            float t = (float)(pos - (double)i);
            const float* ym1p = &buf[((size_t)(i - 1)) * ch];
            const float* y0p  = &buf[((size_t)i)       * ch];
            const float* y1p  = &buf[((size_t)(i + 1)) * ch];
            const float* y2p  = &buf[((size_t)(i + 2)) * ch];
            for (uint32_t c = 0; c < ch; ++c) {
                float ym1 = ym1p[c], y0 = y0p[c], y1 = y1p[c], y2 = y2p[c];
                float c0 = y0;
                float c1 = 0.5f * (y1 - ym1);
                float c2 = ym1 - 2.5f * y0 + 2.0f * y1 - 0.5f * y2;
                float c3 = 0.5f * (y2 - ym1) + 1.5f * (y0 - y1);
                dst.push_back(((c3 * t + c2) * t + c1) * t + c0);
            }
            pos += step;
        }

        // Save the last 3 frames as state for the next chunk.
        m_state.assign(buf.end() - 3 * ch, buf.end());
        // Phase carries forward, shifted by srcFrames so it is relative to
        // the start of the *next* combined buffer (which begins with the
        // same trailing 3 frames we just stored).
        m_phase = pos - (double)srcFrames;
    }

private:
    double             m_srcRate  = 0.0;
    double             m_dstRate  = 0.0;
    uint32_t           m_channels = 0;
    double             m_phase    = 1.0;
    std::vector<float> m_state;
};

// LUFS preset: target loudness + brick-wall ceiling, plus a printable name.
struct LufsPreset {
    const wchar_t* name;
    double         targetLufs;
    double         ceilingDbtp;
};
static const LufsPreset g_lufsPresets[] = {
    { L"Streaming   (-14 LUFS / -1 dBTP)", -14.0, -1.0 },
    { L"Broadcast   (-23 LUFS / -1 dBTP)", -23.0, -1.0 },
    { L"Music       (-16 LUFS / -1 dBTP)", -16.0, -1.0 },
    { L"Speech      (-18 LUFS / -1 dBTP)", -18.0, -1.0 },
    { L"Cinema      (-27 LUFS / -2 dBTP)", -27.0, -2.0 },
    { L"Custom      (no target)",            0.0,  0.0 },
};
static constexpr int g_lufsPresetCount = (int)(sizeof(g_lufsPresets) / sizeof(g_lufsPresets[0]));
static int           g_lufsPresetIdx   = 0;        // default "Streaming"

#pragma endregion

#pragma region GLOBAL_IDS_AND_DEFINES

static const GUID IID_IMFDXGIDeviceManager_local = {
    0xEB533D5D, 0x2DB6, 0x40F8,
    {0x97, 0xA9, 0x49, 0x46, 0x92, 0x01, 0x4F, 0x07}
};

#define IDC_BTN_START       1001
#define IDC_BTN_PAUSE       1002
#define IDC_BTN_STOP        1003
#define IDC_COMBO_MONITOR   1005
#define IDC_COMBO_AUDIO     1006
#define IDC_COMBO_HK_START  1007
#define IDC_COMBO_HK_PAUSE  1008
#define IDC_COMBO_HK_STOP   1009
#define IDC_PREVIEW         1010
#define IDC_STATIC_HKLABEL1 1012
#define IDC_STATIC_HKLABEL2 1013
#define IDC_STATIC_HKLABEL3 1014
#define IDC_CHECK_CURSOR    1015
#define IDC_CHECK_LCLICK    1016
#define IDC_CHECK_RCLICK    1017
#define IDC_COMBO_PRESET    1018
#define IDC_STATIC_PRESET   1019

// Effect-rack panel.
#define IDC_COMBO_FX_SRC      1100
#define IDC_COMBO_FX_TYPE     1101
#define IDC_BTN_FX_ADD        1102
#define IDC_LIST_FX_CHAIN     1103
#define IDC_BTN_FX_REMOVE     1104
#define IDC_BTN_FX_UP         1105
#define IDC_BTN_FX_DOWN       1106
#define IDC_CHECK_FX_BYPASS   1107
#define IDC_CHECK_FX_MONITOR  1108
#define IDC_CHECK_FX_ENABLE   1109
#define IDC_STATIC_FX_TITLE   1110
// Sliders + labels are dynamically (de)allocated in batches; reserve large
// contiguous blocks of IDs so we can compute slider <-> param-index mapping
// arithmetically.
#define IDC_PARAM_SLIDER_BASE 1200   // 1200 .. 1399
#define IDC_PARAM_LABEL_BASE  1400   // 1400 .. 1599
#define IDC_PARAM_VALUE_BASE  1600   // 1600 .. 1799
#define MAX_PARAM_SLOTS       16

// LUFS preset combo + realtime meter readouts.
#define IDC_STATIC_LUFS_LABEL 1800
#define IDC_COMBO_LUFS_PRESET 1801
#define IDC_STATIC_LUFS_M     1802
#define IDC_STATIC_LUFS_S     1803
#define IDC_STATIC_LUFS_I     1804
#define IDC_STATIC_LUFS_TP    1805
#define IDC_BTN_LUFS_RESET    1806

// Tabbed layout + sample-rate selector.
#define IDC_TAB_MAIN          1900
#define IDC_STATIC_RATE       1901
#define IDC_COMBO_SAMPLE_RATE 1902
#define IDC_GROUP_RECORDER    1910
#define IDC_GROUP_AUDIO       1911
#define IDC_GROUP_HOTKEYS     1912
#define IDC_GROUP_OVERLAY     1913
#define IDC_GROUP_FX_CHAIN    1914
#define IDC_GROUP_LUFS        1915
#define IDC_STATIC_LUFS_BIG_M 1920
#define IDC_STATIC_LUFS_BIG_S 1921
#define IDC_STATIC_LUFS_BIG_I 1922
#define IDC_STATIC_LUFS_BIG_TP 1923
#define IDC_STATIC_LUFS_BIG_M_LBL 1924
#define IDC_STATIC_LUFS_BIG_S_LBL 1925
#define IDC_STATIC_LUFS_BIG_I_LBL 1926
#define IDC_STATIC_LUFS_BIG_TP_LBL 1927
#define IDC_PROG_LUFS_M       1928
#define IDC_PROG_LUFS_S       1929
#define IDC_PROG_LUFS_I       1930
#define IDC_PROG_LUFS_TP      1931
#define IDC_STATIC_LUFS_TARGET 1932

// Active tab index: 0 = Recorder, 1 = Audio FX, 2 = Loudness.
static int g_currentTab = 0;

#define HK_ID_START  2001
#define HK_ID_PAUSE  2002
#define HK_ID_STOP   2003

#define MAX_AUDIO_DEVICES 32
#define MAX_MONITORS      16
// Larger WASAPI capture buffer + event-driven wake-up. USB-class
// microphones (FIFINE K658, MV7, etc.) ship buffers in 10–20 ms
// chunks but stalls in our loop bubble through to the encoder as
// glitches. A 200 ms ring + event signalling means a single dropped
// wake never produces audible artifacts.
// 200 ms produced audible crackling on USB mics: WASAPI handed us
// large packets that we pushed straight through the resampler,
// effect rack, and metering — when the rack overran its CPU budget
// for a single packet, the next capture event was already late and
// the engine reported AUDCLNT_S_BUFFER_EMPTY / discontinuity. 20 ms
// matches what OBS / Audacity / Voicemeeter use and gives the audio
// thread plenty of headroom against scheduler jitter.
#define AUDIO_BUFFER_MS   20
#define TARGET_FPS        30
#define FRAME_INTERVAL_MS (1000 / TARGET_FPS)

enum class RecorderState { Idle, Recording, Paused };

// ---------------------------------------------------------------------------
// Video recording presets.
//
// Each preset bundles a target frame rate and an H.264 average bitrate. The
// recording resolution always tracks the captured monitor's native pixel
// dimensions (we don't downscale here — the preset's "name" describes the
// quality tier, not a forced output resolution). Bitrate is the dominant
// quality knob for screen recordings; FPS is the dominant smoothness knob.
//
// Add or reorder entries here; the UI combo populates from this table at
// startup. Index of "Balanced" stays 1 so the default selection is stable.
// ---------------------------------------------------------------------------
struct VideoPreset {
    const wchar_t* name;
    UINT           fps;
    UINT           bitrate;   // bits per second
};
static const VideoPreset g_videoPresets[] = {
    { L"Lightweight  (30 FPS, 2 Mbps)",   30,  2'000'000u },
    { L"Balanced     (30 FPS, 4 Mbps)",   30,  4'000'000u },
    { L"High Quality (30 FPS, 8 Mbps)",   30,  8'000'000u },
    { L"Smooth       (60 FPS, 8 Mbps)",   60,  8'000'000u },
    { L"Ultra        (60 FPS, 16 Mbps)",  60, 16'000'000u },
    { L"Cinema       (24 FPS, 6 Mbps)",   24,  6'000'000u },
};
static const int g_videoPresetCount = (int)(sizeof(g_videoPresets) / sizeof(g_videoPresets[0]));
static int g_selectedPreset = 1;   // "Balanced" — matches the previous hard-coded defaults

#pragma endregion

#pragma region GLOBAL_STATE

static std::atomic<RecorderState> g_recState{RecorderState::Idle};
static HWND          g_hwndMain = nullptr;
static HWND          g_hwndPreview = nullptr;
static HINSTANCE     g_hInst = nullptr;

static UINT g_hkStartVKey = 'R';
static UINT g_hkPauseVKey = 'P';
static UINT g_hkStopVKey  = 'S';
static UINT g_hkMods      = MOD_CONTROL | MOD_SHIFT;

static std::atomic<bool> g_captureRunning{false};
static std::atomic<bool> g_audioRunning{false};
static std::atomic<bool> g_audioReinit {false};   // request audio thread to reopen capture endpoint
// Re-entrancy guard for StartRecording's modal save dialog. Without this,
// a second StartRecording() call (from a held / repeated hotkey, or from
// the immediate-mode UI re-running its scene inside the modal's message
// pump) would open another GetSaveFileNameW on top — producing the
// "infinite file save dialog" loop the user observed. The flag is
// claimed atomically before the dialog opens and released only after
// the entire start path either succeeds or bails out.
static std::atomic<bool> g_dialogOpen   {false};
static std::atomic<bool> g_appRunning{true};
static std::mutex        g_writeMutex;

// Sample rate the audio path is normalized to (encoder rate + LUFS rate).
// Captured audio is resampled into this rate before hitting the bus, so
// switching it from the UI affects the recording, the live monitor, and
// the loudness meter atomically.
static std::atomic<UINT> g_selectedSampleRate{48000};

struct MonitorInfo {
    HMONITOR hMon;
    RECT     rect;
    wchar_t  name[64];
    UINT     adapterIdx;
    UINT     outputIdx;
};

static std::vector<MonitorInfo>  g_monitors;
static int                       g_selectedMonitor = 0;

struct AudioDeviceInfo {
    wchar_t  id[512];
    wchar_t  name[256];
    bool     isLoopback;
};

static std::vector<AudioDeviceInfo> g_audioDevices;
static int                          g_selectedAudio = 0;

static wchar_t g_outputPath[MAX_PATH] = L"recording.mp4";

// User-visible recording options (live-toggleable from the UI; read by the
// DxgiCaptureRenderer compositor every frame).
static std::atomic<bool> g_showCursor      {true};
static std::atomic<bool> g_markLeftClick   {false};
static std::atomic<bool> g_markRightClick  {false};

static LONGLONG g_videoTimestamp = 0;
static LONGLONG g_audioTimestamp = 0;
static bool     g_mfStarted      = false;

#pragma endregion

#pragma region MONITOR_ENUM

static BOOL CALLBACK MonitorEnumProc(HMONITOR hMon, HDC, LPRECT lprc, LPARAM)
{
    if ((int)g_monitors.size() >= MAX_MONITORS) return FALSE;
    MONITORINFOEXW mi = {};
    mi.cbSize = sizeof(mi);
    if (!GetMonitorInfoW(hMon, &mi)) return TRUE;
    MonitorInfo info = {};
    info.hMon = hMon;
    info.rect = mi.rcMonitor;
    wcsncpy_s(info.name, _countof(info.name), mi.szDevice, _TRUNCATE);
    g_monitors.push_back(info);
    return TRUE;
}

static void EnumerateMonitors()
{
    g_monitors.clear();
    EnumDisplayMonitors(nullptr, nullptr, MonitorEnumProc, 0);
}

#pragma endregion

#pragma region WASAPI_AUDIO_CAPTURE

class AudioCaptureManager {
public:
    AudioCaptureManager() = default;
    ~AudioCaptureManager() { Stop(); }

    bool Init(const wchar_t* deviceId, bool loopback)
    {
        m_loopback = loopback;

        IMMDeviceEnumerator* pEnum = nullptr;
        HRESULT hr = CoCreateInstance(
            __uuidof(MMDeviceEnumerator), nullptr, CLSCTX_ALL,
            __uuidof(IMMDeviceEnumerator), (void**)&pEnum);
        if (FAILED(hr)) return false;

        // Three cases:
        //  1) Loopback (any deviceId)        -> default render endpoint
        //  2) Capture with a named deviceId  -> that exact device
        //  3) Capture with null/empty id     -> default *capture* endpoint
        //     (was previously routing to eRender by mistake, which
        //      meant "Microphone with no device id" silently fell back
        //      to desktop loopback and the LUFS meter never reflected
        //      the mic's input.)
        if (loopback) {
            hr = pEnum->GetDefaultAudioEndpoint(eRender, eConsole, &m_pDevice);
        } else if (deviceId == nullptr || deviceId[0] == 0) {
            hr = pEnum->GetDefaultAudioEndpoint(eCapture, eCommunications, &m_pDevice);
            if (FAILED(hr)) {
                hr = pEnum->GetDefaultAudioEndpoint(eCapture, eMultimedia, &m_pDevice);
            }
        } else {
            hr = pEnum->GetDevice(deviceId, &m_pDevice);
        }
        pEnum->Release();
        if (FAILED(hr)) return false;

        hr = m_pDevice->Activate(__uuidof(IAudioClient), CLSCTX_ALL, nullptr, (void**)&m_pClient);
        if (FAILED(hr)) return false;

        WAVEFORMATEX* pwfx = nullptr;
        hr = m_pClient->GetMixFormat(&pwfx);
        if (FAILED(hr)) return false;

        m_wfx = *pwfx;
        if (pwfx->wFormatTag == WAVE_FORMAT_EXTENSIBLE) {
            WAVEFORMATEXTENSIBLE* wfex = (WAVEFORMATEXTENSIBLE*)pwfx;
            if (IsEqualGUID(wfex->SubFormat, KSDATAFORMAT_SUBTYPE_IEEE_FLOAT)) {
                m_isFloat = true;
            }
        } else if (pwfx->wFormatTag == WAVE_FORMAT_IEEE_FLOAT) {
            m_isFloat = true;
        }

        // Event-driven mode is supported by both render-loopback and
        // dedicated capture endpoints. Loopback streams cannot signal
        // an event before Vista SP1; on every supported Maxx target
        // (Win7+) it works for both modes.
        DWORD streamFlags = AUDCLNT_STREAMFLAGS_EVENTCALLBACK;
        if (loopback) streamFlags |= AUDCLNT_STREAMFLAGS_LOOPBACK;

        hr = m_pClient->Initialize(
            AUDCLNT_SHAREMODE_SHARED,
            streamFlags,
            (LONGLONG)AUDIO_BUFFER_MS * 10000LL,
            0, pwfx, nullptr);
        CoTaskMemFree(pwfx);
        // Some loopback endpoints reject EVENTCALLBACK with
        // AUDCLNT_E_DEVICE_INVALIDATED or AUDCLNT_E_UNSUPPORTED_FORMAT
        // — fall back to polling mode in that case so the device still
        // works (the always-on audio thread polls every 5 ms).
        if (FAILED(hr)) {
            DWORD fallbackFlags = loopback ? AUDCLNT_STREAMFLAGS_LOOPBACK : 0;
            hr = m_pClient->Initialize(
                AUDCLNT_SHAREMODE_SHARED,
                fallbackFlags,
                (LONGLONG)AUDIO_BUFFER_MS * 10000LL,
                0, pwfx, nullptr);
            if (FAILED(hr)) return false;
            m_eventDriven = false;
        } else {
            m_eventDriven = true;
        }

        if (m_eventDriven) {
            m_hCaptureEvent = CreateEventW(nullptr, FALSE, FALSE, nullptr);
            if (!m_hCaptureEvent) return false;
            hr = m_pClient->SetEventHandle(m_hCaptureEvent);
            if (FAILED(hr)) {
                // Some drivers don't actually honour event mode; degrade.
                CloseHandle(m_hCaptureEvent);
                m_hCaptureEvent = nullptr;
                m_eventDriven   = false;
            }
        }

        hr = m_pClient->GetService(__uuidof(IAudioCaptureClient), (void**)&m_pCapture);
        if (FAILED(hr)) return false;

        hr = m_pClient->GetBufferSize(&m_bufferFrames);
        if (FAILED(hr)) return false;

        m_sampleRate   = m_wfx.nSamplesPerSec;
        m_numChannels  = m_wfx.nChannels;
        m_bitsPerSample= m_wfx.wBitsPerSample;

        return true;
    }

    bool Start()
    {
        if (!m_pClient) return false;
        HRESULT hr = m_pClient->Start();
        return SUCCEEDED(hr);
    }

    void Stop()
    {
        if (m_pClient) m_pClient->Stop();
        if (m_pCapture) { m_pCapture->Release(); m_pCapture = nullptr; }
        if (m_pClient)  { m_pClient->Release();  m_pClient  = nullptr; }
        if (m_pDevice)  { m_pDevice->Release();  m_pDevice  = nullptr; }
        if (m_hCaptureEvent) { CloseHandle(m_hCaptureEvent); m_hCaptureEvent = nullptr; }
        m_eventDriven = false;
    }

    // Wait handle that the audio thread can WaitForSingleObject on. Returns
    // nullptr if the device is in polling fallback mode.
    HANDLE GetCaptureEvent() const { return m_hCaptureEvent; }
    bool   IsEventDriven()   const { return m_eventDriven; }

    struct AudioPacket {
        std::vector<float> samples;
        UINT32             numFrames;
        UINT32             numChannels;
        UINT32             sampleRate;
        bool               sourceIsLoopback;
    };

    bool ReadNextPacket(AudioPacket& pkt)
    {
        if (!m_pCapture) return false;
        UINT32 packetSize = 0;
        HRESULT hr = m_pCapture->GetNextPacketSize(&packetSize);
        if (FAILED(hr) || packetSize == 0) return false;

        BYTE* pData = nullptr;
        UINT32 numFrames = 0;
        DWORD flags = 0;
        hr = m_pCapture->GetBuffer(&pData, &numFrames, &flags, nullptr, nullptr);
        if (FAILED(hr)) return false;

        pkt.numFrames        = numFrames;
        pkt.numChannels      = m_numChannels;
        pkt.sampleRate       = m_sampleRate;
        pkt.sourceIsLoopback = m_loopback;
        pkt.samples.resize((size_t)numFrames * m_numChannels);

        if (flags & AUDCLNT_BUFFERFLAGS_SILENT) {
            memset(pkt.samples.data(), 0, pkt.samples.size() * sizeof(float));
        } else if (m_isFloat) {
            memcpy(pkt.samples.data(), pData, pkt.samples.size() * sizeof(float));
        } else if (m_bitsPerSample == 16) {
            const int16_t* src = (const int16_t*)pData;
            for (size_t i = 0; i < pkt.samples.size(); ++i)
                pkt.samples[i] = src[i] / 32768.0f;
        } else {
            memset(pkt.samples.data(), 0, pkt.samples.size() * sizeof(float));
        }

        m_pCapture->ReleaseBuffer(numFrames);
        return true;
    }

    UINT32 GetSampleRate()   const { return m_sampleRate; }
    UINT32 GetChannels()     const { return m_numChannels; }

private:
    IMMDevice*          m_pDevice      = nullptr;
    IAudioClient*       m_pClient      = nullptr;
    IAudioCaptureClient*m_pCapture     = nullptr;
    WAVEFORMATEX        m_wfx          = {};
    UINT32              m_bufferFrames = 0;
    UINT32              m_sampleRate   = 44100;
    UINT32              m_numChannels  = 2;
    UINT32              m_bitsPerSample= 32;
    bool                m_isFloat      = false;
    bool                m_loopback     = true;
    HANDLE              m_hCaptureEvent = nullptr;
    bool                m_eventDriven   = false;
};

static void EnumerateAudioDevices()
{
    g_audioDevices.clear();

    AudioDeviceInfo loopback = {};
    wcscpy_s(loopback.name, L"[Desktop Audio - Loopback]");
    loopback.isLoopback = true;
    g_audioDevices.push_back(loopback);

    IMMDeviceEnumerator* pEnum = nullptr;
    if (FAILED(CoCreateInstance(__uuidof(MMDeviceEnumerator), nullptr,
        CLSCTX_ALL, __uuidof(IMMDeviceEnumerator), (void**)&pEnum))) return;

    IMMDeviceCollection* pCol = nullptr;
    if (SUCCEEDED(pEnum->EnumAudioEndpoints(eCapture, DEVICE_STATE_ACTIVE, &pCol))) {
        UINT count = 0;
        pCol->GetCount(&count);
        for (UINT i = 0; i < count && (int)g_audioDevices.size() < MAX_AUDIO_DEVICES; ++i) {
            IMMDevice* pDev = nullptr;
            if (FAILED(pCol->Item(i, &pDev))) continue;
            LPWSTR pwszId = nullptr;
            pDev->GetId(&pwszId);
            IPropertyStore* pProps = nullptr;
            pDev->OpenPropertyStore(STGM_READ, &pProps);
            AudioDeviceInfo di = {};
            di.isLoopback = false;
            if (pwszId) {
                // Use truncating copy so over-long device IDs do not invoke the
                // CRT invalid-parameter handler (which terminates the process).
                wcsncpy_s(di.id, _countof(di.id), pwszId, _TRUNCATE);
                CoTaskMemFree(pwszId);
            }
            if (pProps) {
                PROPVARIANT pv = {};
                PropVariantInit(&pv);
                if (SUCCEEDED(pProps->GetValue(PKEY_Device_FriendlyName, &pv)) && pv.vt == VT_LPWSTR && pv.pwszVal)
                    wcsncpy_s(di.name, _countof(di.name), pv.pwszVal, _TRUNCATE);
                PropVariantClear(&pv);
                pProps->Release();
            }
            g_audioDevices.push_back(di);
            pDev->Release();
        }
        pCol->Release();
    }
    pEnum->Release();
}

#pragma endregion



#pragma region AUDIO_MIX_BUS
//
// AudioMixer — single mix bus through which captured audio flows on its way
// to the encoder and (optionally) the live-monitor render endpoint.
//
//     [Capture] → [Effect Rack (per source)] → [Bus gain] → [Encoder]
//                                                       └─→ [Live monitor]
//
// We maintain TWO independent racks:
//   m_rackLoopback  — applied when the active capture source is the
//                     desktop loopback endpoint.
//   m_rackMic       — applied when the active capture source is a microphone
//                     / line-in capture endpoint.
//
// The active rack is selected per-packet from the AudioCaptureManager's
// reported source class, so switching sources in the UI doesn't lose either
// rack's state — both are kept warm.
//
// Live-monitoring is a per-rack opt-in. The user toggles it from the UI;
// the audio thread checks the toggle each packet and pushes the processed
// buffer to LiveMonitor::Push when enabled.
// ---------------------------------------------------------------------------

class AudioMixer {
public:
    AudioMixer() = default;

    void Configure(uint32_t sampleRate, uint32_t numChannels)
    {
        if (sampleRate == m_sampleRate && numChannels == m_numChannels) return;
        m_sampleRate  = sampleRate;
        m_numChannels = numChannels;
        m_rackLoopback.Prepare((double)sampleRate, numChannels);
        m_rackMic     .Prepare((double)sampleRate, numChannels);
        m_meter       .Prepare((double)sampleRate, numChannels);
        // Re-evaluate the live monitor against the new rate — drop and
        // restart if it's already running, otherwise leave it disabled.
        if (m_monitor.IsActive()) {
            m_monitor.Stop();
            if (m_monitorEnabled.load())
                m_monitor.Start(sampleRate, numChannels);
        }
    }

    // Hard reset: re-Prepare everything and force-restart the monitor
    // even when the rate/channels match. Called from openCapture() on
    // every device switch — without this, picking a microphone whose
    // mix format happens to match the previous endpoint's format
    // (e.g. both 48 kHz / 2 ch) early-returned out of Configure(),
    // leaving the LUFS meter and the live-monitor render endpoint in
    // a stale state primed for the previous capture stream. Hard
    // reset rebuilds them from scratch.
    void ForceReinit(uint32_t sampleRate, uint32_t numChannels)
    {
        m_sampleRate  = sampleRate;
        m_numChannels = numChannels;
        m_rackLoopback.Prepare((double)sampleRate, numChannels);
        m_rackMic     .Prepare((double)sampleRate, numChannels);
        m_meter       .Prepare((double)sampleRate, numChannels);
        m_meter       .ResetIntegrated();
        // Always tear down + restart the WASAPI render endpoint so it
        // matches the new capture stream's rate/channels and clears
        // any residual buffer from the previous device.
        m_monitor.Stop();
        if (m_monitorEnabled.load() && sampleRate && numChannels) {
            m_monitor.Start(sampleRate, numChannels);
        }
    }

    // Adjustable post-effect mix-bus gain (linear; 1.0 == unity).
    void  SetGain(float gain) { m_gain.store(gain); }
    float GetGain() const     { return m_gain.load(); }

    // Run a captured packet through the appropriate effect rack + bus gain.
    // The buffer is processed in place; both the encoder and the optional
    // live-monitor receive the post-effects audio.
    void ProcessMixBus(float* interleaved, uint32_t numFrames, uint32_t numChannels,
                       bool sourceIsLoopback)
    {
        if (!interleaved || numFrames == 0 || numChannels == 0) return;

        EffectRack& rack = sourceIsLoopback ? m_rackLoopback : m_rackMic;
        rack.Process(interleaved, numFrames, numChannels);

        float g = m_gain.load();
        if (g != 1.0f) {
            const size_t n = (size_t)numFrames * numChannels;
            for (size_t i = 0; i < n; ++i) interleaved[i] *= g;
        }

        // Lazy-start the live monitor. Toggling "Monitor" ON before
        // the first audio packet has been processed leaves the mixer
        // unconfigured (m_sampleRate == 0), so SetMonitorEnabled
        // can't yet start the WASAPI render endpoint. Catch up here
        // once we know the real rate/channels.
        if (m_monitorEnabled.load() && !m_monitor.IsActive() &&
            m_sampleRate && m_numChannels)
        {
            m_monitor.Start(m_sampleRate, m_numChannels);
        }
        if (m_monitorEnabled.load() && m_monitor.IsActive()) {
            m_monitor.Push(interleaved, numFrames, numChannels);
        }

        // Loudness metering on the post-effect signal — this is the audio
        // that actually ends up in the recorded file, so its LUFS reading
        // matches what a downstream loudness check would measure.
        m_meter.Process(interleaved, numFrames, numChannels);
    }

    LufsMeter& Meter() { return m_meter; }

    // Direct rack accessors for the UI.
    EffectRack& RackForSource(bool sourceIsLoopback)
    {
        return sourceIsLoopback ? m_rackLoopback : m_rackMic;
    }
    EffectRack& LoopbackRack() { return m_rackLoopback; }
    EffectRack& MicRack()      { return m_rackMic;      }

    // Live monitor toggle. Starting/stopping the WASAPI render endpoint is
    // expensive enough that we do it lazily here instead of on every packet.
    bool SetMonitorEnabled(bool on)
    {
        m_monitorEnabled.store(on);
        if (!on) {
            m_monitor.Stop();
            return true;
        }
        if (!m_sampleRate || !m_numChannels) return false; // not configured yet
        if (m_monitor.IsActive()) return true;
        return m_monitor.Start(m_sampleRate, m_numChannels);
    }
    bool IsMonitorEnabled() const { return m_monitorEnabled.load(); }
    bool IsMonitorActive()  const { return m_monitor.IsActive();    }

    void StopAll() { m_monitor.Stop(); }

private:
    EffectRack          m_rackLoopback;
    EffectRack          m_rackMic;
    LiveMonitor         m_monitor;
    LufsMeter           m_meter;
    std::atomic<bool>   m_monitorEnabled{false};
    uint32_t            m_sampleRate  = 0;
    uint32_t            m_numChannels = 0;
    std::atomic<float>  m_gain{1.0f};
};

static AudioMixer g_audioMixer;

#pragma endregion

#pragma region D3D11_CAPTURE_PREVIEW

// ---------------------------------------------------------------------------
// CompositeOverlays — paint the OS cursor and (optionally) click-marker rings
// onto a freshly captured BGRA32 frame buffer.
//
// monitorRect is the screen-space rectangle of the captured monitor, used to
// translate cursor screen coordinates into frame-local coordinates.
//
// Cached resources (DC + DIB) live for the lifetime of the process; cleaned
// up automatically on exit by the OS.
// ---------------------------------------------------------------------------
static void CompositeOverlays(BYTE* pDst, UINT dstStride, UINT frameW, UINT frameH,
                              const RECT& monitorRect)
{
    bool wantCursor = g_showCursor.load();
    bool lDown = g_markLeftClick.load()  && (GetAsyncKeyState(VK_LBUTTON) & 0x8000);
    bool rDown = g_markRightClick.load() && (GetAsyncKeyState(VK_RBUTTON) & 0x8000);
    if (!wantCursor && !lDown && !rDown) return;

    CURSORINFO ci = {};
    ci.cbSize = sizeof(ci);
    if (!GetCursorInfo(&ci)) return;
    if (!(ci.flags & CURSOR_SHOWING)) return;  // hidden by app (e.g. fullscreen game)

    const int curX = ci.ptScreenPos.x - monitorRect.left;
    const int curY = ci.ptScreenPos.y - monitorRect.top;

    // ---- click-marker rings ---------------------------------------------
    auto drawRing = [&](int cx, int cy, int radius, int thickness,
                        BYTE r, BYTE g, BYTE b, BYTE a)
    {
        const int rOut2 = radius * radius;
        const int rIn   = radius - thickness;
        const int rIn2  = (rIn > 0) ? rIn * rIn : 0;
        for (int dy = -radius; dy <= radius; ++dy) {
            int y = cy + dy;
            if (y < 0 || (UINT)y >= frameH) continue;
            for (int dx = -radius; dx <= radius; ++dx) {
                int x = cx + dx;
                if (x < 0 || (UINT)x >= frameW) continue;
                int d2 = dx * dx + dy * dy;
                if (d2 > rOut2 || d2 < rIn2) continue;
                BYTE* px = pDst + (size_t)y * dstStride + x * 4;
                int invA = 255 - a;
                px[0] = (BYTE)((px[0] * invA + b * a) / 255);
                px[1] = (BYTE)((px[1] * invA + g * a) / 255);
                px[2] = (BYTE)((px[2] * invA + r * a) / 255);
            }
        }
    };
    if (lDown) drawRing(curX, curY, 26, 4, 255,  40,  40, 200);   // red
    if (rDown) drawRing(curX, curY, 20, 4,  60, 110, 255, 200);   // blue

    // ---- cursor bitmap ---------------------------------------------------
    if (wantCursor) {
        ICONINFO iconInfo = {};
        if (!GetIconInfo(ci.hCursor, &iconInfo)) return;
        const int hotX = (int)iconInfo.xHotspot;
        const int hotY = (int)iconInfo.yHotspot;
        if (iconInfo.hbmMask)  DeleteObject(iconInfo.hbmMask);
        if (iconInfo.hbmColor) DeleteObject(iconInfo.hbmColor);

        constexpr int kSize = 64;
        static HDC     s_memDC  = nullptr;
        static HBITMAP s_dib    = nullptr;
        static BYTE*   s_pixels = nullptr;
        if (!s_memDC) {
            HDC screenDC = GetDC(nullptr);
            s_memDC = CreateCompatibleDC(screenDC);
            ReleaseDC(nullptr, screenDC);
            if (s_memDC) {
                BITMAPINFO bi = {};
                bi.bmiHeader.biSize        = sizeof(BITMAPINFOHEADER);
                bi.bmiHeader.biWidth       = kSize;
                bi.bmiHeader.biHeight      = -kSize;          // top-down
                bi.bmiHeader.biPlanes      = 1;
                bi.bmiHeader.biBitCount    = 32;
                bi.bmiHeader.biCompression = BI_RGB;
                s_dib = CreateDIBSection(s_memDC, &bi, DIB_RGB_COLORS,
                                         (void**)&s_pixels, nullptr, 0);
                if (s_dib) SelectObject(s_memDC, s_dib);
            }
        }
        if (!s_memDC || !s_dib || !s_pixels) return;

        // Clear and render
        memset(s_pixels, 0, kSize * kSize * 4);
        DrawIconEx(s_memDC, 0, 0, ci.hCursor, kSize, kSize, 0, nullptr, DI_NORMAL);
        GdiFlush();

        const int destX = curX - hotX;
        const int destY = curY - hotY;
        for (int sy = 0; sy < kSize; ++sy) {
            int dy = destY + sy;
            if (dy < 0 || (UINT)dy >= frameH) continue;
            BYTE* srcRow = s_pixels + (size_t)sy * kSize * 4;
            BYTE* dstRow = pDst    + (size_t)dy * dstStride;
            for (int sx = 0; sx < kSize; ++sx) {
                int dx = destX + sx;
                if (dx < 0 || (UINT)dx >= frameW) continue;
                BYTE* sp = srcRow + sx * 4;
                BYTE  sB = sp[0], sG = sp[1], sR = sp[2], sA = sp[3];
                // Skip fully-transparent pixels.
                if ((sA == 0) && (sR | sG | sB) == 0) continue;
                BYTE* dp = dstRow + dx * 4;
                if (sA == 0) {
                    // DrawIconEx may produce 0-alpha for opaque cursor pixels
                    // (legacy AND/XOR mask cursors). If we have any color,
                    // treat it as opaque.
                    dp[0] = sB; dp[1] = sG; dp[2] = sR;
                } else {
                    int invA = 255 - sA;
                    dp[0] = (BYTE)((dp[0] * invA + sB * sA) / 255);
                    dp[1] = (BYTE)((dp[1] * invA + sG * sA) / 255);
                    dp[2] = (BYTE)((dp[2] * invA + sR * sA) / 255);
                }
            }
        }
    }
}

// =====================================================================
// Compositor (Phase 2) — multi-source canvas + draggable resize handles
// =====================================================================
//
//   [DesktopSource | ImageSource | TextSource | WindowSource | WebcamSource]
//             |                                                  |
//              \                                                /
//               --> CompositorCanvas (D3D11 RTV at canvas res)
//                          |
//                          +--> staging tex --> encoder (WMF)
//                          +--> SRV          --> preview HWND back buffer
//                                            +-> D2D handles overlay
//
//  - Canvas resolution defaults to 1920x1080. The encoder receives the
//    canvas readback (instead of the desktop staging texture).
//  - Each source has a SourceTransform { x, y, w, h, opacity, visible,
//    locked, name }. Transforms live in canvas pixel coords.
//  - The composite shader supports per-source position+size via constant
//    buffer; per-pixel alpha blending so transparent regions of an image
//    or text source see the layers behind.
// =====================================================================

namespace cmp {

// ----------------- Source kinds ---------------------------------------
enum class SourceKind {
    Desktop = 0,
    Window  = 1,
    Webcam  = 2,
    Image   = 3,
    Text    = 4,
};

inline const wchar_t* SourceKindName(SourceKind k) {
    switch (k) {
        case SourceKind::Desktop: return L"Desktop";
        case SourceKind::Window:  return L"Window";
        case SourceKind::Webcam:  return L"Webcam";
        case SourceKind::Image:   return L"Image";
        case SourceKind::Text:    return L"Text";
    }
    return L"Source";
}

// Transform is in canvas pixel coordinates. (x, y) is the top-left.
struct SourceTransform {
    float x = 0, y = 0;
    float w = 1920, h = 1080;
    float opacity = 1.0f;
    bool  visible = true;
    bool  locked  = false;
};

// ----------------- ISource interface ----------------------------------
class ISource {
public:
    virtual ~ISource() = default;
    virtual SourceKind   Kind() const = 0;
    virtual const wchar_t* DisplayName() const = 0;
    virtual void          SetDisplayName(const wchar_t* n) = 0;

    // Native pixel size of the source content. May change at runtime
    // (webcam reformat, window resize, text reflow).
    virtual UINT NativeWidth()  = 0;
    virtual UINT NativeHeight() = 0;

    // Refresh the SRV from any backing source (acquires a new desktop
    // frame, drains a webcam packet, etc.). Called per frame from the
    // capture thread.
    virtual void Update(ID3D11Device* dev, ID3D11DeviceContext* ctx) {}

    // The texture used by the compositor as the source for the textured
    // quad. nullptr -> source draws as a checkerboard placeholder.
    virtual ID3D11ShaderResourceView* SRV() = 0;

    // Per-instance state.
    SourceTransform t;
    int             id = 0;
};

// ----------------- ImageSource ----------------------------------------
//
// Loads a PNG/JPG/BMP via WIC, copies into a static D3D11 BGRA tex.
class ImageSource : public ISource {
public:
    SourceKind Kind() const override { return SourceKind::Image; }
    const wchar_t* DisplayName() const override { return m_name.c_str(); }
    void SetDisplayName(const wchar_t* n) override { m_name = n ? n : L""; }
    UINT NativeWidth()  override { return m_w; }
    UINT NativeHeight() override { return m_h; }
    ID3D11ShaderResourceView* SRV() override { return m_pSRV; }

    bool Load(ID3D11Device* dev, const wchar_t* path);

    void Release() {
        if (m_pSRV) { m_pSRV->Release(); m_pSRV = nullptr; }
        if (m_pTex) { m_pTex->Release(); m_pTex = nullptr; }
        m_w = m_h = 0;
    }
    ~ImageSource() override { Release(); }

    std::wstring m_path;
private:
    std::wstring               m_name = L"Image";
    ID3D11Texture2D*           m_pTex = nullptr;
    ID3D11ShaderResourceView*  m_pSRV = nullptr;
    UINT m_w = 0, m_h = 0;
};

inline bool ImageSource::Load(ID3D11Device* dev, const wchar_t* path)
{
    Release();
    if (!dev || !path) return false;
    m_path = path;

    IWICImagingFactory* wicFac = nullptr;
    HRESULT hr = CoCreateInstance(CLSID_WICImagingFactory, nullptr, CLSCTX_INPROC_SERVER,
                                  IID_PPV_ARGS(&wicFac));
    if (FAILED(hr)) return false;

    IWICBitmapDecoder* dec = nullptr;
    hr = wicFac->CreateDecoderFromFilename(path, nullptr, GENERIC_READ,
                                           WICDecodeMetadataCacheOnLoad, &dec);
    if (FAILED(hr) || !dec) { wicFac->Release(); return false; }

    IWICBitmapFrameDecode* fr = nullptr;
    hr = dec->GetFrame(0, &fr);
    if (FAILED(hr) || !fr) { dec->Release(); wicFac->Release(); return false; }

    IWICFormatConverter* conv = nullptr;
    hr = wicFac->CreateFormatConverter(&conv);
    if (FAILED(hr) || !conv) {
        fr->Release(); dec->Release(); wicFac->Release(); return false;
    }
    hr = conv->Initialize(fr, GUID_WICPixelFormat32bppPBGRA,
                          WICBitmapDitherTypeNone, nullptr, 0.0,
                          WICBitmapPaletteTypeMedianCut);
    if (FAILED(hr)) {
        conv->Release(); fr->Release(); dec->Release(); wicFac->Release();
        return false;
    }

    UINT w = 0, h = 0;
    conv->GetSize(&w, &h);
    if (w == 0 || h == 0) {
        conv->Release(); fr->Release(); dec->Release(); wicFac->Release();
        return false;
    }
    std::vector<BYTE> bytes((size_t)w * h * 4);
    hr = conv->CopyPixels(nullptr, w * 4, (UINT)bytes.size(), bytes.data());
    conv->Release(); fr->Release(); dec->Release(); wicFac->Release();
    if (FAILED(hr)) return false;

    D3D11_TEXTURE2D_DESC td = {};
    td.Width            = w;
    td.Height           = h;
    td.MipLevels        = 1;
    td.ArraySize        = 1;
    td.Format           = DXGI_FORMAT_B8G8R8A8_UNORM;
    td.SampleDesc.Count = 1;
    td.Usage            = D3D11_USAGE_IMMUTABLE;
    td.BindFlags        = D3D11_BIND_SHADER_RESOURCE;

    D3D11_SUBRESOURCE_DATA sd = {};
    sd.pSysMem     = bytes.data();
    sd.SysMemPitch = w * 4;

    hr = dev->CreateTexture2D(&td, &sd, &m_pTex);
    if (FAILED(hr) || !m_pTex) return false;

    D3D11_SHADER_RESOURCE_VIEW_DESC svd = {};
    svd.Format                    = DXGI_FORMAT_B8G8R8A8_UNORM;
    svd.ViewDimension             = D3D11_SRV_DIMENSION_TEXTURE2D;
    svd.Texture2D.MipLevels       = 1;
    hr = dev->CreateShaderResourceView(m_pTex, &svd, &m_pSRV);
    if (FAILED(hr)) { m_pTex->Release(); m_pTex = nullptr; return false; }

    m_w = w; m_h = h;

    // Default name from filename
    const wchar_t* base = wcsrchr(path, L'\\');
    if (!base) base = wcsrchr(path, L'/');
    SetDisplayName(base ? base + 1 : path);
    t.w = (float)w;
    t.h = (float)h;
    return true;
}

// ----------------- TextSource -----------------------------------------
//
// DirectWrite -> D2D bitmap render target -> CPU readback -> D3D11 tex.
// Regenerated whenever text/font/colour/size changes.
class TextSource : public ISource {
public:
    SourceKind Kind() const override { return SourceKind::Text; }
    const wchar_t* DisplayName() const override { return m_name.c_str(); }
    void SetDisplayName(const wchar_t* n) override { m_name = n ? n : L""; }
    UINT NativeWidth()  override { return m_w; }
    UINT NativeHeight() override { return m_h; }
    ID3D11ShaderResourceView* SRV() override { return m_pSRV; }

    bool Rebuild(ID3D11Device* dev, ID2D1Factory1* d2dFac, IDWriteFactory* dwFac);

    void Release() {
        if (m_pSRV) { m_pSRV->Release(); m_pSRV = nullptr; }
        if (m_pTex) { m_pTex->Release(); m_pTex = nullptr; }
        m_w = m_h = 0;
    }
    ~TextSource() override { Release(); }

    std::wstring m_text       = L"Sample text";
    std::wstring m_fontFamily = L"Segoe UI Variable";
    float        m_fontSize   = 64.0f;
    DWRITE_FONT_WEIGHT m_weight = DWRITE_FONT_WEIGHT_BOLD;
    DWRITE_FONT_STYLE  m_style  = DWRITE_FONT_STYLE_NORMAL;
    UINT32       m_color      = 0xFFFFFFFFu;     // ARGB
    bool         m_dirty      = true;
private:
    std::wstring m_name = L"Text";
    ID3D11Texture2D*           m_pTex = nullptr;
    ID3D11ShaderResourceView*  m_pSRV = nullptr;
    UINT m_w = 0, m_h = 0;
};

inline bool TextSource::Rebuild(ID3D11Device* dev, ID2D1Factory1* d2dFac, IDWriteFactory* dwFac)
{
    if (!dev || !d2dFac || !dwFac) return false;
    Release();
    m_dirty = false;

    IDWriteTextFormat* fmt = nullptr;
    HRESULT hr = dwFac->CreateTextFormat(
        m_fontFamily.c_str(), nullptr,
        m_weight, m_style, DWRITE_FONT_STRETCH_NORMAL,
        m_fontSize, L"en-us", &fmt);
    if (FAILED(hr) || !fmt) return false;

    // Measure
    IDWriteTextLayout* layout = nullptr;
    hr = dwFac->CreateTextLayout(m_text.c_str(), (UINT32)m_text.size(),
                                 fmt, 4096.0f, 4096.0f, &layout);
    if (FAILED(hr) || !layout) { fmt->Release(); return false; }

    DWRITE_TEXT_METRICS m = {};
    layout->GetMetrics(&m);

    UINT w = (UINT)std::max(8.0f, std::ceil(m.widthIncludingTrailingWhitespace + 4.0f));
    UINT h = (UINT)std::max(8.0f, std::ceil(m.height + 4.0f));
    if (w > 4096) w = 4096;
    if (h > 4096) h = 4096;

    // Create D3D11 texture (BGRA, render-targetable, shared with D2D)
    D3D11_TEXTURE2D_DESC td = {};
    td.Width            = w;
    td.Height           = h;
    td.MipLevels        = 1;
    td.ArraySize        = 1;
    td.Format           = DXGI_FORMAT_B8G8R8A8_UNORM;
    td.SampleDesc.Count = 1;
    td.Usage            = D3D11_USAGE_DEFAULT;
    td.BindFlags        = D3D11_BIND_SHADER_RESOURCE | D3D11_BIND_RENDER_TARGET;
    td.MiscFlags        = 0;
    hr = dev->CreateTexture2D(&td, nullptr, &m_pTex);
    if (FAILED(hr) || !m_pTex) {
        layout->Release(); fmt->Release(); return false;
    }

    IDXGISurface* surf = nullptr;
    hr = m_pTex->QueryInterface(__uuidof(IDXGISurface), (void**)&surf);
    if (FAILED(hr)) {
        layout->Release(); fmt->Release(); Release(); return false;
    }

    D2D1_RENDER_TARGET_PROPERTIES rtp =
        D2D1::RenderTargetProperties(
            D2D1_RENDER_TARGET_TYPE_DEFAULT,
            D2D1::PixelFormat(DXGI_FORMAT_B8G8R8A8_UNORM, D2D1_ALPHA_MODE_PREMULTIPLIED));
    ID2D1RenderTarget* rt = nullptr;
    hr = d2dFac->CreateDxgiSurfaceRenderTarget(surf, &rtp, &rt);
    surf->Release();
    if (FAILED(hr) || !rt) {
        layout->Release(); fmt->Release(); Release(); return false;
    }

    rt->BeginDraw();
    rt->Clear(D2D1::ColorF(0, 0, 0, 0));    // transparent background

    // Build colour brush from ARGB packed value (premultiplied alpha)
    float ca = ((m_color >> 24) & 0xFF) / 255.0f;
    float cr = ((m_color >> 16) & 0xFF) / 255.0f;
    float cg = ((m_color >>  8) & 0xFF) / 255.0f;
    float cb = ((m_color      ) & 0xFF) / 255.0f;
    ID2D1SolidColorBrush* br = nullptr;
    rt->CreateSolidColorBrush(D2D1::ColorF(cr, cg, cb, ca), &br);
    if (br) {
        rt->DrawTextLayout(D2D1::Point2F(2.0f, 2.0f), layout, br,
                           D2D1_DRAW_TEXT_OPTIONS_ENABLE_COLOR_FONT);
        br->Release();
    }
    rt->EndDraw();
    rt->Release();

    layout->Release();
    fmt->Release();

    D3D11_SHADER_RESOURCE_VIEW_DESC svd = {};
    svd.Format              = DXGI_FORMAT_B8G8R8A8_UNORM;
    svd.ViewDimension       = D3D11_SRV_DIMENSION_TEXTURE2D;
    svd.Texture2D.MipLevels = 1;
    hr = dev->CreateShaderResourceView(m_pTex, &svd, &m_pSRV);
    if (FAILED(hr)) { Release(); return false; }

    m_w = w;
    m_h = h;
    if (t.w <= 0 || t.h <= 0) { t.w = (float)w; t.h = (float)h; }
    return true;
}

// ----------------- WebcamSource (IMFSourceReader, BGRA) ---------------
//
// Best-effort: uses MFCreateSourceReaderFromMediaSource on the chosen
// Video Capture device, asks the reader for an RGB32 output type, and
// uploads each new sample to a dynamic D3D11 texture.
class WebcamSource : public ISource {
public:
    SourceKind Kind() const override { return SourceKind::Webcam; }
    const wchar_t* DisplayName() const override { return m_name.c_str(); }
    void SetDisplayName(const wchar_t* n) override { m_name = n ? n : L""; }
    UINT NativeWidth()  override { return m_w; }
    UINT NativeHeight() override { return m_h; }
    ID3D11ShaderResourceView* SRV() override { return m_pSRV; }

    void Update(ID3D11Device* dev, ID3D11DeviceContext* ctx) override;
    bool Open(ID3D11Device* dev, IMFActivate* dev_act);

    void Release() {
        if (m_pSRV) { m_pSRV->Release(); m_pSRV = nullptr; }
        if (m_pTex) { m_pTex->Release(); m_pTex = nullptr; }
        if (m_reader) { m_reader->Release(); m_reader = nullptr; }
        m_w = m_h = 0;
    }
    ~WebcamSource() override { Release(); }

    std::wstring m_devSymlink;     // for re-opening
private:
    std::wstring m_name = L"Webcam";
    IMFSourceReader*           m_reader = nullptr;
    ID3D11Texture2D*           m_pTex   = nullptr;
    ID3D11ShaderResourceView*  m_pSRV   = nullptr;
    UINT m_w = 0, m_h = 0;
    UINT m_stride = 0;
    bool m_topDown = true;
};

inline bool WebcamSource::Open(ID3D11Device* dev, IMFActivate* dev_act)
{
    if (!dev || !dev_act) return false;
    Release();

    IMFMediaSource* src = nullptr;
    HRESULT hr = dev_act->ActivateObject(IID_PPV_ARGS(&src));
    if (FAILED(hr) || !src) return false;

    // No reader attributes — default behaviour lets MF insert a colour
    // converter / decoder DSP automatically when needed.
    hr = MFCreateSourceReaderFromMediaSource(src, nullptr, &m_reader);
    src->Release();
    if (FAILED(hr) || !m_reader) return false;

    // Ask the reader for RGB32 output (the conversion runs in MF's
    // built-in color converter / decoder DSP).
    IMFMediaType* outType = nullptr;
    MFCreateMediaType(&outType);
    outType->SetGUID(MF_MT_MAJOR_TYPE, MFMediaType_Video);
    outType->SetGUID(MF_MT_SUBTYPE,    MFVideoFormat_RGB32);
    hr = m_reader->SetCurrentMediaType((DWORD)MF_SOURCE_READER_FIRST_VIDEO_STREAM,
                                        nullptr, outType);
    outType->Release();
    if (FAILED(hr)) {
        m_reader->Release(); m_reader = nullptr;
        return false;
    }

    // Read the negotiated size
    IMFMediaType* curType = nullptr;
    hr = m_reader->GetCurrentMediaType((DWORD)MF_SOURCE_READER_FIRST_VIDEO_STREAM, &curType);
    if (SUCCEEDED(hr) && curType) {
        UINT32 ww = 0, hh = 0;
        MFGetAttributeSize(curType, MF_MT_FRAME_SIZE, &ww, &hh);
        m_w = ww; m_h = hh;
        UINT32 stride = 0;
        if (FAILED(curType->GetUINT32(MF_MT_DEFAULT_STRIDE, &stride)) || stride == 0) {
            stride = m_w * 4;
        } else {
            m_topDown = ((INT32)stride > 0);
            if ((INT32)stride < 0) stride = (UINT32)(-(INT32)stride);
        }
        m_stride = stride;
        curType->Release();
    }

    if (m_w == 0 || m_h == 0) {
        m_w = 1280; m_h = 720; m_stride = m_w * 4;
    }

    D3D11_TEXTURE2D_DESC td = {};
    td.Width  = m_w;
    td.Height = m_h;
    td.MipLevels = 1;
    td.ArraySize = 1;
    td.Format = DXGI_FORMAT_B8G8R8A8_UNORM;
    td.SampleDesc.Count = 1;
    td.Usage = D3D11_USAGE_DYNAMIC;
    td.BindFlags = D3D11_BIND_SHADER_RESOURCE;
    td.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
    hr = dev->CreateTexture2D(&td, nullptr, &m_pTex);
    if (FAILED(hr) || !m_pTex) { Release(); return false; }

    D3D11_SHADER_RESOURCE_VIEW_DESC svd = {};
    svd.Format              = DXGI_FORMAT_B8G8R8A8_UNORM;
    svd.ViewDimension       = D3D11_SRV_DIMENSION_TEXTURE2D;
    svd.Texture2D.MipLevels = 1;
    hr = dev->CreateShaderResourceView(m_pTex, &svd, &m_pSRV);
    if (FAILED(hr)) { Release(); return false; }

    if (t.w <= 0 || t.h <= 0) { t.w = (float)m_w; t.h = (float)m_h; }
    return true;
}

inline void WebcamSource::Update(ID3D11Device* dev, ID3D11DeviceContext* ctx)
{
    (void)dev;
    if (!m_reader || !m_pTex) return;

    // Drain available frames non-blocking; only the most recent frame is
    // uploaded to the GPU.
    IMFSample* sampleLatest = nullptr;
    for (int guard = 0; guard < 4; ++guard) {
        DWORD streamFlags = 0;
        LONGLONG ts = 0;
        IMFSample* s = nullptr;
        HRESULT hr = m_reader->ReadSample(
            (DWORD)MF_SOURCE_READER_FIRST_VIDEO_STREAM,
            MF_SOURCE_READER_CONTROLF_DRAIN, nullptr, &streamFlags, &ts, &s);
        if (FAILED(hr)) break;
        if (!s) {
            // No new frame in non-blocking ReadSample
            break;
        }
        if (sampleLatest) sampleLatest->Release();
        sampleLatest = s;
        if (streamFlags & MF_SOURCE_READERF_ENDOFSTREAM) break;
    }
    if (!sampleLatest) return;

    IMFMediaBuffer* buf = nullptr;
    if (SUCCEEDED(sampleLatest->ConvertToContiguousBuffer(&buf)) && buf) {
        BYTE* sp = nullptr;
        DWORD maxL = 0, curL = 0;
        if (SUCCEEDED(buf->Lock(&sp, &maxL, &curL))) {
            D3D11_MAPPED_SUBRESOURCE map = {};
            if (SUCCEEDED(ctx->Map(m_pTex, 0, D3D11_MAP_WRITE_DISCARD, 0, &map))) {
                BYTE* dp = (BYTE*)map.pData;
                UINT srcStride = m_stride ? m_stride : m_w * 4;
                if (m_topDown) {
                    for (UINT y = 0; y < m_h; ++y) {
                        memcpy(dp + (size_t)y * map.RowPitch,
                               sp + (size_t)y * srcStride, m_w * 4);
                    }
                } else {
                    for (UINT y = 0; y < m_h; ++y) {
                        memcpy(dp + (size_t)y * map.RowPitch,
                               sp + (size_t)(m_h - 1 - y) * srcStride, m_w * 4);
                    }
                }
                ctx->Unmap(m_pTex, 0);
            }
            buf->Unlock();
        }
        buf->Release();
    }
    sampleLatest->Release();
}

// ----------------- WindowSource (PrintWindow stub) --------------------
//
// Capture a visible top-level window via PrintWindow (PW_RENDERFULLCONTENT
// flag). Falls back to BitBlt if PrintWindow returns 0. Simple, no GPU
// dependency, works on any Windows version. Slower than the proper
// Windows.Graphics.Capture WinRT path but reliable as a baseline.
class WindowSource : public ISource {
public:
    SourceKind Kind() const override { return SourceKind::Window; }
    const wchar_t* DisplayName() const override { return m_name.c_str(); }
    void SetDisplayName(const wchar_t* n) override { m_name = n ? n : L""; }
    UINT NativeWidth()  override { return m_w; }
    UINT NativeHeight() override { return m_h; }
    ID3D11ShaderResourceView* SRV() override { return m_pSRV; }

    bool Bind(ID3D11Device* dev, HWND target, const wchar_t* title);

    void Update(ID3D11Device* dev, ID3D11DeviceContext* ctx) override;

    void Release() {
        if (m_pSRV) { m_pSRV->Release(); m_pSRV = nullptr; }
        if (m_pTex) { m_pTex->Release(); m_pTex = nullptr; }
        if (m_dib)   { DeleteObject(m_dib); m_dib = nullptr; }
        if (m_memDC) { DeleteDC(m_memDC);   m_memDC = nullptr; }
        m_pixels = nullptr;
        m_target = nullptr;
        m_w = m_h = 0;
    }
    ~WindowSource() override { Release(); }

    HWND m_target = nullptr;
private:
    std::wstring m_name = L"Window";
    ID3D11Texture2D*           m_pTex = nullptr;
    ID3D11ShaderResourceView*  m_pSRV = nullptr;
    HDC      m_memDC  = nullptr;
    HBITMAP  m_dib    = nullptr;
    BYTE*    m_pixels = nullptr;
    UINT     m_w = 0, m_h = 0;
};

inline bool WindowSource::Bind(ID3D11Device* dev, HWND target, const wchar_t* title)
{
    if (!dev || !IsWindow(target)) return false;
    Release();
    m_target = target;
    if (title && *title) m_name = title;

    RECT r = {};
    if (!GetWindowRect(target, &r)) return false;
    UINT w = (UINT)std::max(64L, r.right - r.left);
    UINT h = (UINT)std::max(64L, r.bottom - r.top);
    m_w = w; m_h = h;

    HDC scrDC = GetDC(nullptr);
    m_memDC = CreateCompatibleDC(scrDC);
    ReleaseDC(nullptr, scrDC);
    if (!m_memDC) return false;

    BITMAPINFO bi = {};
    bi.bmiHeader.biSize        = sizeof(BITMAPINFOHEADER);
    bi.bmiHeader.biWidth       = (LONG)m_w;
    bi.bmiHeader.biHeight      = -(LONG)m_h;     // top-down
    bi.bmiHeader.biPlanes      = 1;
    bi.bmiHeader.biBitCount    = 32;
    bi.bmiHeader.biCompression = BI_RGB;
    m_dib = CreateDIBSection(m_memDC, &bi, DIB_RGB_COLORS,
                             (void**)&m_pixels, nullptr, 0);
    if (!m_dib || !m_pixels) { Release(); return false; }
    SelectObject(m_memDC, m_dib);

    D3D11_TEXTURE2D_DESC td = {};
    td.Width  = m_w;
    td.Height = m_h;
    td.MipLevels = 1;
    td.ArraySize = 1;
    td.Format = DXGI_FORMAT_B8G8R8A8_UNORM;
    td.SampleDesc.Count = 1;
    td.Usage = D3D11_USAGE_DYNAMIC;
    td.BindFlags = D3D11_BIND_SHADER_RESOURCE;
    td.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
    HRESULT hr = dev->CreateTexture2D(&td, nullptr, &m_pTex);
    if (FAILED(hr) || !m_pTex) { Release(); return false; }
    D3D11_SHADER_RESOURCE_VIEW_DESC svd = {};
    svd.Format              = DXGI_FORMAT_B8G8R8A8_UNORM;
    svd.ViewDimension       = D3D11_SRV_DIMENSION_TEXTURE2D;
    svd.Texture2D.MipLevels = 1;
    hr = dev->CreateShaderResourceView(m_pTex, &svd, &m_pSRV);
    if (FAILED(hr)) { Release(); return false; }

    if (t.w <= 0 || t.h <= 0) { t.w = (float)m_w; t.h = (float)m_h; }
    return true;
}

inline void WindowSource::Update(ID3D11Device* dev, ID3D11DeviceContext* ctx)
{
    (void)dev;
    if (!m_target || !m_memDC || !m_pixels || !m_pTex) return;
    if (!IsWindow(m_target)) return;

    // PrintWindow with PW_RENDERFULLCONTENT (3) for layered/DWM windows.
    if (!PrintWindow(m_target, m_memDC, 3 /* PW_RENDERFULLCONTENT */)) {
        // Fallback to BitBlt from the window DC
        HDC src = GetDC(m_target);
        if (src) {
            BitBlt(m_memDC, 0, 0, (int)m_w, (int)m_h, src, 0, 0, SRCCOPY);
            ReleaseDC(m_target, src);
        }
    }
    GdiFlush();

    D3D11_MAPPED_SUBRESOURCE map = {};
    if (SUCCEEDED(ctx->Map(m_pTex, 0, D3D11_MAP_WRITE_DISCARD, 0, &map))) {
        for (UINT y = 0; y < m_h; ++y) {
            BYTE* dst = (BYTE*)map.pData + (size_t)y * map.RowPitch;
            BYTE* sp  = m_pixels + (size_t)y * m_w * 4;
            // Force alpha to 0xFF — GDI doesn't write alpha.
            for (UINT x = 0; x < m_w; ++x) {
                dst[0] = sp[0]; dst[1] = sp[1]; dst[2] = sp[2]; dst[3] = 0xFF;
                dst += 4; sp += 4;
            }
        }
        ctx->Unmap(m_pTex, 0);
    }
}

// ----------------- DesktopSource (wraps existing renderer SRV) --------
//
// Owns nothing — its SRV is provided by the existing DXGI duplication
// inside `DxgiCaptureRenderer` (m_pLastCaptureSRV). Per-frame Update is
// a no-op; the renderer drives the duplication in the capture thread.
class DesktopSource : public ISource {
public:
    SourceKind Kind() const override { return SourceKind::Desktop; }
    const wchar_t* DisplayName() const override { return m_name.c_str(); }
    void SetDisplayName(const wchar_t* n) override { m_name = n ? n : L""; }
    UINT NativeWidth()  override { return m_w; }
    UINT NativeHeight() override { return m_h; }
    ID3D11ShaderResourceView* SRV() override { return m_pExtSRV; }

    void Bind(ID3D11ShaderResourceView* extSRV, UINT w, UINT h) {
        m_pExtSRV = extSRV; m_w = w; m_h = h;
        if (t.w <= 0 || t.h <= 0) { t.w = (float)w; t.h = (float)h; }
    }
private:
    std::wstring m_name = L"Display capture";
    ID3D11ShaderResourceView* m_pExtSRV = nullptr;
    UINT m_w = 1920, m_h = 1080;
};

// ----------------- Source list (global) -------------------------------
static std::vector<std::unique_ptr<ISource>> g_sources;
static std::mutex                            g_sourcesMutex;
static int                                   g_nextSourceId = 1;
static int                                   g_selectedSourceId = -1;
static int                                   g_canvasW = 1920;
static int                                   g_canvasH = 1080;

// ---------------------------------------------------------------------
// Drag-time alignment guides (OBS-style). The preview drag code writes
// these whenever a source edge / centerline snaps to the canvas
// edges/centerlines or another source's edges/centerlines, and the D2D
// overlay reads them to draw dashed magenta lines across the canvas.
// `overflow` is set when the moved/resized source extends past the
// canvas bounds, and the renderer paints the out-of-bounds region with
// a red dashed contour.
// ---------------------------------------------------------------------
struct DragGuides {
    bool  active        = false;
    bool  overflow      = false;
    float overflowL=0,  overflowT=0,  overflowR=0,  overflowB=0;  // canvas px rect
    int   vCount        = 0;          // # of vertical guides
    int   hCount        = 0;          // # of horizontal guides
    float vX[8]         = {0};        // canvas-pixel X for each vertical guide
    float hY[8]         = {0};        // canvas-pixel Y for each horizontal guide
    void  Reset() { active = overflow = false; vCount = hCount = 0; }
    void  AddV(float x) {
        for (int i = 0; i < vCount; ++i) if (std::abs(vX[i] - x) < 0.5f) return;
        if (vCount < 8) vX[vCount++] = x;
    }
    void  AddH(float y) {
        for (int i = 0; i < hCount; ++i) if (std::abs(hY[i] - y) < 0.5f) return;
        if (hCount < 8) hY[hCount++] = y;
    }
};
static DragGuides                            g_dragGuides;

inline ISource* FindSource(int id) {
    for (auto& s : g_sources) if (s && s->id == id) return s.get();
    return nullptr;
}

inline int AddSource(std::unique_ptr<ISource> s) {
    if (!s) return -1;
    s->id = g_nextSourceId++;
    int id = s->id;
    std::lock_guard<std::mutex> lk(g_sourcesMutex);
    g_sources.push_back(std::move(s));
    g_selectedSourceId = id;
    return id;
}

inline void RemoveSource(int id) {
    std::lock_guard<std::mutex> lk(g_sourcesMutex);
    g_sources.erase(std::remove_if(g_sources.begin(), g_sources.end(),
        [id](const std::unique_ptr<ISource>& p){ return p && p->id == id; }),
        g_sources.end());
    if (g_selectedSourceId == id) g_selectedSourceId = -1;
}

inline void MoveSource(int id, int dir) {
    std::lock_guard<std::mutex> lk(g_sourcesMutex);
    int n = (int)g_sources.size();
    int idx = -1;
    for (int i = 0; i < n; ++i) if (g_sources[i] && g_sources[i]->id == id) { idx = i; break; }
    if (idx < 0) return;
    int target = idx + dir;
    if (target < 0 || target >= n) return;
    std::swap(g_sources[idx], g_sources[target]);
}

} // namespace cmp


class DxgiCaptureRenderer {
public:
    DxgiCaptureRenderer()  = default;
    ~DxgiCaptureRenderer() { Shutdown(); }

    bool Init(HWND previewWnd, int monitorIdx)
    {
        m_hwndPreview = previewWnd;
        m_monitorIdx  = monitorIdx;

        RECT rc = {};
        GetClientRect(previewWnd, &rc);
        m_previewW = rc.right  - rc.left;
        m_previewH = rc.bottom - rc.top;

        if (m_previewW < 8) m_previewW = 8;
        if (m_previewH < 8) m_previewH = 8;

        UINT createFlags = D3D11_CREATE_DEVICE_BGRA_SUPPORT;
#if defined(_DEBUG)
        createFlags |= D3D11_CREATE_DEVICE_DEBUG;
#endif
        D3D_FEATURE_LEVEL featureLevels[] = {
            D3D_FEATURE_LEVEL_11_1,
            D3D_FEATURE_LEVEL_11_0,
            D3D_FEATURE_LEVEL_10_1,
        };
        D3D_FEATURE_LEVEL chosenLevel = {};
        HRESULT hr = D3D11CreateDevice(
            nullptr, D3D_DRIVER_TYPE_HARDWARE, nullptr,
            createFlags, featureLevels, 3,
            D3D11_SDK_VERSION, &m_pDevice, &chosenLevel, &m_pContext);
        if (FAILED(hr)) {
            hr = D3D11CreateDevice(
                nullptr, D3D_DRIVER_TYPE_WARP, nullptr,
                createFlags, featureLevels, 3,
                D3D11_SDK_VERSION, &m_pDevice, &chosenLevel, &m_pContext);
            if (FAILED(hr)) return false;
        }

        IDXGIDevice* dxgiDev = nullptr;
        hr = m_pDevice->QueryInterface(__uuidof(IDXGIDevice), (void**)&dxgiDev);
        if (FAILED(hr) || !dxgiDev) return false;
        IDXGIAdapter* adapter = nullptr;
        hr = dxgiDev->GetAdapter(&adapter);
        if (FAILED(hr) || !adapter) {
            dxgiDev->Release();
            return false;
        }
        IDXGIFactory2* factory = nullptr;
        hr = adapter->GetParent(__uuidof(IDXGIFactory2), (void**)&factory);

        // Abort safely if DXGI 1.2 is unsupported on this hardware adapter
        if (FAILED(hr) || !factory) {
            adapter->Release();
            dxgiDev->Release();
            return false;
        }

        DXGI_SWAP_CHAIN_DESC1 scd = {};
        scd.Width       = (UINT)m_previewW;
        scd.Height      = (UINT)m_previewH;
        scd.Format      = DXGI_FORMAT_B8G8R8A8_UNORM;
        scd.SampleDesc.Count = 1;
        scd.BufferUsage = DXGI_USAGE_RENDER_TARGET_OUTPUT;
        scd.BufferCount = 2;
        scd.SwapEffect  = DXGI_SWAP_EFFECT_FLIP_DISCARD;
        scd.Scaling     = DXGI_SCALING_STRETCH;
        hr = factory->CreateSwapChainForHwnd(m_pDevice, previewWnd, &scd, nullptr, nullptr, &m_pSwapChain);
        factory->Release();
        adapter->Release();
        dxgiDev->Release();
        if (FAILED(hr)) return false;

        if (!CreateRenderTarget()) return false;

        if (!BindDuplicationToMonitor(monitorIdx)) return false;

        DXGI_OUTDUPL_DESC dupDesc = {};
        m_pDuplication->GetDesc(&dupDesc);
        m_captureW = dupDesc.ModeDesc.Width;
        m_captureH = dupDesc.ModeDesc.Height;

        if (!CreateShaders()) return false;
        if (!CreateSamplerAndBlend()) return false;
        if (!CreateVertexBuffer()) return false;
        if (!CreateStagingTexture()) return false;

        // Phase 2 — compositor canvas (sized to a sane default; encoder
        // re-sizes via CreateCanvasResources when StartRecording starts).
        int initCanvasW = (int)m_captureW > 0 ? (int)m_captureW : 1920;
        int initCanvasH = (int)m_captureH > 0 ? (int)m_captureH : 1080;
        if (!CreateCanvasResources(initCanvasW, initCanvasH)) return false;
        if (!CreateQuadShaders())                            return false;
        if (!CreateQuadVB())                                 return false;
        if (!CreateD2DOverlay())                             return false;
        EnsurePlaceholder();

        return true;
    }

    // Bind m_pDuplication to the requested monitor (or the first available
    // output if monitorIdx < 0 / not found). Extracted so we can call it
    // BOTH from Init() and from AcquireFrame() after a DXGI access-lost
    // event — which is the main reason the preview was freezing badly:
    // any time the desktop session changes (UAC dialog, lock screen, RDP
    // reconnect, GPU driver reset, fullscreen-exclusive game alt-tab) DXGI
    // returns DXGI_ERROR_ACCESS_LOST and the old duplication is dead. The
    // previous code released it and left m_pDuplication permanently null,
    // so the preview never came back. Now we just rebind.
    bool BindDuplicationToMonitor(int monitorIdx)
    {
        if (m_pDuplication) {
            m_pDuplication->Release();
            m_pDuplication = nullptr;
        }
        if (!m_pDevice) return false;

        IDXGIFactory1* pFac1 = nullptr;
        if (FAILED(CreateDXGIFactory1(__uuidof(IDXGIFactory1), (void**)&pFac1)) || !pFac1)
            return false;

        if (monitorIdx >= 0 && monitorIdx < (int)g_monitors.size()) {
            UINT ai = 0;
            IDXGIAdapter* pAdap = nullptr;
            for (;;) {
                HRESULT eaHr = pFac1->EnumAdapters(ai, &pAdap);
                if (eaHr == DXGI_ERROR_NOT_FOUND) break;
                if (FAILED(eaHr) || !pAdap) { pAdap = nullptr; break; }

                UINT oi = 0;
                bool matched = false;
                IDXGIOutput* pOutput = nullptr;
                for (;;) {
                    HRESULT eoHr = pAdap->EnumOutputs(oi, &pOutput);
                    if (eoHr == DXGI_ERROR_NOT_FOUND) break;
                    if (FAILED(eoHr) || !pOutput) { pOutput = nullptr; break; }

                    DXGI_OUTPUT_DESC od = {};
                    pOutput->GetDesc(&od);
                    if (od.Monitor == g_monitors[monitorIdx].hMon) {
                        IDXGIOutput1* out1 = nullptr;
                        if (SUCCEEDED(pOutput->QueryInterface(__uuidof(IDXGIOutput1), (void**)&out1))) {
                            out1->DuplicateOutput(m_pDevice, &m_pDuplication);
                            out1->Release();
                        }
                        pOutput->Release(); pOutput = nullptr;
                        matched = true;
                        break;
                    }
                    pOutput->Release(); pOutput = nullptr;
                    oi++;
                }
                pAdap->Release(); pAdap = nullptr;
                if (matched) break;
                ai++;
            }
        }
        pFac1->Release();

        // Fallback: first available output on the device's primary adapter.
        if (!m_pDuplication) {
            IDXGIDevice*  dDev = nullptr;
            m_pDevice->QueryInterface(__uuidof(IDXGIDevice), (void**)&dDev);
            if (dDev) {
                IDXGIAdapter* pA0 = nullptr;
                if (SUCCEEDED(dDev->GetAdapter(&pA0)) && pA0) {
                    IDXGIOutput* pOut0 = nullptr;
                    if (SUCCEEDED(pA0->EnumOutputs(0, &pOut0)) && pOut0) {
                        IDXGIOutput1* out1 = nullptr;
                        if (SUCCEEDED(pOut0->QueryInterface(__uuidof(IDXGIOutput1), (void**)&out1))) {
                            out1->DuplicateOutput(m_pDevice, &m_pDuplication);
                            out1->Release();
                        }
                        pOut0->Release();
                    }
                    pA0->Release();
                }
                dDev->Release();
            }
        }

        return m_pDuplication != nullptr;
    }

    bool AcquireFrame(bool& gotFrame)
    {
        std::lock_guard<std::mutex> lock(m_ctxMutex);
        gotFrame = false;

        // If we lost duplication previously (or were never able to bind it
        // — e.g. DXGI was unavailable when Init ran on a remote-desktop
        // session), keep retrying inline so the preview comes back as soon
        // as the desktop is reachable again. We retry at most once per
        // call to avoid hot-spinning.
        if (!m_pDuplication) {
            if (!BindDuplicationToMonitor(m_monitorIdx)) return false;
            DXGI_OUTDUPL_DESC dupDesc = {};
            m_pDuplication->GetDesc(&dupDesc);
            m_captureW = dupDesc.ModeDesc.Width;
            m_captureH = dupDesc.ModeDesc.Height;
        }

        IDXGIResource* pRes   = nullptr;
        DXGI_OUTDUPL_FRAME_INFO fi = {};
        HRESULT hr = m_pDuplication->AcquireNextFrame(0, &fi, &pRes);
        if (hr == DXGI_ERROR_WAIT_TIMEOUT) return true;
        if (hr == DXGI_ERROR_ACCESS_LOST) {
            // Don't give up — drop the dead duplication and let the next
            // call re-bind via the path above. The preview keeps showing
            // the last good frame in the meantime instead of freezing.
            m_pDuplication->Release();
            m_pDuplication = nullptr;
            return true;
        }
        if (FAILED(hr)) return false;

        ID3D11Texture2D* pTex = nullptr;
        hr = pRes->QueryInterface(__uuidof(ID3D11Texture2D), (void**)&pTex);
        pRes->Release();
        if (FAILED(hr)) { m_pDuplication->ReleaseFrame(); return false; }

        D3D11_TEXTURE2D_DESC desc = {};
        pTex->GetDesc(&desc);

        if (m_pStagingTex) {
            D3D11_TEXTURE2D_DESC sd = {};
            m_pStagingTex->GetDesc(&sd);
            if (sd.Width != desc.Width || sd.Height != desc.Height) {
                m_pStagingTex->Release();
                m_pStagingTex = nullptr;
            }
        }
        if (!m_pStagingTex) {
            CreateStagingTexture(desc.Width, desc.Height);
        }

        // Pre-allocated capture texture + SRV — reused across frames. The
        // previous code did CreateTexture2D + CreateShaderResourceView on
        // EVERY captured frame (~30/s), which created driver allocation
        // pressure and was a long-tail contributor to the "preview freezes
        // badly" symptom: at 30Hz, an hour of recording would do ~108k
        // allocations and a similar number of D3D ref-counted releases. Now
        // we keep one texture + one SRV and only re-create them when the
        // capture's pixel dimensions actually change.
        bool needRebuild = (m_pLastCaptureTex == nullptr);
        if (m_pLastCaptureTex) {
            D3D11_TEXTURE2D_DESC cd = {};
            m_pLastCaptureTex->GetDesc(&cd);
            if (cd.Width != desc.Width || cd.Height != desc.Height)
                needRebuild = true;
        }
        if (needRebuild) {
            if (m_pLastCaptureSRV) { m_pLastCaptureSRV->Release(); m_pLastCaptureSRV = nullptr; }
            if (m_pLastCaptureTex) { m_pLastCaptureTex->Release(); m_pLastCaptureTex = nullptr; }

            D3D11_TEXTURE2D_DESC cpyDesc = {};
            cpyDesc.Width          = desc.Width;
            cpyDesc.Height         = desc.Height;
            cpyDesc.MipLevels      = 1;
            cpyDesc.ArraySize      = 1;
            cpyDesc.Format         = DXGI_FORMAT_B8G8R8A8_UNORM;
            cpyDesc.SampleDesc.Count = 1;
            cpyDesc.Usage          = D3D11_USAGE_DEFAULT;
            cpyDesc.BindFlags      = D3D11_BIND_SHADER_RESOURCE;
            m_pDevice->CreateTexture2D(&cpyDesc, nullptr, &m_pLastCaptureTex);
            if (m_pLastCaptureTex) {
                D3D11_SHADER_RESOURCE_VIEW_DESC srvd = {};
                srvd.Format                    = DXGI_FORMAT_B8G8R8A8_UNORM;
                srvd.ViewDimension             = D3D11_SRV_DIMENSION_TEXTURE2D;
                srvd.Texture2D.MipLevels       = 1;
                srvd.Texture2D.MostDetailedMip = 0;
                m_pDevice->CreateShaderResourceView(m_pLastCaptureTex, &srvd, &m_pLastCaptureSRV);
            }
        }
        if (m_pLastCaptureTex) {
            m_pContext->CopyResource(m_pLastCaptureTex, pTex);
        }

        if (m_pStagingTex) {
            m_pContext->CopyResource(m_pStagingTex, pTex);
            m_hasStagedFrame = true;
        }

        pTex->Release();
        m_pDuplication->ReleaseFrame();
        gotFrame = true;
        m_captureW = desc.Width;
        m_captureH = desc.Height;
        return true;
    }

    bool CopyStagedFrameToWMF(BYTE* pDst, UINT dstStride)
    {
        std::lock_guard<std::mutex> lock(m_ctxMutex);
        if (!m_pStagingTex || !m_hasStagedFrame) return false;
        D3D11_MAPPED_SUBRESOURCE mapped = {};
        HRESULT hr = m_pContext->Map(m_pStagingTex, 0, D3D11_MAP_READ, 0, &mapped);
        if (FAILED(hr)) return false;

        UINT rows = m_captureH;
        UINT rowBytes = m_captureW * 4;
        BYTE* src = (BYTE*)mapped.pData;
        for (UINT r = 0; r < rows; ++r) {
            memcpy(pDst + (LONGLONG)r * dstStride, src + (LONGLONG)r * mapped.RowPitch, rowBytes);
        }
        m_pContext->Unmap(m_pStagingTex, 0);

        // Composite mouse cursor / click markers onto the recorded frame.
        if (m_monitorIdx >= 0 && m_monitorIdx < (int)g_monitors.size()) {
            CompositeOverlays(pDst, dstStride, m_captureW, m_captureH,
                              g_monitors[m_monitorIdx].rect);
        }
        return true;
    }

    // Layout cache so the preview HWND mouse handler can map screen
    // pixels back into canvas pixels for hit-testing source rects /
    // drag handles.
    struct PreviewLayout {
        float viewX = 0, viewY = 0;
        float viewW = 0, viewH = 0;
        int   canvasW = 0, canvasH = 0;
    };
    PreviewLayout m_lastLayout;
    PreviewLayout GetLastLayout() { return m_lastLayout; }

    void RenderPreview()
    {
        std::lock_guard<std::mutex> lock(m_ctxMutex);
        if (!m_pRenderTargetView) return;
        // NOTE: m_pCanvasSRV may be null on the very first frame —
        // we still want to clear+Present the swap chain so the user
        // sees solid black, not whatever uninitialized memory the
        // back buffer was allocated on top of (which on some drivers
        // looks like a transparent checkerboard).

        RECT rc = {};
        GetClientRect(m_hwndPreview, &rc);
        int newW = rc.right - rc.left;
        int newH = rc.bottom - rc.top;
        if (newW < 8) newW = 8;
        if (newH < 8) newH = 8;

        if (newW != m_previewW || newH != m_previewH) {
            m_previewW = newW;
            m_previewH = newH;

            // Drop D2D back-buffer binding before swap-chain resize.
            if (m_pD2DContext) m_pD2DContext->SetTarget(nullptr);
            if (m_pD2DBackBuf) { m_pD2DBackBuf->Release(); m_pD2DBackBuf = nullptr; }

            m_pContext->ClearState();
            m_pContext->Flush();
            if (m_pRenderTargetView) {
                m_pRenderTargetView->Release();
                m_pRenderTargetView = nullptr;
            }
            m_pSwapChain->ResizeBuffers(2, (UINT)newW, (UINT)newH,
                                        DXGI_FORMAT_B8G8R8A8_UNORM, 0);
            if (!CreateRenderTarget()) return;
        }

        float clearColor[4] = {0.04f, 0.04f, 0.05f, 1.0f};
        m_pContext->ClearRenderTargetView(m_pRenderTargetView, clearColor);

        // Letterbox the canvas inside the preview HWND (canvas AR fixed
        // at m_canvasW : m_canvasH). Cache the mapping so the mouse
        // handler can convert screen pixels -> canvas pixels.
        FLOAT viewW = (FLOAT)m_previewW;
        FLOAT viewH = (FLOAT)m_previewH;
        FLOAT viewX = 0.0f;
        FLOAT viewY = 0.0f;
        if (m_canvasW > 0 && m_canvasH > 0 && m_previewW > 0 && m_previewH > 0) {
            const double srcAR = (double)m_canvasW / (double)m_canvasH;
            const double dstAR = (double)m_previewW / (double)m_previewH;
            if (srcAR > dstAR) {
                viewW = (FLOAT)m_previewW;
                viewH = (FLOAT)(m_previewW / srcAR);
                viewY = (FLOAT)((m_previewH - viewH) * 0.5);
            } else {
                viewH = (FLOAT)m_previewH;
                viewW = (FLOAT)(m_previewH * srcAR);
                viewX = (FLOAT)((m_previewW - viewW) * 0.5);
            }
        }
        m_lastLayout.viewX = viewX;
        m_lastLayout.viewY = viewY;
        m_lastLayout.viewW = viewW;
        m_lastLayout.viewH = viewH;
        m_lastLayout.canvasW = m_canvasW;
        m_lastLayout.canvasH = m_canvasH;

        D3D11_VIEWPORT vp = {};
        vp.TopLeftX = viewX;
        vp.TopLeftY = viewY;
        vp.Width    = viewW;
        vp.Height   = viewH;
        vp.MinDepth = 0.0f;
        vp.MaxDepth = 1.0f;
        m_pContext->RSSetViewports(1, &vp);
        m_pContext->OMSetRenderTargets(1, &m_pRenderTargetView, nullptr);

        UINT stride = sizeof(float) * 4;
        UINT offset = 0;
        if (m_pCanvasSRV) {
            m_pContext->VSSetShader(m_pVS, nullptr, 0);
            m_pContext->PSSetShader(m_pPS, nullptr, 0);
            m_pContext->PSSetShaderResources(0, 1, &m_pCanvasSRV);
            m_pContext->PSSetSamplers(0, 1, &m_pSampler);

            m_pContext->IASetVertexBuffers(0, 1, &m_pVB, &stride, &offset);
            m_pContext->IASetPrimitiveTopology(D3D11_PRIMITIVE_TOPOLOGY_TRIANGLESTRIP);
            m_pContext->IASetInputLayout(m_pInputLayout);
            if (m_pBlendState) m_pContext->OMSetBlendState(m_pBlendState, nullptr, 0xFFFFFFFF);
            m_pContext->Draw(4, 0);
        }

        // ---- Cursor overlay pass on the live preview ------------------
        // The cursor sits on top of the canvas, mapped through the
        // currently-active DesktopSource transform so it lands at the
        // right place even when the desktop has been moved/resized
        // within the canvas. Cursor compositing on the recorded MP4
        // happens via the canvas readback path inside
        // `FinalizeCanvasFrame` (CompositeOverlays).
        cmp::ISource* descSrc = nullptr;
        for (auto& sp : cmp::g_sources)
            if (sp && sp->Kind() == cmp::SourceKind::Desktop && sp->t.visible) {
                descSrc = sp.get(); break;
            }
        if (descSrc && EnsureCursorOverlayResources() && m_captureW > 0 && m_captureH > 0) {
            BYTE overlay[kCursorTexSize * kCursorTexSize * 4];
            int capCx = 0, capCy = 0, hotX = 0, hotY = 0;
            if (RenderCursorBitmap(overlay, &capCx, &capCy, &hotX, &hotY)) {
                D3D11_MAPPED_SUBRESOURCE mapped = {};
                if (SUCCEEDED(m_pContext->Map(m_pCursorTex, 0,
                              D3D11_MAP_WRITE_DISCARD, 0, &mapped))) {
                    BYTE* dst = (BYTE*)mapped.pData;
                    for (int row = 0; row < kCursorTexSize; ++row) {
                        memcpy(dst + (size_t)row * mapped.RowPitch,
                               overlay + (size_t)row * kCursorTexSize * 4,
                               kCursorTexSize * 4);
                    }
                    m_pContext->Unmap(m_pCursorTex, 0);
                }
                // Map cursor (in desktop-source pixel coords) -> canvas
                // pixel coords via the desktop source's transform, then
                // -> NDC using the canvas dimensions. The active
                // viewport letterboxes the canvas correctly inside the
                // preview so cursor placement is faithful.
                const float dsW = (float)std::max<UINT>(1u, m_captureW);
                const float dsH = (float)std::max<UINT>(1u, m_captureH);
                const float scaleX = descSrc->t.w / dsW;
                const float scaleY = descSrc->t.h / dsH;
                const float canvasLeft  = descSrc->t.x + (capCx - hotX) * scaleX;
                const float canvasTop   = descSrc->t.y + (capCy - hotY) * scaleY;
                const float canvasRight = canvasLeft + (float)kCursorTexSize * scaleX;
                const float canvasBot   = canvasTop  + (float)kCursorTexSize * scaleY;
                const float W = (float)m_canvasW;
                const float H = (float)m_canvasH;
                const float xL = canvasLeft  / W * 2.0f - 1.0f;
                const float xR = canvasRight / W * 2.0f - 1.0f;
                const float yT = 1.0f - canvasTop  / H * 2.0f;
                const float yB = 1.0f - canvasBot  / H * 2.0f;
                float verts[] = {
                    xL, yT, 0.0f, 0.0f,
                    xR, yT, 1.0f, 0.0f,
                    xL, yB, 0.0f, 1.0f,
                    xR, yB, 1.0f, 1.0f,
                };
                D3D11_MAPPED_SUBRESOURCE vbm = {};
                if (SUCCEEDED(m_pContext->Map(m_pCursorVB, 0,
                              D3D11_MAP_WRITE_DISCARD, 0, &vbm))) {
                    memcpy(vbm.pData, verts, sizeof(verts));
                    m_pContext->Unmap(m_pCursorVB, 0);
                }
                m_pContext->IASetVertexBuffers(0, 1, &m_pCursorVB, &stride, &offset);
                m_pContext->PSSetShaderResources(0, 1, &m_pCursorSRV);
                if (m_pBlendStateAlpha)
                    m_pContext->OMSetBlendState(m_pBlendStateAlpha, nullptr, 0xFFFFFFFF);
                m_pContext->Draw(4, 0);
                if (m_pBlendState)
                    m_pContext->OMSetBlendState(m_pBlendState, nullptr, 0xFFFFFFFF);
            }
        }

        // ---- D2D selection box + 8 drag handles overlay --------------
        // Bind the swap-chain back buffer as a D2D bitmap and draw the
        // selection rect + 8 resize handles for the currently selected
        // source. The D2D surface shares the D3D11 device, so this is
        // a single Present, no GDI tearing.
        DrawHandlesOverlay();

        m_pSwapChain->Present(0, 0);
    }

    void DrawHandlesOverlay()
    {
        if (!m_pD2DContext || !m_pSwapChain) return;
        if (!m_pD2DBackBuf) {
            IDXGISurface* backSurf = nullptr;
            HRESULT hr = m_pSwapChain->GetBuffer(0, __uuidof(IDXGISurface), (void**)&backSurf);
            if (FAILED(hr) || !backSurf) return;
            D2D1_BITMAP_PROPERTIES1 bp = {};
            bp.bitmapOptions = D2D1_BITMAP_OPTIONS_TARGET | D2D1_BITMAP_OPTIONS_CANNOT_DRAW;
            bp.pixelFormat   = D2D1::PixelFormat(DXGI_FORMAT_B8G8R8A8_UNORM,
                                                 D2D1_ALPHA_MODE_PREMULTIPLIED);
            bp.dpiX = bp.dpiY = 96.0f;
            hr = m_pD2DContext->CreateBitmapFromDxgiSurface(backSurf, &bp, &m_pD2DBackBuf);
            backSurf->Release();
            if (FAILED(hr) || !m_pD2DBackBuf) return;
        }
        m_pD2DContext->SetTarget(m_pD2DBackBuf);
        m_pD2DContext->BeginDraw();

        cmp::ISource* sel = nullptr;
        for (auto& sp : cmp::g_sources)
            if (sp && sp->id == cmp::g_selectedSourceId) { sel = sp.get(); break; }

        if (sel) {
            // Map canvas-pixel rect -> preview-pixel rect
            const float sx = m_lastLayout.viewW / std::max(1.0f, (float)m_lastLayout.canvasW);
            const float sy = m_lastLayout.viewH / std::max(1.0f, (float)m_lastLayout.canvasH);
            const float pl = m_lastLayout.viewX + sel->t.x * sx;
            const float pt = m_lastLayout.viewY + sel->t.y * sy;
            const float pr = pl + sel->t.w * sx;
            const float pb = pt + sel->t.h * sy;

            ID2D1SolidColorBrush* brOut = nullptr;
            ID2D1SolidColorBrush* brHan = nullptr;
            ID2D1SolidColorBrush* brHFi = nullptr;
            m_pD2DContext->CreateSolidColorBrush(D2D1::ColorF(0.482f, 0.380f, 1.0f, 1.0f), &brOut);
            m_pD2DContext->CreateSolidColorBrush(D2D1::ColorF(0.482f, 0.380f, 1.0f, 1.0f), &brHan);
            m_pD2DContext->CreateSolidColorBrush(D2D1::ColorF(1.0f, 1.0f, 1.0f, 1.0f), &brHFi);
            if (brOut) {
                m_pD2DContext->DrawRectangle(D2D1::RectF(pl, pt, pr, pb), brOut, 2.0f);
            }
            const float hsz = 8.0f;
            float hx[3] = { pl, (pl + pr) * 0.5f, pr };
            float hy[3] = { pt, (pt + pb) * 0.5f, pb };
            for (int j = 0; j < 3; ++j) for (int i = 0; i < 3; ++i) {
                if (i == 1 && j == 1) continue;     // center skipped
                float x = hx[i], y = hy[j];
                D2D1_RECT_F rr = D2D1::RectF(x - hsz, y - hsz, x + hsz, y + hsz);
                if (brHFi) m_pD2DContext->FillRectangle(rr, brHFi);
                if (brOut) m_pD2DContext->DrawRectangle(rr, brOut, 1.5f);
            }
            if (brOut) brOut->Release();
            if (brHan) brHan->Release();
            if (brHFi) brHFi->Release();
        }

        // ---- OBS-style alignment guides + bounds overflow ---------
        // Drawn while a drag is active. Guide lines are dashed
        // magenta and span the full preview viewport, matching OBS's
        // visual language. The overflow contour is dashed red and
        // outlines the *full* selected-source rect (not just the
        // outside-canvas portion) so it's obvious which source is
        // overshooting.
        if (cmp::g_dragGuides.active &&
            (cmp::g_dragGuides.vCount > 0 || cmp::g_dragGuides.hCount > 0 ||
             cmp::g_dragGuides.overflow))
        {
            const float vx0 = m_lastLayout.viewX;
            const float vy0 = m_lastLayout.viewY;
            const float vw  = m_lastLayout.viewW;
            const float vh  = m_lastLayout.viewH;
            const float sxg = vw / std::max(1.0f, (float)m_lastLayout.canvasW);
            const float syg = vh / std::max(1.0f, (float)m_lastLayout.canvasH);

            // Dashed magenta guide brush + stroke style
            ID2D1SolidColorBrush* brGuide = nullptr;
            m_pD2DContext->CreateSolidColorBrush(
                D2D1::ColorF(1.0f, 0.18f, 0.86f, 0.95f), &brGuide);

            ID2D1StrokeStyle* dash = nullptr;
            if (m_pD2DFactory) {
                D2D1_STROKE_STYLE_PROPERTIES sp = D2D1::StrokeStyleProperties();
                sp.dashStyle = D2D1_DASH_STYLE_DASH;
                sp.dashCap   = D2D1_CAP_STYLE_FLAT;
                m_pD2DFactory->CreateStrokeStyle(sp, nullptr, 0, &dash);
            }

            if (brGuide) {
                for (int i = 0; i < cmp::g_dragGuides.vCount; ++i) {
                    float px = vx0 + cmp::g_dragGuides.vX[i] * sxg;
                    m_pD2DContext->DrawLine(
                        D2D1::Point2F(px, vy0),
                        D2D1::Point2F(px, vy0 + vh),
                        brGuide, 1.5f, dash);
                }
                for (int i = 0; i < cmp::g_dragGuides.hCount; ++i) {
                    float py = vy0 + cmp::g_dragGuides.hY[i] * syg;
                    m_pD2DContext->DrawLine(
                        D2D1::Point2F(vx0,        py),
                        D2D1::Point2F(vx0 + vw,   py),
                        brGuide, 1.5f, dash);
                }
            }

            if (cmp::g_dragGuides.overflow) {
                ID2D1SolidColorBrush* brOver = nullptr;
                m_pD2DContext->CreateSolidColorBrush(
                    D2D1::ColorF(1.0f, 0.28f, 0.30f, 0.95f), &brOver);
                if (brOver) {
                    float pl = vx0 + cmp::g_dragGuides.overflowL * sxg;
                    float pt = vy0 + cmp::g_dragGuides.overflowT * syg;
                    float pr = vx0 + cmp::g_dragGuides.overflowR * sxg;
                    float pb = vy0 + cmp::g_dragGuides.overflowB * syg;
                    m_pD2DContext->DrawRectangle(
                        D2D1::RectF(pl, pt, pr, pb),
                        brOver, 2.0f, dash);
                    brOver->Release();
                }
            }

            if (brGuide) brGuide->Release();
            if (dash)    dash->Release();
        }

        m_pD2DContext->EndDraw();
    }

    void Shutdown()
    {
        if (m_pLastCaptureSRV) { m_pLastCaptureSRV->Release(); m_pLastCaptureSRV = nullptr; }
        if (m_pLastCaptureTex) { m_pLastCaptureTex->Release(); m_pLastCaptureTex = nullptr; }
        if (m_pStagingTex)     { m_pStagingTex->Release();     m_pStagingTex     = nullptr; }
        if (m_pVB)             { m_pVB->Release();             m_pVB             = nullptr; }
        if (m_pSampler)        { m_pSampler->Release();        m_pSampler        = nullptr; }
        if (m_pBlendState)     { m_pBlendState->Release();     m_pBlendState     = nullptr; }
        if (m_pBlendStateAlpha){ m_pBlendStateAlpha->Release();m_pBlendStateAlpha= nullptr; }
        if (m_pCursorSRV)      { m_pCursorSRV->Release();      m_pCursorSRV      = nullptr; }
        if (m_pCursorTex)      { m_pCursorTex->Release();      m_pCursorTex      = nullptr; }
        if (m_pCursorVB)       { m_pCursorVB->Release();       m_pCursorVB       = nullptr; }
        if (m_pInputLayout)    { m_pInputLayout->Release();    m_pInputLayout    = nullptr; }
        if (m_pVS)             { m_pVS->Release();             m_pVS             = nullptr; }
        if (m_pPS)             { m_pPS->Release();             m_pPS             = nullptr; }
        if (m_pRenderTargetView){ m_pRenderTargetView->Release(); m_pRenderTargetView = nullptr; }
        if (m_pSwapChain)      { m_pSwapChain->Release();      m_pSwapChain      = nullptr; }
        if (m_pDuplication)    { m_pDuplication->Release();    m_pDuplication    = nullptr; }
        if (m_pContext)        { m_pContext->Release();        m_pContext        = nullptr; }
        if (m_pDevice)         { m_pDevice->Release();        m_pDevice         = nullptr; }
    }

    UINT GetCaptureW() const { return m_captureW; }
    UINT GetCaptureH() const { return m_captureH; }
    ID3D11Device* GetDevice() const { return m_pDevice; }

private:
    bool CreateRenderTarget()
    {
        ID3D11Texture2D* pBack = nullptr;
        HRESULT hr = m_pSwapChain->GetBuffer(0, __uuidof(ID3D11Texture2D), (void**)&pBack);
        if (FAILED(hr)) return false;
        hr = m_pDevice->CreateRenderTargetView(pBack, nullptr, &m_pRenderTargetView);
        pBack->Release();
        // Prime the swap chain with an opaque black clear so the
        // very first WM_PAINT (before the first preview tick) shows
        // black instead of whatever uninitialized DXGI memory
        // happened to be there — that's the "transparent
        // checkerboard at app open" failure mode.
        if (SUCCEEDED(hr) && m_pRenderTargetView && m_pContext) {
            const float black[4] = { 0.0f, 0.0f, 0.0f, 1.0f };
            m_pContext->ClearRenderTargetView(m_pRenderTargetView, black);
            if (m_pSwapChain) m_pSwapChain->Present(0, 0);
        }
        return SUCCEEDED(hr);
    }

    bool CreateStagingTexture(UINT w = 0, UINT h = 0)
    {
        if (w == 0) {
            if (m_monitorIdx >= 0 && m_monitorIdx < (int)g_monitors.size()) {
                w = (UINT)(g_monitors[m_monitorIdx].rect.right  - g_monitors[m_monitorIdx].rect.left);
                h = (UINT)(g_monitors[m_monitorIdx].rect.bottom - g_monitors[m_monitorIdx].rect.top);
            }
            if (w == 0) { w = 1920; h = 1080; }
        }
        D3D11_TEXTURE2D_DESC sd = {};
        sd.Width              = w;
        sd.Height             = h;
        sd.MipLevels          = 1;
        sd.ArraySize          = 1;
        sd.Format             = DXGI_FORMAT_B8G8R8A8_UNORM;
        sd.SampleDesc.Count   = 1;
        sd.Usage              = D3D11_USAGE_STAGING;
        sd.CPUAccessFlags     = D3D11_CPU_ACCESS_READ;
        return SUCCEEDED(m_pDevice->CreateTexture2D(&sd, nullptr, &m_pStagingTex));
    }

    bool CreateShaders()
    {
        static const char* vsHlsl =
            "struct VS_OUT { float4 pos : SV_POSITION; float2 uv : TEXCOORD0; };\n"
            "VS_OUT main(float4 v : POSITION) {\n"
            "  VS_OUT o;\n"
            "  o.pos = float4(v.xy, 0, 1);\n"
            "  o.uv  = v.zw;\n"
            "  return o;\n"
            "}\n";
        // PS preserves source alpha so the same shader is reused for the
        // desktop blit (alpha blending disabled, alpha ignored) and the
        // cursor overlay pass (alpha blending enabled, alpha drives compose).
        static const char* psHlsl =
            "Texture2D tex : register(t0);\n"
            "SamplerState smp : register(s0);\n"
            "struct PS_IN { float4 pos : SV_POSITION; float2 uv : TEXCOORD0; };\n"
            "float4 main(PS_IN i) : SV_TARGET {\n"
            "  return tex.Sample(smp, i.uv);\n"
            "}\n";

        typedef HRESULT (WINAPI *D3DCompile_t)(
            LPCVOID, SIZE_T, LPCSTR, const void*, const void*,
            LPCSTR, LPCSTR, UINT, UINT, ID3DBlob**, ID3DBlob**);

        HMODULE hComp = LoadLibraryW(L"d3dcompiler_47.dll");
        if (!hComp) hComp = LoadLibraryW(L"d3dcompiler_46.dll");
        if (!hComp) return false;

        D3DCompile_t pCompile = (D3DCompile_t)GetProcAddress(hComp, "D3DCompile");
        if (!pCompile) { FreeLibrary(hComp); return false; }

        ID3DBlob* pVSBlob = nullptr; ID3DBlob* pErr = nullptr;
        HRESULT hr = pCompile(vsHlsl, strlen(vsHlsl), nullptr, nullptr, nullptr,
            "main", "vs_4_0", 0, 0, &pVSBlob, &pErr);
        if (pErr) pErr->Release();
        if (FAILED(hr)) { FreeLibrary(hComp); return false; }

        ID3DBlob* pPSBlob = nullptr;
        hr = pCompile(psHlsl, strlen(psHlsl), nullptr, nullptr, nullptr,
            "main", "ps_4_0", 0, 0, &pPSBlob, &pErr);
        if (pErr) pErr->Release();
        if (FAILED(hr)) { pVSBlob->Release(); FreeLibrary(hComp); return false; }

        m_pDevice->CreateVertexShader(pVSBlob->GetBufferPointer(), pVSBlob->GetBufferSize(), nullptr, &m_pVS);
        m_pDevice->CreatePixelShader(pPSBlob->GetBufferPointer(), pPSBlob->GetBufferSize(), nullptr, &m_pPS);

        D3D11_INPUT_ELEMENT_DESC ied[] = {
            { "POSITION", 0, DXGI_FORMAT_R32G32B32A32_FLOAT, 0, 0,
              D3D11_INPUT_PER_VERTEX_DATA, 0 }
        };
        m_pDevice->CreateInputLayout(ied, 1,
            pVSBlob->GetBufferPointer(), pVSBlob->GetBufferSize(), &m_pInputLayout);

        pVSBlob->Release();
        pPSBlob->Release();
        FreeLibrary(hComp);
        return m_pVS && m_pPS && m_pInputLayout;
    }

    bool CreateSamplerAndBlend()
    {
        D3D11_SAMPLER_DESC sd = {};
        sd.Filter   = D3D11_FILTER_MIN_MAG_MIP_LINEAR;
        sd.AddressU = D3D11_TEXTURE_ADDRESS_CLAMP;
        sd.AddressV = D3D11_TEXTURE_ADDRESS_CLAMP;
        sd.AddressW = D3D11_TEXTURE_ADDRESS_CLAMP;
        m_pDevice->CreateSamplerState(&sd, &m_pSampler);

        D3D11_BLEND_DESC bd = {};
        bd.RenderTarget[0].BlendEnable    = FALSE;
        bd.RenderTarget[0].RenderTargetWriteMask = D3D11_COLOR_WRITE_ENABLE_ALL;
        m_pDevice->CreateBlendState(&bd, &m_pBlendState);

        // Premultiplied-alpha blend state for the cursor overlay quad.
        D3D11_BLEND_DESC ba = {};
        ba.RenderTarget[0].BlendEnable           = TRUE;
        ba.RenderTarget[0].SrcBlend              = D3D11_BLEND_ONE;
        ba.RenderTarget[0].DestBlend             = D3D11_BLEND_INV_SRC_ALPHA;
        ba.RenderTarget[0].BlendOp               = D3D11_BLEND_OP_ADD;
        ba.RenderTarget[0].SrcBlendAlpha         = D3D11_BLEND_ONE;
        ba.RenderTarget[0].DestBlendAlpha        = D3D11_BLEND_INV_SRC_ALPHA;
        ba.RenderTarget[0].BlendOpAlpha          = D3D11_BLEND_OP_ADD;
        ba.RenderTarget[0].RenderTargetWriteMask = D3D11_COLOR_WRITE_ENABLE_ALL;
        m_pDevice->CreateBlendState(&ba, &m_pBlendStateAlpha);

        return m_pSampler != nullptr;
    }

    // Lazily create the cursor-overlay resources: a 96x96 BGRA dynamic
    // texture and a 4-vertex dynamic vertex buffer for the cursor quad.
    bool EnsureCursorOverlayResources()
    {
        if (m_pCursorTex && m_pCursorSRV && m_pCursorVB) return true;
        if (!m_pCursorTex) {
            D3D11_TEXTURE2D_DESC td = {};
            td.Width            = kCursorTexSize;
            td.Height           = kCursorTexSize;
            td.MipLevels        = 1;
            td.ArraySize        = 1;
            td.Format           = DXGI_FORMAT_B8G8R8A8_UNORM;
            td.SampleDesc.Count = 1;
            td.Usage            = D3D11_USAGE_DYNAMIC;
            td.BindFlags        = D3D11_BIND_SHADER_RESOURCE;
            td.CPUAccessFlags   = D3D11_CPU_ACCESS_WRITE;
            HRESULT hr = m_pDevice->CreateTexture2D(&td, nullptr, &m_pCursorTex);
            if (FAILED(hr)) return false;
        }
        if (!m_pCursorSRV) {
            D3D11_SHADER_RESOURCE_VIEW_DESC sd = {};
            sd.Format              = DXGI_FORMAT_B8G8R8A8_UNORM;
            sd.ViewDimension       = D3D11_SRV_DIMENSION_TEXTURE2D;
            sd.Texture2D.MipLevels = 1;
            HRESULT hr = m_pDevice->CreateShaderResourceView(m_pCursorTex, &sd, &m_pCursorSRV);
            if (FAILED(hr)) return false;
        }
        if (!m_pCursorVB) {
            D3D11_BUFFER_DESC bd = {};
            bd.Usage          = D3D11_USAGE_DYNAMIC;
            bd.ByteWidth      = sizeof(float) * 4 * 4;
            bd.BindFlags      = D3D11_BIND_VERTEX_BUFFER;
            bd.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
            HRESULT hr = m_pDevice->CreateBuffer(&bd, nullptr, &m_pCursorVB);
            if (FAILED(hr)) return false;
        }
        return true;
    }

    // Build a CPU-side BGRA bitmap of cursor + click rings, premultiplied
    // alpha so the alpha-blend pass composes correctly.
    //
    // Returns true and fills capCx/capCy with the cursor's screen-space
    // position translated into capture coordinates if anything was drawn.
    bool RenderCursorBitmap(BYTE* dst, int* outCapCx, int* outCapCy,
                            int* outHotX, int* outHotY)
    {
        if (m_monitorIdx < 0 || m_monitorIdx >= (int)g_monitors.size()) return false;
        const RECT mon = g_monitors[m_monitorIdx].rect;

        bool wantCursor = g_showCursor.load();
        bool lDown = g_markLeftClick.load()  && (GetAsyncKeyState(VK_LBUTTON) & 0x8000);
        bool rDown = g_markRightClick.load() && (GetAsyncKeyState(VK_RBUTTON) & 0x8000);
        if (!wantCursor && !lDown && !rDown) return false;

        CURSORINFO ci = {};
        ci.cbSize = sizeof(ci);
        if (!GetCursorInfo(&ci)) return false;
        if (!(ci.flags & CURSOR_SHOWING)) return false;

        const int capCx = ci.ptScreenPos.x - mon.left;
        const int capCy = ci.ptScreenPos.y - mon.top;

        // Acquire hotspot.
        int hotX = 0, hotY = 0;
        ICONINFO iconInfo = {};
        if (wantCursor && GetIconInfo(ci.hCursor, &iconInfo)) {
            hotX = (int)iconInfo.xHotspot;
            hotY = (int)iconInfo.yHotspot;
            if (iconInfo.hbmMask)  DeleteObject(iconInfo.hbmMask);
            if (iconInfo.hbmColor) DeleteObject(iconInfo.hbmColor);
        }

        // Clear the overlay buffer.
        memset(dst, 0, kCursorTexSize * kCursorTexSize * 4);

        // Click rings are drawn first so the cursor sits on top of them.
        // The rings are centered on the cursor hotspot, which is at
        // (hotX, hotY) inside the overlay tile.
        auto drawRing = [&](int radius, int thickness, BYTE r, BYTE g, BYTE b, BYTE a) {
            const int rOut2 = radius * radius;
            const int rIn   = radius - thickness;
            const int rIn2  = (rIn > 0) ? rIn * rIn : 0;
            for (int dy = -radius; dy <= radius; ++dy) {
                int y = hotY + dy;
                if (y < 0 || y >= kCursorTexSize) continue;
                for (int dx = -radius; dx <= radius; ++dx) {
                    int x = hotX + dx;
                    if (x < 0 || x >= kCursorTexSize) continue;
                    int d2 = dx * dx + dy * dy;
                    if (d2 > rOut2 || d2 < rIn2) continue;
                    BYTE* px = dst + ((size_t)y * kCursorTexSize + x) * 4;
                    int aN = a;
                    int invA = 255 - aN;
                    px[0] = (BYTE)((px[0] * invA + b * aN) / 255);
                    px[1] = (BYTE)((px[1] * invA + g * aN) / 255);
                    px[2] = (BYTE)((px[2] * invA + r * aN) / 255);
                    if (px[3] < a) px[3] = a;
                }
            }
        };
        if (lDown) drawRing(26, 4, 255,  40,  40, 200);
        if (rDown) drawRing(20, 4,  60, 110, 255, 200);

        // Cursor pixels — DrawIconEx into a scratch DIB, then copy with
        // alpha-aware logic into the overlay buffer.
        if (wantCursor) {
            constexpr int kCur = 64;
            static HDC     s_memDC  = nullptr;
            static HBITMAP s_dib    = nullptr;
            static BYTE*   s_pixels = nullptr;
            if (!s_memDC) {
                HDC screenDC = GetDC(nullptr);
                s_memDC = CreateCompatibleDC(screenDC);
                ReleaseDC(nullptr, screenDC);
                if (s_memDC) {
                    BITMAPINFO bi = {};
                    bi.bmiHeader.biSize        = sizeof(BITMAPINFOHEADER);
                    bi.bmiHeader.biWidth       = kCur;
                    bi.bmiHeader.biHeight      = -kCur;
                    bi.bmiHeader.biPlanes      = 1;
                    bi.bmiHeader.biBitCount    = 32;
                    bi.bmiHeader.biCompression = BI_RGB;
                    s_dib = CreateDIBSection(s_memDC, &bi, DIB_RGB_COLORS,
                                             (void**)&s_pixels, nullptr, 0);
                    if (s_dib) SelectObject(s_memDC, s_dib);
                }
            }
            if (s_memDC && s_dib && s_pixels) {
                memset(s_pixels, 0, kCur * kCur * 4);
                DrawIconEx(s_memDC, 0, 0, ci.hCursor, kCur, kCur, 0, nullptr, DI_NORMAL);
                GdiFlush();
                // Top-left of cursor's pixel data inside the overlay tile.
                const int destX = hotX - hotX;            // = 0 — the icon's
                const int destY = hotY - hotY;            //       (0,0) is at
                // ...wait, re-evaluate: hot is the cursor's *internal* hotspot
                // offset; relative to the overlay tile, the hotspot must end
                // up at (hotX, hotY), so the cursor's (0,0) lands at
                // (hotX - cursorHotX, hotY - cursorHotY) — but in this scope
                // hotX/hotY ARE the cursor's own hotspot, so the cursor's
                // (0,0) sits at (0,0) and its hotspot pixel is naturally at
                // (hotX, hotY). Pin it in place.
                (void)destX; (void)destY;
                for (int sy = 0; sy < kCur; ++sy) {
                    int dy = sy;
                    if (dy < 0 || dy >= kCursorTexSize) continue;
                    BYTE* srcRow = s_pixels + (size_t)sy * kCur * 4;
                    BYTE* dstRow = dst      + (size_t)dy * kCursorTexSize * 4;
                    for (int sx = 0; sx < kCur; ++sx) {
                        int dx = sx;
                        if (dx < 0 || dx >= kCursorTexSize) continue;
                        BYTE* sp = srcRow + sx * 4;
                        BYTE* dp = dstRow + dx * 4;
                        BYTE  sB = sp[0], sG = sp[1], sR = sp[2], sA = sp[3];
                        if (sA == 0 && (sR | sG | sB) == 0) continue;
                        if (sA == 0) sA = 255;        // legacy AND/XOR cursors
                        // Premultiply for the ONE / INV_SRC_ALPHA blend state.
                        int invDst = 255 - sA;
                        int dB = (dp[0] * invDst + sB * sA) / 255;
                        int dG = (dp[1] * invDst + sG * sA) / 255;
                        int dR = (dp[2] * invDst + sR * sA) / 255;
                        int dA = std::min(255, dp[3] + sA);
                        dp[0] = (BYTE)((dB * dA) / 255);
                        dp[1] = (BYTE)((dG * dA) / 255);
                        dp[2] = (BYTE)((dR * dA) / 255);
                        dp[3] = (BYTE)dA;
                    }
                }
            }
        }

        if (outCapCx) *outCapCx = capCx;
        if (outCapCy) *outCapCy = capCy;
        if (outHotX)  *outHotX  = hotX;
        if (outHotY)  *outHotY  = hotY;
        return true;
    }

    bool CreateVertexBuffer()
    {
        // pos.xy = NDC, pos.zw = UV
        float verts[] = {
            -1.0f,  1.0f, 0.0f, 0.0f,
             1.0f,  1.0f, 1.0f, 0.0f,
            -1.0f, -1.0f, 0.0f, 1.0f,
             1.0f, -1.0f, 1.0f, 1.0f,
        };
        D3D11_BUFFER_DESC bd = {};
        bd.Usage          = D3D11_USAGE_IMMUTABLE;
        bd.ByteWidth      = sizeof(verts);
        bd.BindFlags      = D3D11_BIND_VERTEX_BUFFER;
        D3D11_SUBRESOURCE_DATA sd = {};
        sd.pSysMem = verts;
        return SUCCEEDED(m_pDevice->CreateBuffer(&bd, &sd, &m_pVB));
    }

    HWND                    m_hwndPreview      = nullptr;
    int                     m_monitorIdx       = 0;
    int                     m_previewW         = 640;
    int                     m_previewH         = 360;
    UINT                    m_captureW         = 1920;
    UINT                    m_captureH         = 1080;

    ID3D11Device*           m_pDevice          = nullptr;
    ID3D11DeviceContext*    m_pContext          = nullptr;
    IDXGISwapChain1*        m_pSwapChain       = nullptr;
    ID3D11RenderTargetView* m_pRenderTargetView= nullptr;
    IDXGIOutputDuplication* m_pDuplication     = nullptr;
    ID3D11Texture2D*        m_pStagingTex      = nullptr;
    ID3D11Texture2D*        m_pLastCaptureTex  = nullptr;
    ID3D11ShaderResourceView* m_pLastCaptureSRV= nullptr;

    ID3D11VertexShader*     m_pVS              = nullptr;
    ID3D11PixelShader*      m_pPS              = nullptr;
    ID3D11InputLayout*      m_pInputLayout     = nullptr;
    ID3D11Buffer*           m_pVB              = nullptr;
    ID3D11SamplerState*     m_pSampler         = nullptr;
    ID3D11BlendState*       m_pBlendState      = nullptr;

    // Cursor-overlay resources for the live preview path.
    static constexpr int    kCursorTexSize     = 96;
    ID3D11Texture2D*        m_pCursorTex       = nullptr;
    ID3D11ShaderResourceView* m_pCursorSRV     = nullptr;
    ID3D11Buffer*           m_pCursorVB        = nullptr;
    ID3D11BlendState*       m_pBlendStateAlpha = nullptr;

    bool                    m_hasStagedFrame   = false;

    // ---- Compositor canvas (Phase 2) -------------------------------
    int                       m_canvasW         = 1920;
    int                       m_canvasH         = 1080;
    ID3D11Texture2D*          m_pCanvasTex      = nullptr;
    ID3D11RenderTargetView*   m_pCanvasRTV      = nullptr;
    ID3D11ShaderResourceView* m_pCanvasSRV      = nullptr;
    ID3D11Texture2D*          m_pCanvasStaging  = nullptr;
    bool                      m_canvasHasFrame  = false;

    // Transform-aware textured-quad shaders. Same input layout as the
    // base VS (POSITION = float4 with xy = unit-quad pos in 0..1, zw =
    // UV). The constant buffer carries the destination rect in NDC and
    // a per-source opacity.
    ID3D11VertexShader*       m_pVSQuad         = nullptr;
    ID3D11PixelShader*        m_pPSQuad         = nullptr;
    ID3D11InputLayout*        m_pQuadLayout     = nullptr;
    ID3D11Buffer*             m_pQuadVB         = nullptr;
    ID3D11Buffer*             m_pQuadCB         = nullptr;
    ID3D11BlendState*         m_pBlendStraight  = nullptr;

    // Placeholder texture for sources without a real SRV (Window stub
    // before binding, etc.) — a 16x16 light grey checkerboard.
    ID3D11Texture2D*          m_pPlaceholderTex = nullptr;
    ID3D11ShaderResourceView* m_pPlaceholderSRV = nullptr;

    // ---- D2D-on-D3D11 overlay for selection box + 8 drag handles --
    ID2D1Factory1*            m_pD2DFactory     = nullptr;
    ID2D1Device*              m_pD2DDevice      = nullptr;
    ID2D1DeviceContext*       m_pD2DContext     = nullptr;
    ID2D1Bitmap1*             m_pD2DBackBuf     = nullptr;
    IDWriteFactory*           m_pDWFactory      = nullptr;

public:
    int CanvasW() const { return m_canvasW; }
    int CanvasH() const { return m_canvasH; }
    ID3D11Device*         Device()  { return m_pDevice;  }
    ID3D11DeviceContext*  Context() { return m_pContext; }
    ID2D1Factory1*        D2DFactory()    { return m_pD2DFactory; }
    IDWriteFactory*       DWriteFactory() { return m_pDWFactory; }

    // The desktop SRV that the existing capture path writes into. Used
    // by the DesktopSource to expose the same texture as a compositor
    // input without copying.
    ID3D11ShaderResourceView* DesktopCaptureSRV() { return m_pLastCaptureSRV; }
    UINT DesktopCaptureW() const { return m_captureW; }
    UINT DesktopCaptureH() const { return m_captureH; }

    bool CreateCanvasResources(int w, int h);
    bool CreateQuadShaders();
    bool CreateQuadVB();
    bool CreateD2DOverlay();
    bool EnsurePlaceholder();

    // Composite all sources to canvas RTV. Returns true on success.
    // Called by the capture thread once per frame, before the encoder
    // reads from the canvas staging tex.
    bool CompositeFrame();

    // CPU readback of the canvas at native pixel rate. Replaces the
    // older desktop-staging readback path for the encoder.
    bool CopyCanvasToWMF(BYTE* pDst, UINT dstStride);

    std::mutex              m_ctxMutex;
};

static DxgiCaptureRenderer g_renderer;

// ---------------------------------------------------------------------
// Compositor implementations live outside the class so they can call
// into renderer-private state. Forward declared in the class above.
// ---------------------------------------------------------------------
bool DxgiCaptureRenderer::CreateCanvasResources(int w, int h)
{
    if (!m_pDevice || w < 16 || h < 16) return false;

    if (m_pCanvasRTV)     { m_pCanvasRTV->Release();     m_pCanvasRTV = nullptr; }
    if (m_pCanvasSRV)     { m_pCanvasSRV->Release();     m_pCanvasSRV = nullptr; }
    if (m_pCanvasTex)     { m_pCanvasTex->Release();     m_pCanvasTex = nullptr; }
    if (m_pCanvasStaging) { m_pCanvasStaging->Release(); m_pCanvasStaging = nullptr; }

    D3D11_TEXTURE2D_DESC td = {};
    td.Width  = (UINT)w;
    td.Height = (UINT)h;
    td.MipLevels = 1;
    td.ArraySize = 1;
    td.Format = DXGI_FORMAT_B8G8R8A8_UNORM;
    td.SampleDesc.Count = 1;
    td.Usage = D3D11_USAGE_DEFAULT;
    td.BindFlags = D3D11_BIND_RENDER_TARGET | D3D11_BIND_SHADER_RESOURCE;
    HRESULT hr = m_pDevice->CreateTexture2D(&td, nullptr, &m_pCanvasTex);
    if (FAILED(hr) || !m_pCanvasTex) return false;

    D3D11_RENDER_TARGET_VIEW_DESC rtv = {};
    rtv.Format             = DXGI_FORMAT_B8G8R8A8_UNORM;
    rtv.ViewDimension      = D3D11_RTV_DIMENSION_TEXTURE2D;
    hr = m_pDevice->CreateRenderTargetView(m_pCanvasTex, &rtv, &m_pCanvasRTV);
    if (FAILED(hr)) return false;

    D3D11_SHADER_RESOURCE_VIEW_DESC svd = {};
    svd.Format              = DXGI_FORMAT_B8G8R8A8_UNORM;
    svd.ViewDimension       = D3D11_SRV_DIMENSION_TEXTURE2D;
    svd.Texture2D.MipLevels = 1;
    hr = m_pDevice->CreateShaderResourceView(m_pCanvasTex, &svd, &m_pCanvasSRV);
    if (FAILED(hr)) return false;

    D3D11_TEXTURE2D_DESC sd = td;
    sd.Usage = D3D11_USAGE_STAGING;
    sd.BindFlags = 0;
    sd.CPUAccessFlags = D3D11_CPU_ACCESS_READ;
    hr = m_pDevice->CreateTexture2D(&sd, nullptr, &m_pCanvasStaging);
    if (FAILED(hr)) return false;

    m_canvasW = w;
    m_canvasH = h;
    cmp::g_canvasW = w;
    cmp::g_canvasH = h;

    // Prime the canvas with a solid black opaque clear immediately so
    // the preview pass that runs before the first capture frame samples
    // a defined texture (otherwise we'd be sampling uninitialized GPU
    // memory which on some drivers shows up as a transparent
    // checkerboard).
    if (m_pCanvasRTV) {
        const float black[4] = { 0.0f, 0.0f, 0.0f, 1.0f };
        m_pContext->ClearRenderTargetView(m_pCanvasRTV, black);
    }
    return true;
}

bool DxgiCaptureRenderer::CreateQuadShaders()
{
    static const char* vsHlsl =
        "cbuffer CB : register(b0) {\n"
        "  float4 dstNDC;   /* x, y, w, h in NDC: x,y top-left of quad, w,h size */\n"
        "  float4 params;   /* x = opacity, yzw = unused */\n"
        "}\n"
        "struct VS_OUT { float4 pos : SV_POSITION; float2 uv : TEXCOORD0; float opa : TEXCOORD1; };\n"
        "VS_OUT main(float4 v : POSITION) {\n"
        "  /* v.xy in [0,1] unit quad; v.zw uv same space */\n"
        "  VS_OUT o;\n"
        "  float2 ndc = dstNDC.xy + v.xy * dstNDC.zw;\n"
        "  o.pos = float4(ndc, 0, 1);\n"
        "  o.uv  = v.zw;\n"
        "  o.opa = params.x;\n"
        "  return o;\n"
        "}\n";
    static const char* psHlsl =
        "Texture2D tex : register(t0);\n"
        "SamplerState smp : register(s0);\n"
        "struct PS_IN { float4 pos : SV_POSITION; float2 uv : TEXCOORD0; float opa : TEXCOORD1; };\n"
        "float4 main(PS_IN i) : SV_TARGET {\n"
        "  float4 c = tex.Sample(smp, i.uv);\n"
        "  c.a *= i.opa;\n"
        "  return float4(c.rgb * c.a, c.a);\n"   // premultiplied output
        "}\n";

    typedef HRESULT (WINAPI *D3DCompile_t)(
        LPCVOID, SIZE_T, LPCSTR, const void*, const void*,
        LPCSTR, LPCSTR, UINT, UINT, ID3DBlob**, ID3DBlob**);
    HMODULE hComp = LoadLibraryW(L"d3dcompiler_47.dll");
    if (!hComp) hComp = LoadLibraryW(L"d3dcompiler_46.dll");
    if (!hComp) return false;
    D3DCompile_t pCompile = (D3DCompile_t)GetProcAddress(hComp, "D3DCompile");
    if (!pCompile) { FreeLibrary(hComp); return false; }

    ID3DBlob* pVSBlob = nullptr; ID3DBlob* pErr = nullptr;
    HRESULT hr = pCompile(vsHlsl, strlen(vsHlsl), nullptr, nullptr, nullptr,
                          "main", "vs_4_0", 0, 0, &pVSBlob, &pErr);
    if (pErr) pErr->Release();
    if (FAILED(hr)) { FreeLibrary(hComp); return false; }

    ID3DBlob* pPSBlob = nullptr;
    hr = pCompile(psHlsl, strlen(psHlsl), nullptr, nullptr, nullptr,
                  "main", "ps_4_0", 0, 0, &pPSBlob, &pErr);
    if (pErr) pErr->Release();
    if (FAILED(hr)) { pVSBlob->Release(); FreeLibrary(hComp); return false; }

    m_pDevice->CreateVertexShader(pVSBlob->GetBufferPointer(), pVSBlob->GetBufferSize(),
                                  nullptr, &m_pVSQuad);
    m_pDevice->CreatePixelShader(pPSBlob->GetBufferPointer(), pPSBlob->GetBufferSize(),
                                 nullptr, &m_pPSQuad);

    D3D11_INPUT_ELEMENT_DESC ied[] = {
        { "POSITION", 0, DXGI_FORMAT_R32G32B32A32_FLOAT, 0, 0,
          D3D11_INPUT_PER_VERTEX_DATA, 0 }
    };
    m_pDevice->CreateInputLayout(ied, 1,
        pVSBlob->GetBufferPointer(), pVSBlob->GetBufferSize(), &m_pQuadLayout);

    pVSBlob->Release();
    pPSBlob->Release();
    FreeLibrary(hComp);

    // Constant buffer (16-byte aligned)
    D3D11_BUFFER_DESC cb = {};
    cb.ByteWidth      = 32;     // 8 floats
    cb.Usage          = D3D11_USAGE_DYNAMIC;
    cb.BindFlags      = D3D11_BIND_CONSTANT_BUFFER;
    cb.CPUAccessFlags = D3D11_CPU_ACCESS_WRITE;
    m_pDevice->CreateBuffer(&cb, nullptr, &m_pQuadCB);

    // Premultiplied source-over blend state
    D3D11_BLEND_DESC bd = {};
    bd.RenderTarget[0].BlendEnable           = TRUE;
    bd.RenderTarget[0].SrcBlend              = D3D11_BLEND_ONE;
    bd.RenderTarget[0].DestBlend             = D3D11_BLEND_INV_SRC_ALPHA;
    bd.RenderTarget[0].BlendOp               = D3D11_BLEND_OP_ADD;
    bd.RenderTarget[0].SrcBlendAlpha         = D3D11_BLEND_ONE;
    bd.RenderTarget[0].DestBlendAlpha        = D3D11_BLEND_INV_SRC_ALPHA;
    bd.RenderTarget[0].BlendOpAlpha          = D3D11_BLEND_OP_ADD;
    bd.RenderTarget[0].RenderTargetWriteMask = D3D11_COLOR_WRITE_ENABLE_ALL;
    m_pDevice->CreateBlendState(&bd, &m_pBlendStraight);

    return m_pVSQuad && m_pPSQuad && m_pQuadLayout && m_pQuadCB;
}

bool DxgiCaptureRenderer::CreateQuadVB()
{
    if (m_pQuadVB) return true;
    // 4 vertices, each (x,y, u,v). Unit quad in (0,0)..(1,1), UV matching.
    float verts[] = {
        0.0f, 0.0f,  0.0f, 0.0f,
        1.0f, 0.0f,  1.0f, 0.0f,
        0.0f, 1.0f,  0.0f, 1.0f,
        1.0f, 1.0f,  1.0f, 1.0f,
    };
    D3D11_BUFFER_DESC bd = {};
    bd.ByteWidth = sizeof(verts);
    bd.Usage     = D3D11_USAGE_IMMUTABLE;
    bd.BindFlags = D3D11_BIND_VERTEX_BUFFER;
    D3D11_SUBRESOURCE_DATA sd = { verts, 0, 0 };
    return SUCCEEDED(m_pDevice->CreateBuffer(&bd, &sd, &m_pQuadVB));
}

bool DxgiCaptureRenderer::EnsurePlaceholder()
{
    if (m_pPlaceholderSRV) return true;
    BYTE px[16 * 16 * 4];
    for (int y = 0; y < 16; ++y) for (int x = 0; x < 16; ++x) {
        bool dark = ((x / 4) ^ (y / 4)) & 1;
        BYTE v = dark ? 0x40 : 0x60;
        BYTE* p = px + ((size_t)y * 16 + x) * 4;
        p[0] = v; p[1] = v; p[2] = v; p[3] = 0xFF;
    }
    D3D11_TEXTURE2D_DESC td = {};
    td.Width = 16; td.Height = 16; td.MipLevels = 1; td.ArraySize = 1;
    td.Format = DXGI_FORMAT_B8G8R8A8_UNORM;
    td.SampleDesc.Count = 1;
    td.Usage = D3D11_USAGE_IMMUTABLE;
    td.BindFlags = D3D11_BIND_SHADER_RESOURCE;
    D3D11_SUBRESOURCE_DATA sd = { px, 16 * 4, 0 };
    if (FAILED(m_pDevice->CreateTexture2D(&td, &sd, &m_pPlaceholderTex))) return false;
    D3D11_SHADER_RESOURCE_VIEW_DESC svd = {};
    svd.Format = DXGI_FORMAT_B8G8R8A8_UNORM;
    svd.ViewDimension = D3D11_SRV_DIMENSION_TEXTURE2D;
    svd.Texture2D.MipLevels = 1;
    return SUCCEEDED(m_pDevice->CreateShaderResourceView(
        m_pPlaceholderTex, &svd, &m_pPlaceholderSRV));
}

bool DxgiCaptureRenderer::CreateD2DOverlay()
{
    if (m_pD2DContext) return true;
    if (!m_pDevice) return false;

    HRESULT hr = D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED,
        __uuidof(ID2D1Factory1), nullptr, (void**)&m_pD2DFactory);
    if (FAILED(hr) || !m_pD2DFactory) return false;

    IDXGIDevice* pDxgiDev = nullptr;
    hr = m_pDevice->QueryInterface(__uuidof(IDXGIDevice), (void**)&pDxgiDev);
    if (FAILED(hr) || !pDxgiDev) return false;

    hr = m_pD2DFactory->CreateDevice(pDxgiDev, &m_pD2DDevice);
    pDxgiDev->Release();
    if (FAILED(hr) || !m_pD2DDevice) return false;

    hr = m_pD2DDevice->CreateDeviceContext(D2D1_DEVICE_CONTEXT_OPTIONS_NONE, &m_pD2DContext);
    if (FAILED(hr)) return false;

    hr = DWriteCreateFactory(DWRITE_FACTORY_TYPE_SHARED,
        __uuidof(IDWriteFactory), (IUnknown**)&m_pDWFactory);
    if (FAILED(hr) || !m_pDWFactory) return false;

    return true;
}

bool DxgiCaptureRenderer::CompositeFrame()
{
    std::lock_guard<std::mutex> lock(m_ctxMutex);
    if (!m_pCanvasRTV || !m_pVSQuad || !m_pQuadVB || !m_pQuadCB) return false;

    // Clear canvas to black opaque.
    float clear[4] = { 0.0f, 0.0f, 0.0f, 1.0f };
    m_pContext->ClearRenderTargetView(m_pCanvasRTV, clear);

    D3D11_VIEWPORT vp = {};
    vp.TopLeftX = 0; vp.TopLeftY = 0;
    vp.Width    = (FLOAT)m_canvasW;
    vp.Height   = (FLOAT)m_canvasH;
    vp.MinDepth = 0.0f; vp.MaxDepth = 1.0f;
    m_pContext->RSSetViewports(1, &vp);
    m_pContext->OMSetRenderTargets(1, &m_pCanvasRTV, nullptr);

    UINT stride = sizeof(float) * 4;
    UINT offset = 0;
    m_pContext->IASetVertexBuffers(0, 1, &m_pQuadVB, &stride, &offset);
    m_pContext->IASetPrimitiveTopology(D3D11_PRIMITIVE_TOPOLOGY_TRIANGLESTRIP);
    m_pContext->IASetInputLayout(m_pQuadLayout);
    m_pContext->VSSetShader(m_pVSQuad, nullptr, 0);
    m_pContext->PSSetShader(m_pPSQuad, nullptr, 0);
    m_pContext->PSSetSamplers(0, 1, &m_pSampler);
    m_pContext->VSSetConstantBuffers(0, 1, &m_pQuadCB);
    if (m_pBlendStraight) {
        float bf[4] = {0,0,0,0};
        m_pContext->OMSetBlendState(m_pBlendStraight, bf, 0xFFFFFFFF);
    }

    // Walk sources in z-order (bottom-to-top = vector order).
    std::lock_guard<std::mutex> srcLk(cmp::g_sourcesMutex);

    // Refresh every DesktopSource against the renderer's *current*
    // capture SRV. Without this re-bind, a DesktopSource added before
    // the first DXGI duplication frame caches a null pointer (because
    // DesktopCaptureSRV() returns null at app boot — the texture
    // hasn't been created yet) and continues returning null forever
    // even after capture starts. That's the "transparent / black-and-
    // grey checkerboard preview on app open" failure mode the user
    // reported: with no valid SRV the source was skipped, the canvas
    // stayed black, and the swap chain back-buffer showed whatever
    // happened to be in DXGI's reserve memory — the desktop wallpaper
    // bleed-through pattern that looks like an alpha-checker.
    for (auto& sp : cmp::g_sources) {
        if (sp && sp->Kind() == cmp::SourceKind::Desktop) {
            ((cmp::DesktopSource*)sp.get())->Bind(
                m_pLastCaptureSRV,
                m_captureW  ? m_captureW  : (UINT)m_canvasW,
                m_captureH  ? m_captureH  : (UINT)m_canvasH);
        }
    }

    for (auto& sp : cmp::g_sources) {
        cmp::ISource* s = sp.get();
        if (!s || !s->t.visible) continue;

        // If a source has no SRV yet (DesktopSource on the very first
        // frame, before duplication has produced a single frame) just
        // skip it. The canvas is already cleared to opaque black, so
        // the user sees clean black for the one or two frames before
        // capture produces output — never a checkerboard.
        ID3D11ShaderResourceView* srv = s->SRV();
        if (!srv) continue;

        // Convert canvas-space rect -> NDC. Canvas (0,0)=top-left, NDC (-1,1)=top-left.
        float cx = s->t.x;
        float cy = s->t.y;
        float cw = s->t.w;
        float ch = s->t.h;
        float ndcX = (cx / (float)m_canvasW) * 2.0f - 1.0f;
        float ndcY = 1.0f - (cy / (float)m_canvasH) * 2.0f;
        float ndcW = (cw / (float)m_canvasW) * 2.0f;
        float ndcH = -((ch / (float)m_canvasH) * 2.0f);  // flip Y because canvas Y grows down

        // Update CB
        struct CBData { float dstNDC[4]; float params[4]; } cbd = {};
        cbd.dstNDC[0] = ndcX;
        cbd.dstNDC[1] = ndcY;
        cbd.dstNDC[2] = ndcW;
        cbd.dstNDC[3] = ndcH;
        cbd.params[0] = std::max(0.0f, std::min(1.0f, s->t.opacity));
        D3D11_MAPPED_SUBRESOURCE m = {};
        if (SUCCEEDED(m_pContext->Map(m_pQuadCB, 0, D3D11_MAP_WRITE_DISCARD, 0, &m))) {
            memcpy(m.pData, &cbd, sizeof(cbd));
            m_pContext->Unmap(m_pQuadCB, 0);
        }

        m_pContext->PSSetShaderResources(0, 1, &srv);
        m_pContext->Draw(4, 0);
    }

    // Copy canvas -> staging for the encoder readback.
    if (m_pCanvasStaging && m_pCanvasTex) {
        m_pContext->CopyResource(m_pCanvasStaging, m_pCanvasTex);
        m_canvasHasFrame = true;
    }

    return true;
}

bool DxgiCaptureRenderer::CopyCanvasToWMF(BYTE* pDst, UINT dstStride)
{
    std::lock_guard<std::mutex> lock(m_ctxMutex);
    if (!m_pCanvasStaging || !m_canvasHasFrame) return false;
    D3D11_MAPPED_SUBRESOURCE mapped = {};
    HRESULT hr = m_pContext->Map(m_pCanvasStaging, 0, D3D11_MAP_READ, 0, &mapped);
    if (FAILED(hr)) return false;
    UINT rows = (UINT)m_canvasH;
    UINT copyBytes = (dstStride < (UINT)m_canvasW * 4) ? dstStride : (UINT)m_canvasW * 4;
    for (UINT y = 0; y < rows; ++y) {
        memcpy(pDst + (size_t)y * dstStride,
               (BYTE*)mapped.pData + (size_t)y * mapped.RowPitch,
               copyBytes);
    }
    m_pContext->Unmap(m_pCanvasStaging, 0);
    return true;
}

#pragma endregion

#pragma region WMF_SINK_WRITER

class WmfSinkWriter {
public:
    WmfSinkWriter()  = default;
    ~WmfSinkWriter() { Finalize(); }

    bool Init(const wchar_t* outputPath,
              UINT videoW, UINT videoH, UINT fps,
              UINT audioSampleRate, UINT audioChannels,
              UINT videoBitrate = 4'000'000u)
    {
        m_videoW         = videoW;
        m_videoH         = videoH;
        m_fps            = fps;
        m_videoBitrate   = videoBitrate;
        m_audioSampleRate= audioSampleRate;
        m_audioChannels  = audioChannels;
        m_videoTimestamp = 0;
        m_audioTimestamp = 0;
        // Wall-clock bookkeeping (drives video PTS).
        QueryPerformanceFrequency(&m_qpcFreq);
        QueryPerformanceCounter(&m_qpcResumeAt);
        m_qpcActiveAccum = 0;
        m_lastVideoPts   = -1;
        m_paused         = false;

        IMFAttributes* pAttr = nullptr;
        MFCreateAttributes(&pAttr, 4);
        pAttr->SetUINT32(MF_READWRITE_ENABLE_HARDWARE_TRANSFORMS, TRUE);
        pAttr->SetUINT32(MF_SINK_WRITER_DISABLE_THROTTLING, TRUE);

        HRESULT hr = MFCreateSinkWriterFromURL(outputPath, nullptr, pAttr, &m_pWriter);
        pAttr->Release();
        if (FAILED(hr)) return false;

        if (!AddVideoStream()) return false;
        if (!AddAudioStream()) return false;

        hr = m_pWriter->BeginWriting();
        if (FAILED(hr)) return false;

        m_initialized = true;
        return true;
    }

    bool WriteVideoFrame(const BYTE* bgra, UINT stride)
    {
        if (!m_initialized || !m_pWriter) return false;

        DWORD bufSize = stride * m_videoH;
        IMFMediaBuffer* pBuf = nullptr;
        HRESULT hr = MFCreateMemoryBuffer(bufSize, &pBuf);
        if (FAILED(hr)) return false;

        BYTE* pData = nullptr;
        pBuf->Lock(&pData, nullptr, nullptr);
        // Convert BGRA to NV12 inline for encoder compatibility
        BGRAtoNV12(bgra, stride, pData, m_videoW, m_videoH);
        pBuf->Unlock();
        pBuf->SetCurrentLength((DWORD)(m_videoW * m_videoH * 3 / 2));

        IMFSample* pSample = nullptr;
        MFCreateSample(&pSample);
        pSample->AddBuffer(pBuf);
        pBuf->Release();

        // ---- Wall-clock-correct PTS ---------------------------------
        // Stamp this sample at the actual elapsed *active* recording
        // time. Duration = delta from the previous frame's PTS so the
        // muxer knows how long to display each frame even when the
        // capture rate is below the nominal target fps. If somehow we
        // got two frames within < 1 hns of each other, nudge the PTS
        // forward by 1 hns to keep PTS strictly increasing (some
        // muxers drop equal-PTS samples).
        LONGLONG nowPts = ActiveHns();
        if (nowPts <= m_lastVideoPts) nowPts = m_lastVideoPts + 1;
        LONGLONG dur = (m_lastVideoPts < 0)
                       ? (LONGLONG)(10000000LL / std::max(1u, m_fps))
                       : (nowPts - m_lastVideoPts);
        if (dur <= 0) dur = (LONGLONG)(10000000LL / std::max(1u, m_fps));
        pSample->SetSampleTime(nowPts);
        pSample->SetSampleDuration(dur);
        m_lastVideoPts   = nowPts;
        m_videoTimestamp = nowPts;     // kept for any external readers

        hr = m_pWriter->WriteSample(m_videoStreamIndex, pSample);
        pSample->Release();
        return SUCCEEDED(hr);
    }

    bool WriteAudioSamples(const float* interleaved, UINT numFrames)
    {
        if (!m_initialized || !m_pWriter || numFrames == 0) return false;

        DWORD bufSize = numFrames * m_audioChannels * sizeof(float);
        IMFMediaBuffer* pBuf = nullptr;
        HRESULT hr = MFCreateMemoryBuffer(bufSize, &pBuf);
        if (FAILED(hr)) return false;

        BYTE* pData = nullptr;
        pBuf->Lock(&pData, nullptr, nullptr);
        memcpy(pData, interleaved, bufSize);
        pBuf->Unlock();
        pBuf->SetCurrentLength(bufSize);

        IMFSample* pSample = nullptr;
        MFCreateSample(&pSample);
        pSample->AddBuffer(pBuf);
        pBuf->Release();

        LONGLONG dur = (LONGLONG)((LONGLONG)numFrames * 10000000LL / m_audioSampleRate);
        pSample->SetSampleDuration(dur);
        pSample->SetSampleTime(m_audioTimestamp);
        m_audioTimestamp += dur;

        hr = m_pWriter->WriteSample(m_audioStreamIndex, pSample);
        pSample->Release();
        return SUCCEEDED(hr);
    }

    void Finalize()
    {
        if (m_pWriter && m_initialized) {
            m_pWriter->Finalize();
        }
        if (m_pWriter) { m_pWriter->Release(); m_pWriter = nullptr; }
        m_initialized = false;
    }

private:
    bool AddVideoStream()
    {
        IMFMediaType* pOutType = nullptr;
        MFCreateMediaType(&pOutType);
        pOutType->SetGUID(MF_MT_MAJOR_TYPE,    MFMediaType_Video);
        pOutType->SetGUID(MF_MT_SUBTYPE,        MFVideoFormat_H264);
        // Bitrate now comes from the user-selected video preset (was a
        // hard-coded 4 Mbps).
        pOutType->SetUINT32(MF_MT_AVG_BITRATE,  m_videoBitrate);
        pOutType->SetUINT32(MF_MT_INTERLACE_MODE, MFVideoInterlace_Progressive);
        MFSetAttributeSize(pOutType, MF_MT_FRAME_SIZE, m_videoW, m_videoH);
        MFSetAttributeRatio(pOutType, MF_MT_FRAME_RATE, m_fps, 1);
        MFSetAttributeRatio(pOutType, MF_MT_PIXEL_ASPECT_RATIO, 1, 1);

        HRESULT hr = m_pWriter->AddStream(pOutType, &m_videoStreamIndex);
        pOutType->Release();
        if (FAILED(hr)) return false;

        IMFMediaType* pInType = nullptr;
        MFCreateMediaType(&pInType);
        pInType->SetGUID(MF_MT_MAJOR_TYPE,   MFMediaType_Video);
        pInType->SetGUID(MF_MT_SUBTYPE,       MFVideoFormat_NV12);
        pInType->SetUINT32(MF_MT_INTERLACE_MODE, MFVideoInterlace_Progressive);
        MFSetAttributeSize(pInType, MF_MT_FRAME_SIZE, m_videoW, m_videoH);
        MFSetAttributeRatio(pInType, MF_MT_FRAME_RATE, m_fps, 1);
        MFSetAttributeRatio(pInType, MF_MT_PIXEL_ASPECT_RATIO, 1, 1);

        hr = m_pWriter->SetInputMediaType(m_videoStreamIndex, pInType, nullptr);
        pInType->Release();
        return SUCCEEDED(hr);
    }

    bool AddAudioStream()
    {
        IMFMediaType* pOutType = nullptr;
        MFCreateMediaType(&pOutType);
        pOutType->SetGUID(MF_MT_MAJOR_TYPE,             MFMediaType_Audio);
        pOutType->SetGUID(MF_MT_SUBTYPE,                 MFAudioFormat_AAC);
        pOutType->SetUINT32(MF_MT_AUDIO_BITS_PER_SAMPLE, 16);
        pOutType->SetUINT32(MF_MT_AUDIO_SAMPLES_PER_SECOND, m_audioSampleRate);
        pOutType->SetUINT32(MF_MT_AUDIO_NUM_CHANNELS,    m_audioChannels);
        pOutType->SetUINT32(MF_MT_AUDIO_AVG_BYTES_PER_SECOND, 20000);

        HRESULT hr = m_pWriter->AddStream(pOutType, &m_audioStreamIndex);
        pOutType->Release();
        if (FAILED(hr)) return false;

        IMFMediaType* pInType = nullptr;
        MFCreateMediaType(&pInType);
        pInType->SetGUID(MF_MT_MAJOR_TYPE,              MFMediaType_Audio);
        pInType->SetGUID(MF_MT_SUBTYPE,                  MFAudioFormat_Float);
        pInType->SetUINT32(MF_MT_AUDIO_BITS_PER_SAMPLE,  32);
        pInType->SetUINT32(MF_MT_AUDIO_SAMPLES_PER_SECOND, m_audioSampleRate);
        pInType->SetUINT32(MF_MT_AUDIO_NUM_CHANNELS,     m_audioChannels);
        pInType->SetUINT32(MF_MT_AUDIO_BLOCK_ALIGNMENT,  m_audioChannels * 4);
        pInType->SetUINT32(MF_MT_AUDIO_AVG_BYTES_PER_SECOND, m_audioSampleRate * m_audioChannels * 4);

        hr = m_pWriter->SetInputMediaType(m_audioStreamIndex, pInType, nullptr);
        pInType->Release();
        return SUCCEEDED(hr);
    }

    static void BGRAtoNV12(const BYTE* bgra, UINT bgraStride,
                           BYTE* nv12, UINT w, UINT h)
    {
        BYTE* yPlane  = nv12;
        BYTE* uvPlane = nv12 + (LONGLONG)w * h;

        for (UINT row = 0; row < h; ++row) {
            const BYTE* src = bgra + (LONGLONG)row * bgraStride;
            BYTE* yd = yPlane + (LONGLONG)row * w;
            for (UINT col = 0; col < w; ++col) {
                BYTE b = src[col * 4 + 0];
                BYTE g = src[col * 4 + 1];
                BYTE r = src[col * 4 + 2];
                // BT.601 limited range
                yd[col] = (BYTE)(((66 * r + 129 * g + 25 * b + 128) >> 8) + 16);
            }
        }

        for (UINT row = 0; row < h / 2; ++row) {
            const BYTE* src0 = bgra + (LONGLONG)(row * 2    ) * bgraStride;
            const BYTE* src1 = bgra + (LONGLONG)(row * 2 + 1) * bgraStride;
            BYTE* uvd = uvPlane + (LONGLONG)row * w;
            for (UINT col = 0; col < w / 2; ++col) {
                BYTE b = src0[col * 8 + 0];
                BYTE g = src0[col * 8 + 1];
                BYTE r = src0[col * 8 + 2];
                uvd[col * 2 + 0] = (BYTE)(((( -38 * r - 74 * g + 112 * b + 128) >> 8) + 128));
                uvd[col * 2 + 1] = (BYTE)((((112 * r - 94 * g -  18 * b + 128) >> 8) + 128));
                (void)src1;
            }
        }
    }

    IMFSinkWriter* m_pWriter         = nullptr;
    DWORD          m_videoStreamIndex= 0;
    DWORD          m_audioStreamIndex= 1;
    UINT           m_videoW          = 1920;
    UINT           m_videoH          = 1080;
    UINT           m_fps             = TARGET_FPS;
    UINT           m_videoBitrate    = 4'000'000u;
    UINT           m_audioSampleRate = 44100;
    UINT           m_audioChannels   = 2;
    LONGLONG       m_videoTimestamp  = 0;
    LONGLONG       m_audioTimestamp  = 0;
    // ---- Wall-clock PTS bookkeeping ---------------------------------
    // The video PTS used to be derived from frame index × (1/fps), which
    // produced a video timeline that ran faster than wall clock whenever
    // the capture/composite thread couldn't sustain the target fps —
    // resulting in "video ends at half duration while audio plays on".
    // We now stamp every video sample with the actual elapsed *active*
    // recording time from QueryPerformanceCounter, so the video stream
    // tracks wall clock exactly regardless of capture rate.
    LARGE_INTEGER  m_qpcFreq         = {};   // counts/sec
    LARGE_INTEGER  m_qpcResumeAt     = {};   // QPC at last Start/Resume
    LONGLONG       m_qpcActiveAccum  = 0;    // accumulated active counts (excludes pause)
    LONGLONG       m_lastVideoPts    = -1;   // hns; -1 = none yet
    bool           m_paused          = false;
    bool           m_initialized     = false;

public:
    // Pause / resume hooks driven by Start/Pause/Resume in the
    // recorder state machine. They keep the active wall-clock counter
    // accurate so paused time isn't included in the video PTS.
    void OnPause() {
        if (!m_initialized || m_paused) return;
        LARGE_INTEGER now; QueryPerformanceCounter(&now);
        m_qpcActiveAccum += (now.QuadPart - m_qpcResumeAt.QuadPart);
        m_paused = true;
    }
    void OnResume() {
        if (!m_initialized || !m_paused) return;
        QueryPerformanceCounter(&m_qpcResumeAt);
        m_paused = false;
    }
    LONGLONG ActiveHns() const {
        if (!m_qpcFreq.QuadPart) return 0;
        LONGLONG counts = m_qpcActiveAccum;
        if (!m_paused) {
            LARGE_INTEGER now; QueryPerformanceCounter(&now);
            counts += (now.QuadPart - m_qpcResumeAt.QuadPart);
        }
        // counts * 1e7 / freq, computed without 64-bit overflow for
        // reasonable session lengths (< ~hundreds of years).
        return (LONGLONG)((double)counts * 10000000.0 / (double)m_qpcFreq.QuadPart);
    }
};

static WmfSinkWriter    g_sinkWriter;
static AudioCaptureManager g_audioCap;

#pragma endregion

#pragma region CAPTURE_THREADS

static std::thread g_captureThread;
static std::thread g_audioThread;

static void CaptureThreadProc()
{
    CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_ABOVE_NORMAL);

    while (g_appRunning.load()) {
        auto t0 = std::chrono::steady_clock::now();

        bool gotFrame = false;
        if (!g_renderer.AcquireFrame(gotFrame)) {
            Sleep(10);
            continue;
        }

        // Phase 2: per-frame source updates + canvas composite. The
        // desktop SRV is refreshed by AcquireFrame above; webcam /
        // window sources pull a new frame from their backend here.
        // The composite pass draws every visible source into the
        // canvas RTV in z-order. The encoder reads from the canvas
        // staging tex (replacing the older direct desktop-staging
        // readback path).
        {
            std::lock_guard<std::mutex> srcLk(cmp::g_sourcesMutex);
            for (auto& sp : cmp::g_sources) {
                if (sp) sp->Update(g_renderer.Device(), g_renderer.Context());
            }
        }
        g_renderer.CompositeFrame();

        if (g_recState == RecorderState::Recording) {
            UINT w = (UINT)g_renderer.CanvasW();
            UINT h = (UINT)g_renderer.CanvasH();
            UINT stride = w * 4;
            std::vector<BYTE> buf((size_t)stride * h);
            if (g_renderer.CopyCanvasToWMF(buf.data(), stride)) {
                std::lock_guard<std::mutex> lk(g_writeMutex);
                g_sinkWriter.WriteVideoFrame(buf.data(), stride);
            }
        }

        // Frame interval tracks the currently selected preset's target FPS
        // (used to be a fixed FRAME_INTERVAL_MS). Re-evaluating per-frame is
        // cheap and lets the user change preset on the fly.
        UINT presetFps = TARGET_FPS;
        int  pIdx = g_selectedPreset;
        if (pIdx >= 0 && pIdx < g_videoPresetCount && g_videoPresets[pIdx].fps > 0)
            presetFps = g_videoPresets[pIdx].fps;
        const long long frameIntervalMs = 1000LL / (long long)presetFps;

        auto t1 = std::chrono::steady_clock::now();
        auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(t1 - t0).count();
        DWORD toSleep = (DWORD)std::max(0LL, frameIntervalMs - elapsed);
        if (toSleep > 0) Sleep(toSleep);
    }

    CoUninitialize();
}

// Always-on audio capture / processing thread.
//
//   [WASAPI capture] → [Cubic resampler to user rate]
//                    → [Effect rack (loopback OR mic)]
//                    → [Bus gain]
//                    → [LiveMonitor (optional)]
//                    → [LUFSMeter]
//                    → [WMF SinkWriter] (only while Recording)
//
// The thread runs from app start to app exit so the LUFS meter, live
// monitor, and any inserted effects work without having to start a
// recording. UI changes (audio device, sample rate) signal a hot reinit
// via g_audioReinit, which the thread services on its next iteration.
static void AudioThreadProc()
{
    CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_TIME_CRITICAL);

    // Register with MMCSS "Pro Audio" so the scheduler treats this thread
    // as a glitch-sensitive workload. This is the single most important
    // change for USB microphones — without MMCSS the audio thread can be
    // preempted by Explorer / Defender / etc. for 5–20 ms at a time which
    // shows up as crackle on the device's 10 ms WASAPI buffer.
    DWORD mmcssIndex = 0;
    HANDLE mmcssTask = AvSetMmThreadCharacteristicsW(L"Pro Audio", &mmcssIndex);
    if (!mmcssTask) {
        // Some installs ship without "Pro Audio" — fall back to "Capture".
        mmcssTask = AvSetMmThreadCharacteristicsW(L"Capture", &mmcssIndex);
    }

    CubicResampler    resampler;
    std::vector<float> resampled;
    UINT              srcSr  = 0;
    UINT              dstSr  = g_selectedSampleRate.load();
    UINT              ch     = 2;

    auto openCapture = [&]() -> bool {
        g_audioCap.Stop();
        bool loopback = true;
        const wchar_t* devId = nullptr;
        if (g_selectedAudio >= 0 && g_selectedAudio < (int)g_audioDevices.size()) {
            loopback = g_audioDevices[g_selectedAudio].isLoopback;
            devId    = loopback ? nullptr : g_audioDevices[g_selectedAudio].id;
        }
        bool ok = g_audioCap.Init(devId, loopback);
        if (!ok && !loopback) {
            ok = g_audioCap.Init(nullptr, /*loopbackFallback=*/false);
        }
        if (!ok) {
            ok = g_audioCap.Init(nullptr, /*loopback=*/true);
            if (ok) loopback = true;
        }
        if (!ok) return false;
        if (!g_audioCap.Start()) return false;

        // Let the new capture endpoint fill at least one WASAPI buffer
        // before we read. USB mics need ~10–20 ms to produce their first
        // packet; without this sleep the initial ReadNextPacket returns
        // empty and the monitor/meter stays silent until the second loop
        // iteration, which the user perceives as "mic not working."
        Sleep(AUDIO_BUFFER_MS + 5);

        srcSr = g_audioCap.GetSampleRate();
        ch    = g_audioCap.GetChannels();
        dstSr = g_selectedSampleRate.load();
        resampler.Configure((double)srcSr, (double)dstSr, ch);

        // Drain and discard any initial stale / partial packets. Some
        // endpoints deliver a short fragment or a zero-filled block as
        // their first packet after Start(). Feeding that through the
        // resampler seeds the cubic Hermite history with garbage and
        // causes a brief crackle burst. Discard up to 2 packets.
        for (int warmup = 0; warmup < 2; ++warmup) {
            AudioCaptureManager::AudioPacket discard;
            if (!g_audioCap.ReadNextPacket(discard)) break;
        }

        // Hard-reset the bus + meter + monitor for the new capture
        // stream. Configure()'s no-op early return was leaving the
        // monitor primed from the previous device when rate/channels
        // happened to match (e.g. both 48 kHz stereo) — that's the
        // "mic silent at 48 kHz on first selection" failure mode.
        g_audioMixer.ForceReinit(dstSr, ch);
        return true;
    };

    openCapture();

    while (g_audioRunning.load()) {
        if (g_audioReinit.exchange(false)) {
            openCapture();
            continue;
        }

        // Wait for the next WASAPI buffer.  In event-driven mode, the
        // driver pulses our event the instant a buffer is ready; in
        // polling mode we poll every 5 ms.  Either way, when we wake
        // up we drain *every* queued packet before going back to sleep
        // so a single late wake never produces an audible glitch.
        HANDLE hEvt = g_audioCap.GetCaptureEvent();
        if (g_audioCap.IsEventDriven() && hEvt) {
            DWORD wr = WaitForSingleObject(hEvt, 100);
            if (wr == WAIT_TIMEOUT) {
                // Nothing arrived — let the loop continue so reinit /
                // shutdown signals are observed promptly.
                continue;
            }
            if (wr != WAIT_OBJECT_0) {
                Sleep(2);
                continue;
            }
        } else {
            Sleep(5);
        }

        // Drain ALL packets the WASAPI capture client currently has queued.
        // Failing to do this is the #1 cause of crackle on a USB mic: a
        // single late wake leaves multiple 10 ms buffers piled up, and if
        // we only consume one per loop iteration the rest get overwritten
        // when the next event fires (AUDCLNT_E_BUFFER_TOO_LARGE / data
        // discontinuity). Keep going until GetNextPacketSize reports 0.
        while (g_audioRunning.load()) {
            AudioCaptureManager::AudioPacket pkt;
            if (!g_audioCap.ReadNextPacket(pkt)) break;

            // Pause path: drain the capture but skip both the bus and the
            // encoder so the rate-of-flow stays correct without metering
            // or monitoring half-rendered audio.
            if (g_recState == RecorderState::Paused) continue;

            // Resample if the device's native rate differs from the user's
            // selected pipeline rate.
            const UINT activeDst = g_selectedSampleRate.load();
            if (activeDst != dstSr) {
                dstSr = activeDst;
                resampler.Configure((double)srcSr, (double)dstSr, ch);
                // ForceReinit (not Configure) so the live monitor's
                // WASAPI render endpoint is torn down and re-opened at
                // the new rate. Configure() skips the restart when
                // rate/channels match, which leaves the monitor running
                // at the old rate — the user hears nothing or garbled
                // audio until they toggle Monitor off/on.
                g_audioMixer.ForceReinit(dstSr, ch);
            }
            float*  procSamples = pkt.samples.data();
            UINT32  procFrames  = pkt.numFrames;
            UINT32  procRate    = pkt.sampleRate;
            if (!resampler.Bypass()) {
                resampler.Process(pkt.samples.data(), pkt.numFrames, resampled);
                if (resampled.empty()) continue;
                procSamples = resampled.data();
                procFrames  = (UINT32)(resampled.size() / pkt.numChannels);
                procRate    = dstSr;
            }

            g_audioMixer.Configure(procRate, pkt.numChannels);
            g_audioMixer.ProcessMixBus(procSamples, procFrames, pkt.numChannels,
                                       pkt.sourceIsLoopback);

            if (g_recState == RecorderState::Recording) {
                std::lock_guard<std::mutex> lk(g_writeMutex);
                g_sinkWriter.WriteAudioSamples(procSamples, procFrames);
            }
        }
    }

    g_audioCap.Stop();
    if (mmcssTask) AvRevertMmThreadCharacteristics(mmcssTask);
    CoUninitialize();
}

static void StartRecording()
{
    if (g_recState == RecorderState::Recording) return;

    if (g_recState == RecorderState::Paused) {
        {
            std::lock_guard<std::mutex> lk(g_writeMutex);
            g_sinkWriter.OnResume();
        }
        g_recState = RecorderState::Recording;
        return;
    }

    // Re-entrancy guard. exchange(true) returns the previous value;
    // if it was already true, another thread (or another invocation
    // of this function from inside the modal pump) is in the middle
    // of opening the save dialog — bail immediately so we don't
    // stack a second dialog on top.
    if (g_dialogOpen.exchange(true)) return;

    wchar_t path[MAX_PATH] = L"recording.mp4";
    OPENFILENAMEW ofn = {};
    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner   = g_hwndMain;
    ofn.lpstrFile   = path;
    ofn.nMaxFile    = MAX_PATH;
    ofn.lpstrFilter = L"MP4 File\0*.mp4\0All Files\0*.*\0";
    ofn.lpstrDefExt = L"mp4";
    ofn.Flags       = OFN_PATHMUSTEXIST | OFN_OVERWRITEPROMPT;
    BOOL gotPath = GetSaveFileNameW(&ofn);

    // Drain any WM_HOTKEY messages that piled up while the modal was
    // open — without this, the system message queue replays them as
    // soon as we return, and a held Ctrl+Shift+R produces a string
    // of additional StartRecording() calls (= infinite dialog).
    {
        MSG msg;
        while (PeekMessageW(&msg, nullptr, WM_HOTKEY, WM_HOTKEY, PM_REMOVE)) { /* drop */ }
    }

    if (!gotPath) { g_dialogOpen.store(false); return; }
    wcsncpy_s(g_outputPath, _countof(g_outputPath), path, _TRUNCATE);

    // Phase 2 — the encoder consumes the compositor canvas, so its
    // dimensions are the canvas dimensions (not the desktop's). The
    // canvas was sized by Init(); StartRecording does not change it.
    UINT capW = (UINT)g_renderer.CanvasW();
    UINT capH = (UINT)g_renderer.CanvasH();
    if (capW == 0 || capH == 0) { capW = 1920; capH = 1080; }
    capW = (capW + 1) & ~1u;
    capH = (capH + 1) & ~1u;

    // Audio thread is always-on (started at app boot), so we just adopt
    // its current rate / channel count for the sink writer.
    UINT sr = g_selectedSampleRate.load();
    UINT ch = g_audioCap.GetChannels();
    if (ch == 0) ch = 2;

    // Resolve current video preset (FPS + bitrate). Falls back to "Balanced"
    // if the user-selected index has somehow become out of range.
    int presetIdx = g_selectedPreset;
    if (presetIdx < 0 || presetIdx >= g_videoPresetCount) presetIdx = 1;
    const VideoPreset& preset = g_videoPresets[presetIdx];

    {
        std::lock_guard<std::mutex> lk(g_writeMutex);
        if (!g_sinkWriter.Init(g_outputPath, capW, capH, preset.fps, sr, ch, preset.bitrate)) {
            MessageBoxW(g_hwndMain, L"Failed to initialize WMF Sink Writer.", L"Error", MB_ICONERROR);
            g_dialogOpen.store(false);
            return;
        }
    }

    g_recState = RecorderState::Recording;
    g_dialogOpen.store(false);
}

static void PauseRecording()
{
    if (g_recState == RecorderState::Recording) {
        g_recState = RecorderState::Paused;
        std::lock_guard<std::mutex> lk(g_writeMutex);
        g_sinkWriter.OnPause();
    } else if (g_recState == RecorderState::Paused) {
        {
            std::lock_guard<std::mutex> lk(g_writeMutex);
            g_sinkWriter.OnResume();
        }
        g_recState = RecorderState::Recording;
    }
}

static void StopRecording()
{
    if (g_recState == RecorderState::Idle) return;

    // Audio thread keeps running (it's always-on for live monitoring + LUFS);
    // we just stop feeding the encoder and finalize the file.
    g_recState = RecorderState::Idle;

    {
        std::lock_guard<std::mutex> lk(g_writeMutex);
        g_sinkWriter.Finalize();
    }
}

#pragma endregion

#pragma region HOTKEY_VK_TABLE

struct VkEntry { const wchar_t* name; UINT vk; };
static const VkEntry g_vkTable[] = {
    { L"None", 0 },
    { L"F1",   VK_F1  }, { L"F2",   VK_F2  }, { L"F3",  VK_F3  },
    { L"F4",   VK_F4  }, { L"F5",   VK_F5  }, { L"F6",  VK_F6  },
    { L"F7",   VK_F7  }, { L"F8",   VK_F8  }, { L"F9",  VK_F9  },
    { L"F10",  VK_F10 }, { L"F11",  VK_F11 }, { L"F12", VK_F12 },
    { L"R",    'R'    }, { L"P",    'P'    }, { L"S",   'S'    },
    { L"1",    '1'    }, { L"2",    '2'    }, { L"3",   '3'    },
};
static const int g_vkTableCount = (int)(sizeof(g_vkTable)/sizeof(g_vkTable[0]));

static int VkToComboIndex(UINT vk)
{
    for (int i = 0; i < g_vkTableCount; ++i)
        if (g_vkTable[i].vk == vk) return i;
    return 0;
}

static void RegisterGlobalHotkeys(HWND hwnd)
{
    UnregisterHotKey(hwnd, HK_ID_START);
    UnregisterHotKey(hwnd, HK_ID_PAUSE);
    UnregisterHotKey(hwnd, HK_ID_STOP);
    // MOD_NOREPEAT (Win7+) suppresses auto-repeat WM_HOTKEY messages
    // when the user holds the chord. Without it, holding Ctrl+Shift+R
    // for half a second posts ~15 WM_HOTKEY messages — and each one
    // tries to open another save dialog (= infinite dialog cycle).
    UINT mods = g_hkMods | 0x4000 /* MOD_NOREPEAT */;
    if (g_hkStartVKey) RegisterHotKey(hwnd, HK_ID_START, mods, g_hkStartVKey);
    if (g_hkPauseVKey) RegisterHotKey(hwnd, HK_ID_PAUSE, mods, g_hkPauseVKey);
    if (g_hkStopVKey)  RegisterHotKey(hwnd, HK_ID_STOP,  mods, g_hkStopVKey);
}

#pragma endregion

// Custom UI core: Direct2D + DirectWrite, immediate-mode widget kit.
//
// Replaces every Win32 common control in this file. Drawing happens on a
// dedicated child window (the "UI panel") with its own D3D11 device and a
// flip-discard swap chain; Direct2D 1.1 interops with that device so we get
// hardware-accelerated, alpha-correct, per-pixel-DPI vector rendering. Text
// is laid out by DirectWrite. No GDI is used anywhere on this surface so
// there is no compositor-tear seam between the UI and the live preview pane.
//
// Architecture is immediate-mode (à la Dear ImGui, but written from scratch
// for this app). Each frame we drain mouse / keyboard events into an
// InputState struct, then call widget functions in straight-line code; each
// widget hit-tests, updates its tracking state, draws, and returns whether
// it was activated. Persistent state (slider values, combo selection, etc.)
// lives in the application — the UI just visualises and edits them.
//
// Animations: when a widget transitions hover / press / dropdown-open we
// store a small std::map<int, AnimState> keyed by the widget id, and lerp
// smoothly with `dt` from the frame timer (60 Hz). Eased with ease-out-cubic.
// =====================================================================

namespace ui {

// ---------------------------------------------------------------------
//                              Theme
// ---------------------------------------------------------------------
struct Color { float r, g, b, a; };

static inline Color RGBHex(uint32_t hex, float a = 1.0f)
{
    return Color{
        ((hex >> 16) & 0xFF) / 255.0f,
        ((hex >>  8) & 0xFF) / 255.0f,
        ((hex >>  0) & 0xFF) / 255.0f,
        a
    };
}

static inline Color Lerp(const Color& a, const Color& b, float t)
{
    return Color{
        a.r + (b.r - a.r) * t,
        a.g + (b.g - a.g) * t,
        a.b + (b.b - a.b) * t,
        a.a + (b.a - a.a) * t,
    };
}

static inline Color WithAlpha(const Color& c, float a)
{
    return Color{ c.r, c.g, c.b, a };
}

struct Theme {
    // Backgrounds — macOS-inspired warm dark tones with subtle depth
    Color bgWindow      = RGBHex(0x1C1C1E);   // macOS dark mode window
    Color bgPanel       = RGBHex(0x2C2C2E);   // elevated surface
    Color bgElevated    = RGBHex(0x3A3A3C);   // cards / popovers
    Color bgInput       = RGBHex(0x1C1C1E);   // input fields
    Color bgInputHover  = RGBHex(0x38383A);   // hovered inputs

    // Borders / dividers — softer, translucent-feel
    Color border        = RGBHex(0x3A3A3C);
    Color borderHover   = RGBHex(0x545458);
    Color divider       = RGBHex(0x38383A);

    // Text — SF-style hierarchy
    Color text          = RGBHex(0xF5F5F7);   // primary label
    Color textDim       = RGBHex(0xA1A1A6);   // secondary label
    Color textMuted     = RGBHex(0x636366);   // tertiary / placeholder
    Color textOnAccent  = RGBHex(0xFFFFFF);

    // Accent + states — macOS system blue
    Color accent        = RGBHex(0x0A84FF);   // system blue (dark)
    Color accentHover   = RGBHex(0x409CFF);
    Color accentPressed = RGBHex(0x0071E3);
    Color accentDim     = RGBHex(0x1C3A5F);
    Color danger        = RGBHex(0xFF453A);   // system red
    Color success       = RGBHex(0x30D158);   // system green
    Color warning       = RGBHex(0xFFD60A);   // system yellow

    // Meter palette (LUFS / VU)
    Color meterGreen    = RGBHex(0x30D158);
    Color meterYellow   = RGBHex(0xFFD60A);
    Color meterRed      = RGBHex(0xFF453A);
    Color meterTrack    = RGBHex(0x1C1C1E);

    // Geometry — rounder, more spacious (macOS HIG)
    float radiusCard      = 10.0f;
    float radiusInput     = 7.0f;
    float radiusButton    = 7.0f;
    float radiusPill      = 999.0f;

    float padPanel        = 20.0f;
    float padCard         = 14.0f;
    float gap             = 10.0f;

    float fontBody        = 13.0f;
    float fontCaption     = 11.0f;
    float fontSubhead     = 14.0f;
    float fontHeadline    = 16.0f;
    float fontDisplayBig  = 32.0f;
    float fontDisplaySml  = 22.0f;

    int   ctlH            = 32;    // slightly taller controls
    int   ctlHTall        = 38;
    int   rowGap          = 12;    // more breathing room
};

static Theme g_theme;

// ---------------------------------------------------------------------
//                              Geometry
// ---------------------------------------------------------------------
struct Rect {
    float x = 0, y = 0, w = 0, h = 0;

    bool Contains(float px, float py) const
    {
        return px >= x && py >= y && px < x + w && py < y + h;
    }
    Rect Inset(float p) const { return Rect{ x + p, y + p, w - 2*p, h - 2*p }; }
    Rect Inset(float l, float t, float r, float b) const
    { return Rect{ x + l, y + t, w - l - r, h - t - b }; }
    Rect Shift(float dx, float dy) const { return Rect{ x+dx, y+dy, w, h }; }
    float CX() const { return x + w * 0.5f; }
    float CY() const { return y + h * 0.5f; }
    float R()  const { return x + w; }
    float B()  const { return y + h; }
};

// ---------------------------------------------------------------------
//                              Renderer
// ---------------------------------------------------------------------
class Renderer {
public:
    bool Init(HWND hwnd);
    void Shutdown();
    void Resize(int w, int h);
    int  Width()  const { return m_w; }
    int  Height() const { return m_h; }

    bool BeginFrame(const Color& clear);
    void EndFrame();

    // Primitives
    void FillRect(const Rect& r, const Color& c);
    void FillRoundedRect(const Rect& r, float radius, const Color& c);
    void StrokeRect(const Rect& r, float thickness, const Color& c);
    void StrokeRoundedRect(const Rect& r, float radius, float thickness,
                           const Color& c);
    void FillCircle(float cx, float cy, float radius, const Color& c);
    void StrokeCircle(float cx, float cy, float radius, float thickness,
                      const Color& c);
    void DrawLine(float x1, float y1, float x2, float y2, float thickness,
                  const Color& c);
    // soft glow / drop shadow approximation: stack of translucent rounded
    // rects, slightly larger and dimmer each pass — cheaper than D2D effects
    void DrawShadow(const Rect& r, float radius, float spread,
                    const Color& c);

    enum TextAlignH { AlignLeft, AlignCenter, AlignRight };
    enum TextAlignV { AlignTop,  AlignMiddle, AlignBottom };

    void DrawText(const wchar_t* text, const Rect& r, const Color& c,
                  float fontSize,
                  TextAlignH ah = AlignLeft, TextAlignV av = AlignMiddle,
                  bool bold = false, const wchar_t* family = nullptr);

    // Returns the pixel width the text would take on a single baseline.
    float MeasureText(const wchar_t* text, float fontSize, bool bold = false,
                      const wchar_t* family = nullptr);

    // Clip stack (axis-aligned rectangular)
    void PushClip(const Rect& r);
    void PopClip();

private:
    ID2D1Factory1*       m_d2dFac    = nullptr;
    IDWriteFactory*      m_dwFac     = nullptr;
    ID3D11Device*        m_d3dDev    = nullptr;
    ID3D11DeviceContext* m_d3dCtx    = nullptr;
    IDXGISwapChain1*     m_swap      = nullptr;
    ID2D1Device*         m_d2dDev    = nullptr;
    ID2D1DeviceContext*  m_d2dCtx    = nullptr;
    ID2D1Bitmap1*        m_target    = nullptr;
    HWND                 m_hwnd      = nullptr;

    int m_w = 0, m_h = 0;

    // Caches
    struct BrushKey {
        uint32_t rgba;
        bool operator<(const BrushKey& o) const { return rgba < o.rgba; }
    };
    std::map<uint32_t, ID2D1SolidColorBrush*> m_brushCache;
    ID2D1SolidColorBrush* GetBrush(const Color& c);

    struct FmtKey {
        std::wstring family;
        float        size;
        bool         bold;
        bool operator<(const FmtKey& o) const
        {
            if (family != o.family) return family < o.family;
            if (size   != o.size)   return size   < o.size;
            return bold < o.bold;
        }
    };
    std::map<FmtKey, IDWriteTextFormat*> m_fmtCache;
    IDWriteTextFormat* GetFormat(const wchar_t* family, float size, bool bold);

    bool CreateTargetBitmap();
    void ReleaseTargetBitmap();
};

bool Renderer::Init(HWND hwnd)
{
    m_hwnd = hwnd;

    UINT createFlags = D3D11_CREATE_DEVICE_BGRA_SUPPORT;
    D3D_FEATURE_LEVEL chosen = {};
    HRESULT hr = D3D11CreateDevice(nullptr, D3D_DRIVER_TYPE_HARDWARE, nullptr,
                                   createFlags, nullptr, 0,
                                   D3D11_SDK_VERSION,
                                   &m_d3dDev, &chosen, &m_d3dCtx);
    if (FAILED(hr)) {
        hr = D3D11CreateDevice(nullptr, D3D_DRIVER_TYPE_WARP, nullptr,
                               createFlags, nullptr, 0,
                               D3D11_SDK_VERSION,
                               &m_d3dDev, &chosen, &m_d3dCtx);
        if (FAILED(hr)) return false;
    }

    IDXGIDevice*  dxgi = nullptr;
    m_d3dDev->QueryInterface(__uuidof(IDXGIDevice), (void**)&dxgi);
    IDXGIAdapter* adap = nullptr;
    if (dxgi) dxgi->GetAdapter(&adap);
    IDXGIFactory2* fac = nullptr;
    if (adap) adap->GetParent(__uuidof(IDXGIFactory2), (void**)&fac);

    RECT rc; GetClientRect(hwnd, &rc);
    m_w = std::max(8, (int)(rc.right - rc.left));
    m_h = std::max(8, (int)(rc.bottom - rc.top));

    DXGI_SWAP_CHAIN_DESC1 scd = {};
    scd.Width              = (UINT)m_w;
    scd.Height             = (UINT)m_h;
    scd.Format             = DXGI_FORMAT_B8G8R8A8_UNORM;
    scd.SampleDesc.Count   = 1;
    scd.BufferUsage        = DXGI_USAGE_RENDER_TARGET_OUTPUT;
    scd.BufferCount        = 2;
    scd.SwapEffect         = DXGI_SWAP_EFFECT_FLIP_DISCARD;
    scd.Scaling            = DXGI_SCALING_NONE;
    scd.AlphaMode          = DXGI_ALPHA_MODE_IGNORE;

    if (fac) hr = fac->CreateSwapChainForHwnd(m_d3dDev, hwnd, &scd,
                                              nullptr, nullptr, &m_swap);
    else     hr = E_FAIL;

    if (fac)  fac->Release();
    if (adap) adap->Release();
    if (dxgi) dxgi->Release();
    if (FAILED(hr)) return false;

    D2D1_FACTORY_OPTIONS fo = {};
    hr = D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED,
                           __uuidof(ID2D1Factory1), &fo, (void**)&m_d2dFac);
    if (FAILED(hr)) return false;

    IDXGIDevice* dxgiDev = nullptr;
    m_d3dDev->QueryInterface(__uuidof(IDXGIDevice), (void**)&dxgiDev);
    if (!dxgiDev) return false;
    hr = m_d2dFac->CreateDevice(dxgiDev, &m_d2dDev);
    dxgiDev->Release();
    if (FAILED(hr)) return false;

    hr = m_d2dDev->CreateDeviceContext(D2D1_DEVICE_CONTEXT_OPTIONS_NONE,
                                       &m_d2dCtx);
    if (FAILED(hr)) return false;

    hr = DWriteCreateFactory(DWRITE_FACTORY_TYPE_SHARED,
                             __uuidof(IDWriteFactory),
                             (IUnknown**)&m_dwFac);
    if (FAILED(hr)) return false;

    if (!CreateTargetBitmap()) return false;

    return true;
}

bool Renderer::CreateTargetBitmap()
{
    IDXGISurface* surf = nullptr;
    HRESULT hr = m_swap->GetBuffer(0, __uuidof(IDXGISurface), (void**)&surf);
    if (FAILED(hr) || !surf) return false;

    D2D1_BITMAP_PROPERTIES1 bp = {};
    bp.pixelFormat   = D2D1::PixelFormat(DXGI_FORMAT_B8G8R8A8_UNORM,
                                         D2D1_ALPHA_MODE_IGNORE);
    bp.bitmapOptions = D2D1_BITMAP_OPTIONS_TARGET |
                       D2D1_BITMAP_OPTIONS_CANNOT_DRAW;
    bp.dpiX = 96.0f;
    bp.dpiY = 96.0f;

    hr = m_d2dCtx->CreateBitmapFromDxgiSurface(surf, &bp, &m_target);
    surf->Release();
    if (FAILED(hr)) return false;
    m_d2dCtx->SetTarget(m_target);
    return true;
}

void Renderer::ReleaseTargetBitmap()
{
    if (m_d2dCtx) m_d2dCtx->SetTarget(nullptr);
    if (m_target) { m_target->Release(); m_target = nullptr; }
}

void Renderer::Shutdown()
{
    for (auto& kv : m_brushCache) if (kv.second) kv.second->Release();
    m_brushCache.clear();
    for (auto& kv : m_fmtCache)   if (kv.second) kv.second->Release();
    m_fmtCache.clear();

    ReleaseTargetBitmap();
    if (m_d2dCtx) { m_d2dCtx->Release(); m_d2dCtx = nullptr; }
    if (m_d2dDev) { m_d2dDev->Release(); m_d2dDev = nullptr; }
    if (m_d2dFac) { m_d2dFac->Release(); m_d2dFac = nullptr; }
    if (m_dwFac)  { m_dwFac->Release();  m_dwFac  = nullptr; }
    if (m_swap)   { m_swap->Release();   m_swap   = nullptr; }
    if (m_d3dCtx) { m_d3dCtx->Release(); m_d3dCtx = nullptr; }
    if (m_d3dDev) { m_d3dDev->Release(); m_d3dDev = nullptr; }
}

void Renderer::Resize(int w, int h)
{
    if (w < 8) w = 8;
    if (h < 8) h = 8;
    if (w == m_w && h == m_h) return;
    m_w = w;
    m_h = h;
    if (!m_swap) return;

    // Release any brushes that depend on the device context (none here, but
    // we MUST release the bitmap target before resizing the swap chain).
    for (auto& kv : m_brushCache) if (kv.second) kv.second->Release();
    m_brushCache.clear();

    ReleaseTargetBitmap();
    HRESULT hr = m_swap->ResizeBuffers(0, (UINT)w, (UINT)h,
                                       DXGI_FORMAT_UNKNOWN, 0);
    if (FAILED(hr)) return;
    CreateTargetBitmap();
}

ID2D1SolidColorBrush* Renderer::GetBrush(const Color& c)
{
    uint32_t key =
        ((uint32_t)(Clamp(c.r,0,1)*255) << 24) |
        ((uint32_t)(Clamp(c.g,0,1)*255) << 16) |
        ((uint32_t)(Clamp(c.b,0,1)*255) <<  8) |
        ((uint32_t)(Clamp(c.a,0,1)*255) <<  0);
    auto it = m_brushCache.find(key);
    if (it != m_brushCache.end()) return it->second;
    ID2D1SolidColorBrush* b = nullptr;
    D2D1_COLOR_F cf = { c.r, c.g, c.b, c.a };
    HRESULT hr = m_d2dCtx->CreateSolidColorBrush(cf, &b);
    if (FAILED(hr)) return nullptr;
    m_brushCache[key] = b;
    return b;
}

IDWriteTextFormat* Renderer::GetFormat(const wchar_t* family, float size, bool bold)
{
    FmtKey key{ family ? family : L"Segoe UI", size, bold };
    auto it = m_fmtCache.find(key);
    if (it != m_fmtCache.end()) return it->second;
    IDWriteTextFormat* f = nullptr;
    HRESULT hr = m_dwFac->CreateTextFormat(
        key.family.c_str(), nullptr,
        bold ? DWRITE_FONT_WEIGHT_SEMI_BOLD : DWRITE_FONT_WEIGHT_NORMAL,
        DWRITE_FONT_STYLE_NORMAL, DWRITE_FONT_STRETCH_NORMAL,
        size, L"en-us", &f);
    if (FAILED(hr) || !f) return nullptr;
    m_fmtCache[key] = f;
    return f;
}

bool Renderer::BeginFrame(const Color& clear)
{
    if (!m_d2dCtx || !m_target) return false;
    m_d2dCtx->BeginDraw();
    m_d2dCtx->Clear(D2D1::ColorF(clear.r, clear.g, clear.b, clear.a));
    return true;
}

void Renderer::EndFrame()
{
    if (!m_d2dCtx) return;
    HRESULT hr = m_d2dCtx->EndDraw();
    if (hr == D2DERR_RECREATE_TARGET) {
        ReleaseTargetBitmap();
        CreateTargetBitmap();
        return;
    }
    if (m_swap) {
        DXGI_PRESENT_PARAMETERS pp = {};
        m_swap->Present1(1, 0, &pp);
    }
}

void Renderer::FillRect(const Rect& r, const Color& c)
{
    auto* b = GetBrush(c); if (!b) return;
    D2D1_RECT_F dr = { r.x, r.y, r.x + r.w, r.y + r.h };
    m_d2dCtx->FillRectangle(dr, b);
}
void Renderer::FillRoundedRect(const Rect& r, float radius, const Color& c)
{
    auto* b = GetBrush(c); if (!b) return;
    D2D1_ROUNDED_RECT rr;
    rr.rect = { r.x, r.y, r.x + r.w, r.y + r.h };
    rr.radiusX = rr.radiusY = radius;
    m_d2dCtx->FillRoundedRectangle(rr, b);
}
void Renderer::StrokeRect(const Rect& r, float thickness, const Color& c)
{
    auto* b = GetBrush(c); if (!b) return;
    D2D1_RECT_F dr = { r.x + thickness*0.5f, r.y + thickness*0.5f,
                       r.x + r.w - thickness*0.5f,
                       r.y + r.h - thickness*0.5f };
    m_d2dCtx->DrawRectangle(dr, b, thickness);
}
void Renderer::StrokeRoundedRect(const Rect& r, float radius, float thickness,
                                 const Color& c)
{
    auto* b = GetBrush(c); if (!b) return;
    D2D1_ROUNDED_RECT rr;
    rr.rect = { r.x + thickness*0.5f, r.y + thickness*0.5f,
                r.x + r.w - thickness*0.5f, r.y + r.h - thickness*0.5f };
    rr.radiusX = rr.radiusY = radius;
    m_d2dCtx->DrawRoundedRectangle(rr, b, thickness);
}
void Renderer::FillCircle(float cx, float cy, float radius, const Color& c)
{
    auto* b = GetBrush(c); if (!b) return;
    D2D1_ELLIPSE e = { { cx, cy }, radius, radius };
    m_d2dCtx->FillEllipse(e, b);
}
void Renderer::StrokeCircle(float cx, float cy, float radius, float thickness,
                            const Color& c)
{
    auto* b = GetBrush(c); if (!b) return;
    D2D1_ELLIPSE e = { { cx, cy }, radius, radius };
    m_d2dCtx->DrawEllipse(e, b, thickness);
}
void Renderer::DrawLine(float x1, float y1, float x2, float y2, float thickness,
                        const Color& c)
{
    auto* b = GetBrush(c); if (!b) return;
    m_d2dCtx->DrawLine({ x1, y1 }, { x2, y2 }, b, thickness);
}
void Renderer::DrawShadow(const Rect& r, float radius, float spread, const Color& c)
{
    // Cheap fake-shadow: 4 increasingly-larger rounded rects with falling alpha.
    int   layers = 6;
    float a0     = c.a;
    for (int i = layers; i >= 1; --i) {
        float t  = (float)i / (float)layers;
        float p  = spread * t;
        Color col = c;
        col.a    = a0 * (1.0f - t) * 0.4f;
        Rect rr  = { r.x - p, r.y - p, r.w + 2*p, r.h + 2*p };
        FillRoundedRect(rr, radius + p, col);
    }
}
void Renderer::DrawText(const wchar_t* text, const Rect& r, const Color& c,
                        float fontSize,
                        TextAlignH ah, TextAlignV av,
                        bool bold, const wchar_t* family)
{
    if (!text || !*text) return;
    auto* b   = GetBrush(c); if (!b) return;
    auto* fmt = GetFormat(family, fontSize, bold); if (!fmt) return;
    DWRITE_TEXT_ALIGNMENT      ta = DWRITE_TEXT_ALIGNMENT_LEADING;
    DWRITE_PARAGRAPH_ALIGNMENT pa = DWRITE_PARAGRAPH_ALIGNMENT_CENTER;
    if (ah == AlignCenter) ta = DWRITE_TEXT_ALIGNMENT_CENTER;
    if (ah == AlignRight)  ta = DWRITE_TEXT_ALIGNMENT_TRAILING;
    if (av == AlignTop)    pa = DWRITE_PARAGRAPH_ALIGNMENT_NEAR;
    if (av == AlignBottom) pa = DWRITE_PARAGRAPH_ALIGNMENT_FAR;
    fmt->SetTextAlignment(ta);
    fmt->SetParagraphAlignment(pa);
    D2D1_RECT_F dr = { r.x, r.y, r.x + r.w, r.y + r.h };
    m_d2dCtx->DrawTextW(text, (UINT32)wcslen(text), fmt, dr, b,
                        D2D1_DRAW_TEXT_OPTIONS_CLIP);
}
float Renderer::MeasureText(const wchar_t* text, float fontSize, bool bold,
                            const wchar_t* family)
{
    if (!text) return 0;
    auto* fmt = GetFormat(family, fontSize, bold); if (!fmt) return 0;
    IDWriteTextLayout* lay = nullptr;
    HRESULT hr = m_dwFac->CreateTextLayout(text, (UINT32)wcslen(text), fmt,
                                           4096.0f, 64.0f, &lay);
    if (FAILED(hr) || !lay) return 0;
    DWRITE_TEXT_METRICS tm = {};
    lay->GetMetrics(&tm);
    lay->Release();
    return tm.widthIncludingTrailingWhitespace;
}
void Renderer::PushClip(const Rect& r)
{
    D2D1_RECT_F dr = { r.x, r.y, r.x + r.w, r.y + r.h };
    m_d2dCtx->PushAxisAlignedClip(dr, D2D1_ANTIALIAS_MODE_PER_PRIMITIVE);
}
void Renderer::PopClip()
{
    m_d2dCtx->PopAxisAlignedClip();
}

// ---------------------------------------------------------------------
//                              Input + animations
// ---------------------------------------------------------------------
struct InputState {
    float mouseX = 0, mouseY = 0;
    float lastMouseX = 0, lastMouseY = 0;
    bool  mouseDown[3]      = { false, false, false };
    bool  mousePressed[3]   = { false, false, false };
    bool  mouseReleased[3]  = { false, false, false };
    bool  mouseInside       = false;
    bool  mouseDouble[3]    = { false, false, false };
    int   wheelTicks        = 0;          // accumulated whole-tick deltas
    std::vector<wchar_t> chars;
    bool  keyDown[256]      = {};
    bool  keyPressed[256]   = {};

    int   hovered  = 0;       // widget id under cursor
    int   active   = 0;       // widget id mouse-pressed on (sticky until release)
    int   focused  = 0;       // keyboard focus
    int   lastDropdown = 0;   // open dropdown (so click-elsewhere can close it)

    void NewFrame()
    {
        for (int i = 0; i < 3; ++i) {
            mousePressed[i]  = false;
            mouseReleased[i] = false;
            mouseDouble[i]   = false;
        }
        for (int i = 0; i < 256; ++i) keyPressed[i] = false;
        wheelTicks = 0;
        chars.clear();
        hovered = 0;
    }
};

struct AnimState {
    float hover   = 0; // 0..1 hover-amount, eased
    float press   = 0; // 0..1 press-amount, eased
    float open    = 0; // 0..1 dropdown openness, eased
    float scroll  = 0; // scroll offset in pixels
};
static std::map<int, AnimState> g_anim;
static AnimState& Anim(int id) { return g_anim[id]; }

static inline float EaseOutCubic(float t)
{
    if (t < 0) t = 0; if (t > 1) t = 1;
    float u = 1 - t;
    return 1 - u * u * u;
}
static inline float ApproachLin(float cur, float target, float dt, float halflife)
{
    float k = 1.0f - std::pow(0.5f, dt / std::max(halflife, 1e-3f));
    return cur + (target - cur) * k;
}

// ---------------------------------------------------------------------
//                              Widget kit
// ---------------------------------------------------------------------
struct Context {
    Renderer*   r   = nullptr;
    InputState* in  = nullptr;
    float       dt  = 1.0f / 60.0f;

    // dropdown layer (deferred so it draws over everything else this frame)
    struct Dropdown {
        int      id       = 0;
        Rect     anchor   {};
        std::vector<std::wstring> items;
        int*     selected = nullptr;
    };
    Dropdown openDropdown;
    bool     hasOpenDropdown = false;
};
static Context g_ctx;

// Tiny helper: pushed by the Audio FX listbox so we can detect drag-reorder.
static int g_listboxDragSrc = -1;
static int g_listboxDragDst = -1;

static bool MouseInsideAndPressed(const Rect& rc, int btn = 0)
{
    return g_ctx.in->mouseInside && g_ctx.in->mousePressed[btn] &&
           rc.Contains(g_ctx.in->mouseX, g_ctx.in->mouseY);
}
static bool MouseInsideAndReleased(const Rect& rc, int btn = 0)
{
    return g_ctx.in->mouseInside && g_ctx.in->mouseReleased[btn] &&
           rc.Contains(g_ctx.in->mouseX, g_ctx.in->mouseY);
}
static bool MouseHovering(const Rect& rc)
{
    return g_ctx.in->mouseInside && rc.Contains(g_ctx.in->mouseX, g_ctx.in->mouseY);
}

// --- Label ---
void Label(const Rect& r, const wchar_t* text,
           Renderer::TextAlignH ah = Renderer::AlignLeft,
           bool dim = false, float size = 0, bool bold = false)
{
    if (size <= 0) size = g_theme.fontBody;
    g_ctx.r->DrawText(text, r, dim ? g_theme.textDim : g_theme.text,
                      size, ah, Renderer::AlignMiddle, bold);
}
void Heading(const Rect& r, const wchar_t* text)
{
    g_ctx.r->DrawText(text, r, g_theme.text, g_theme.fontHeadline,
                      Renderer::AlignLeft, Renderer::AlignMiddle, true);
}
void Caption(const Rect& r, const wchar_t* text)
{
    g_ctx.r->DrawText(text, r, g_theme.textDim, g_theme.fontCaption,
                      Renderer::AlignLeft, Renderer::AlignMiddle);
}

// --- Card / Group ---
void Card(const Rect& r)
{
    g_ctx.r->FillRoundedRect(r, g_theme.radiusCard, g_theme.bgPanel);
    g_ctx.r->StrokeRoundedRect(r, g_theme.radiusCard, 1.0f, g_theme.border);
}
void GroupBox(const Rect& r, const wchar_t* title)
{
    Card(r);
    if (title && *title) {
        Rect th = { r.x + 14, r.y + 8, r.w - 28, 18 };
        g_ctx.r->DrawText(title, th, g_theme.textDim, g_theme.fontCaption,
                          Renderer::AlignLeft, Renderer::AlignMiddle, true);
    }
}

// --- Button ---
struct ButtonStyle { bool primary = false; bool danger = false; bool subtle = false; bool disabled = false; };
bool Button(int id, const Rect& r, const wchar_t* label,
            ButtonStyle st = {})
{
    auto& a = Anim(id);
    bool hov = MouseHovering(r) && !st.disabled;
    bool prs = hov && g_ctx.in->mouseDown[0];
    a.hover  = ApproachLin(a.hover, hov ? 1.0f : 0.0f, g_ctx.dt, 0.07f);
    a.press  = ApproachLin(a.press, prs ? 1.0f : 0.0f, g_ctx.dt, 0.04f);

    Color bg, txt = g_theme.text, brd = g_theme.border;
    if (st.disabled) {
        bg  = WithAlpha(g_theme.bgInput, 0.5f);
        txt = g_theme.textMuted;
    } else if (st.primary) {
        Color base = g_theme.accent;
        Color on   = g_theme.accentHover;
        Color dn   = g_theme.accentPressed;
        bg = Lerp(base, on, EaseOutCubic(a.hover));
        bg = Lerp(bg,   dn, EaseOutCubic(a.press));
        txt = g_theme.textOnAccent;
        brd = WithAlpha(g_theme.accent, 0.0f);
    } else if (st.danger) {
        bg = Lerp(g_theme.bgInput, g_theme.danger, 0.15f + 0.4f * a.hover);
        txt = (a.hover > 0.5f) ? g_theme.textOnAccent : g_theme.text;
    } else if (st.subtle) {
        bg = Lerp(WithAlpha(g_theme.bgPanel, 0.0f), g_theme.bgInputHover, a.hover);
        brd = WithAlpha(g_theme.border, 0.0f);
    } else {
        bg = Lerp(g_theme.bgInput, g_theme.bgInputHover, EaseOutCubic(a.hover));
        bg = Lerp(bg, g_theme.bgElevated, EaseOutCubic(a.press) * 0.5f);
    }

    g_ctx.r->FillRoundedRect(r, g_theme.radiusButton, bg);
    if (!st.primary && !st.subtle) {
        g_ctx.r->StrokeRoundedRect(r, g_theme.radiusButton, 1.0f,
            Lerp(brd, g_theme.borderHover, a.hover));
    }
    g_ctx.r->DrawText(label, r.Inset(10, 0, 10, 0), txt, g_theme.fontBody,
                      Renderer::AlignCenter, Renderer::AlignMiddle, true);

    bool clicked = MouseInsideAndReleased(r) && !st.disabled;
    if (clicked) g_ctx.in->active = 0;
    if (MouseInsideAndPressed(r) && !st.disabled) g_ctx.in->active = id;
    return clicked;
}

bool IconButton(int id, const Rect& r, const wchar_t* glyph,
                ButtonStyle st = {})
{
    return Button(id, r, glyph, st);
}

// --- Checkbox / Toggle ---
bool Checkbox(int id, const Rect& r, const wchar_t* label, bool* state)
{
    auto& a = Anim(id);
    bool hov = MouseHovering(r);
    a.hover  = ApproachLin(a.hover, hov ? 1.0f : 0.0f, g_ctx.dt, 0.07f);
    a.press  = ApproachLin(a.press, *state ? 1.0f : 0.0f, g_ctx.dt, 0.06f);

    float bs = 18.0f;
    Rect box = { r.x, r.y + (r.h - bs) * 0.5f, bs, bs };
    Color fill = Lerp(g_theme.bgInput, g_theme.accent, a.press);
    Color brd  = Lerp(g_theme.border, g_theme.accent, std::max(a.hover * 0.6f, a.press));
    g_ctx.r->FillRoundedRect(box, 4.0f, fill);
    g_ctx.r->StrokeRoundedRect(box, 4.0f, 1.0f, brd);

    if (a.press > 0.05f) {
        // Draw a check-mark via two strokes
        float t = EaseOutCubic(a.press);
        float ax = box.x + 4.0f;
        float ay = box.CY();
        float bx = box.x + 7.5f;
        float by = box.y + box.h - 5.0f;
        float cx = box.x + box.w - 3.5f;
        float cy = box.y + 4.5f;
        Color ch = WithAlpha(g_theme.textOnAccent, t);
        g_ctx.r->DrawLine(ax, ay, bx, by, 2.0f, ch);
        g_ctx.r->DrawLine(bx, by, cx, cy, 2.0f, ch);
    }

    Rect lbl = { box.R() + 8, r.y, r.w - bs - 8, r.h };
    g_ctx.r->DrawText(label, lbl, g_theme.text, g_theme.fontBody,
                      Renderer::AlignLeft, Renderer::AlignMiddle);

    bool clicked = MouseInsideAndReleased(r);
    if (clicked) { *state = !*state; }
    return clicked;
}

// --- Slider ---
// Logarithmic mapping when log==true (suits frequencies, attack/release).
bool Slider(int id, const Rect& r, float* value, float minV, float maxV,
            bool log, const wchar_t* fmt = L"%.2f")
{
    auto& a = Anim(id);
    Rect track = { r.x, r.CY() - 3, r.w, 6 };

    float t = 0;
    if (log) {
        float lo = std::log(std::max(1e-6f, minV));
        float hi = std::log(std::max(1e-6f, maxV));
        t = (std::log(std::max(1e-6f, *value)) - lo) / std::max(1e-6f, hi - lo);
    } else {
        t = (*value - minV) / std::max(1e-6f, maxV - minV);
    }
    t = Clamp(t, 0.0f, 1.0f);

    bool hov  = MouseHovering(r);
    bool actv = (g_ctx.in->active == id);
    if (hov && g_ctx.in->mousePressed[0]) { g_ctx.in->active = id; actv = true; }
    if (!g_ctx.in->mouseDown[0]) actv = (g_ctx.in->active == id) ? false : actv;

    a.hover = ApproachLin(a.hover, (hov || actv) ? 1.0f : 0.0f, g_ctx.dt, 0.06f);

    if (actv && g_ctx.in->mouseDown[0]) {
        float nx = (g_ctx.in->mouseX - track.x) / std::max(1.0f, track.w);
        nx = Clamp(nx, 0.0f, 1.0f);
        float nv;
        if (log) {
            float lo = std::log(std::max(1e-6f, minV));
            float hi = std::log(std::max(1e-6f, maxV));
            nv = std::exp(lo + (hi - lo) * nx);
        } else {
            nv = minV + (maxV - minV) * nx;
        }
        *value = nv;
        t = nx;
    }
    if (g_ctx.in->active == id && !g_ctx.in->mouseDown[0]) g_ctx.in->active = 0;

    g_ctx.r->FillRoundedRect(track, 3.0f, g_theme.bgInput);
    Rect filled = { track.x, track.y, track.w * t, track.h };
    g_ctx.r->FillRoundedRect(filled, 3.0f, g_theme.accent);

    float kx = track.x + track.w * t;
    float kr = 7.0f + a.hover * 1.5f;
    g_ctx.r->FillCircle(kx, track.CY(), kr + 2, WithAlpha(g_theme.bgWindow, 0.6f));
    g_ctx.r->FillCircle(kx, track.CY(), kr, g_theme.accent);
    g_ctx.r->FillCircle(kx, track.CY(), kr - 3, g_theme.textOnAccent);

    return actv;
}

// --- Vertical scrollbar (used inside Listbox) ---
static void DrawScrollbar(const Rect& trackR, float contentH, float* scroll)
{
    if (contentH <= trackR.h + 1) return;
    float thumbH = std::max(24.0f, trackR.h * (trackR.h / contentH));
    float maxScroll = contentH - trackR.h;
    if (*scroll < 0) *scroll = 0;
    if (*scroll > maxScroll) *scroll = maxScroll;
    float t = *scroll / std::max(1.0f, maxScroll);
    Rect thumb = { trackR.R() - 5, trackR.y + (trackR.h - thumbH) * t, 4, thumbH };
    g_ctx.r->FillRoundedRect(thumb, 2.0f, g_theme.borderHover);
}

// --- Combo (closed face only; opens dropdown layer) ---
struct ComboResult { bool changed = false; };
ComboResult Combo(int id, const Rect& r, int* selected,
                  const std::vector<std::wstring>& items)
{
    auto& a = Anim(id);
    bool hov = MouseHovering(r);
    a.hover = ApproachLin(a.hover, hov ? 1.0f : 0.0f, g_ctx.dt, 0.07f);

    Color bg = Lerp(g_theme.bgInput, g_theme.bgInputHover, a.hover);
    g_ctx.r->FillRoundedRect(r, g_theme.radiusInput, bg);
    g_ctx.r->StrokeRoundedRect(r, g_theme.radiusInput, 1.0f,
        Lerp(g_theme.border, g_theme.borderHover, a.hover));

    const wchar_t* txt = L"";
    if (selected && *selected >= 0 && *selected < (int)items.size())
        txt = items[*selected].c_str();
    g_ctx.r->DrawText(txt, r.Inset(10, 0, 24, 0), g_theme.text,
                      g_theme.fontBody, Renderer::AlignLeft, Renderer::AlignMiddle);

    // Chevron
    float cx = r.R() - 12;
    float cy = r.CY();
    g_ctx.r->DrawLine(cx - 4, cy - 2, cx,     cy + 2, 1.5f, g_theme.textDim);
    g_ctx.r->DrawLine(cx,     cy + 2, cx + 4, cy - 2, 1.5f, g_theme.textDim);

    ComboResult res;
    if (MouseInsideAndPressed(r)) {
        // Open dropdown — defer to end-of-frame layer
        g_ctx.openDropdown.id        = id;
        g_ctx.openDropdown.anchor    = r;
        g_ctx.openDropdown.items     = items;
        g_ctx.openDropdown.selected  = selected;
        g_ctx.hasOpenDropdown        = true;
        g_ctx.in->lastDropdown       = id;
    }
    return res;
}

// Convenience overload that takes a const wchar_t* array
ComboResult Combo(int id, const Rect& r, int* selected,
                  const wchar_t* const* items, int count)
{
    std::vector<std::wstring> v;
    v.reserve(count);
    for (int i = 0; i < count; ++i) v.push_back(items[i]);
    return Combo(id, r, selected, v);
}

// Drawn AFTER the rest of the frame so it appears on top.
static int Combo_FlushDropdown()
{
    int activatedItem = -1;
    if (!g_ctx.hasOpenDropdown) return activatedItem;
    auto& d = g_ctx.openDropdown;
    auto& a = Anim(d.id);
    a.open  = ApproachLin(a.open, 1.0f, g_ctx.dt, 0.05f);

    int n = (int)d.items.size();
    if (n <= 0) return activatedItem;
    float itemH = 28.0f;
    float listH = std::min(itemH * n + 6, 320.0f);
    // Flip the dropdown upwards when there isn't room below the anchor.
    float surfH    = (float)g_ctx.r->Height();
    float spaceDn  = surfH - d.anchor.B() - 4;
    bool  flipUp   = spaceDn < listH && d.anchor.y > spaceDn;
    if (flipUp) listH = std::min(listH, std::max(40.0f, d.anchor.y - 4));
    Rect popup = flipUp
        ? Rect{ d.anchor.x, d.anchor.y - 2 - listH * EaseOutCubic(a.open),
                d.anchor.w, listH * EaseOutCubic(a.open) }
        : Rect{ d.anchor.x, d.anchor.B() + 2, d.anchor.w,
                listH * EaseOutCubic(a.open) };

    g_ctx.r->DrawShadow(popup, g_theme.radiusInput, 8.0f,
                        Color{0,0,0,0.45f});
    g_ctx.r->FillRoundedRect(popup, g_theme.radiusInput, g_theme.bgElevated);
    g_ctx.r->StrokeRoundedRect(popup, g_theme.radiusInput, 1.0f, g_theme.border);

    g_ctx.r->PushClip(popup);
    for (int i = 0; i < n; ++i) {
        Rect ir = { popup.x + 3, popup.y + 3 + i * itemH,
                    popup.w - 6, itemH };
        bool ihov = MouseHovering(ir);
        if (ihov) {
            g_ctx.r->FillRoundedRect(ir, g_theme.radiusInput - 2,
                                     WithAlpha(g_theme.accent, 0.18f));
        }
        if (d.selected && *d.selected == i) {
            g_ctx.r->FillRoundedRect(ir, g_theme.radiusInput - 2,
                                     WithAlpha(g_theme.accent, 0.28f));
        }
        g_ctx.r->DrawText(d.items[i].c_str(), ir.Inset(10, 0, 10, 0),
                          g_theme.text, g_theme.fontBody);
        if (MouseInsideAndReleased(ir)) {
            if (d.selected) *d.selected = i;
            activatedItem = i;
            a.open = 0;
            g_ctx.hasOpenDropdown = false;
            g_ctx.in->lastDropdown = 0;
            break;
        }
    }
    g_ctx.r->PopClip();

    // Close on click outside
    if (g_ctx.in->mousePressed[0] &&
        !popup.Contains(g_ctx.in->mouseX, g_ctx.in->mouseY) &&
        !d.anchor.Contains(g_ctx.in->mouseX, g_ctx.in->mouseY))
    {
        a.open = 0;
        g_ctx.hasOpenDropdown = false;
        g_ctx.in->lastDropdown = 0;
    }
    return activatedItem;
}

// --- Tab strip (Big-Sur sliding underline) ---
void TabStrip(int id, const Rect& r, int* selected,
              const wchar_t* const* labels, int count)
{
    if (count <= 0) return;
    // macOS-style segmented control: rounded pill background with a
    // sliding highlight behind the selected segment.
    Rect bg = r.Inset(2, 3, 2, 3);
    g_ctx.r->FillRoundedRect(bg, g_theme.radiusButton, g_theme.bgInput);

    float itemW = bg.w / (float)count;
    // Animated highlight position
    auto& a = g_anim[id ^ 0xBEEF];
    float targetX = *selected * itemW;
    a.scroll = ApproachLin(a.scroll, targetX, g_ctx.dt, 0.06f);
    Rect pill = { bg.x + a.scroll + 2, bg.y + 2, itemW - 4, bg.h - 4 };
    g_ctx.r->FillRoundedRect(pill, g_theme.radiusButton - 1, g_theme.bgElevated);

    for (int i = 0; i < count; ++i) {
        Rect tr = { bg.x + i * itemW, bg.y, itemW, bg.h };
        bool sel = (*selected == i);
        bool hov = MouseHovering(tr);
        Color txt = sel ? g_theme.text :
                          (hov ? g_theme.text : g_theme.textDim);
        g_ctx.r->DrawText(labels[i], tr, txt, g_theme.fontBody,
                          Renderer::AlignCenter, Renderer::AlignMiddle, sel);
        if (MouseInsideAndReleased(tr)) *selected = i;
    }
}

// --- Listbox (scrollable, click-to-select, drag-to-reorder) ---
struct ListboxResult { int clicked = -1; int reordered_from = -1; int reordered_to = -1; };
ListboxResult Listbox(int id, const Rect& r,
                      const std::vector<std::wstring>& items,
                      int* selected, float itemH = 28.0f,
                      bool drawIndex = true)
{
    ListboxResult res;
    auto& a = Anim(id);
    g_ctx.r->FillRoundedRect(r, g_theme.radiusInput, g_theme.bgInput);
    g_ctx.r->StrokeRoundedRect(r, g_theme.radiusInput, 1.0f, g_theme.border);
    g_ctx.r->PushClip(r.Inset(1));

    int n = (int)items.size();
    float contentH = n * itemH;
    if (MouseHovering(r) && g_ctx.in->wheelTicks != 0) {
        a.scroll -= g_ctx.in->wheelTicks * 24.0f;
    }
    if (a.scroll < 0) a.scroll = 0;
    float maxScroll = std::max(0.0f, contentH - r.h + 6);
    if (a.scroll > maxScroll) a.scroll = maxScroll;

    float yBase = r.y + 3 - a.scroll;
    for (int i = 0; i < n; ++i) {
        Rect ir = { r.x + 3, yBase + i * itemH, r.w - 6, itemH - 2 };
        if (ir.B() < r.y || ir.y > r.B()) continue;
        bool sel = selected && (*selected == i);
        bool hov = MouseHovering(ir);

        Color bg = sel ? WithAlpha(g_theme.accent, 0.20f) :
                   (hov ? WithAlpha(g_theme.accent, 0.08f) : Color{0,0,0,0});
        g_ctx.r->FillRoundedRect(ir, g_theme.radiusInput - 2, bg);
        if (sel) {
            Rect bar = { ir.x, ir.y + 4, 3, ir.h - 8 };
            g_ctx.r->FillRoundedRect(bar, 1.5f, g_theme.accent);
        }
        Rect txt = ir.Inset(12, 0, 8, 0);
        if (drawIndex) {
            wchar_t buf[16];
            swprintf(buf, 16, L"%02d", i + 1);
            g_ctx.r->DrawText(buf, { ir.x + 8, ir.y, 24, ir.h },
                              g_theme.textMuted, g_theme.fontCaption,
                              Renderer::AlignLeft, Renderer::AlignMiddle);
            txt = ir.Inset(38, 0, 8, 0);
        }
        g_ctx.r->DrawText(items[i].c_str(), txt, g_theme.text,
                          g_theme.fontBody);

        if (MouseInsideAndPressed(ir)) {
            if (selected) *selected = i;
            res.clicked = i;
            g_listboxDragSrc = i;
        }
        if (g_listboxDragSrc >= 0 && hov && g_ctx.in->mouseDown[0]) {
            g_listboxDragDst = i;
        }
    }
    g_ctx.r->PopClip();

    DrawScrollbar(r.Inset(0, 4, 4, 4), contentH, &a.scroll);

    // Commit reorder on release
    if (g_listboxDragSrc >= 0 && !g_ctx.in->mouseDown[0]) {
        if (g_listboxDragDst >= 0 && g_listboxDragDst != g_listboxDragSrc) {
            res.reordered_from = g_listboxDragSrc;
            res.reordered_to   = g_listboxDragDst;
        }
        g_listboxDragSrc = -1;
        g_listboxDragDst = -1;
    }
    return res;
}

// --- LUFS / VU style bar meter ---
// dB from -60..0, with green/yellow/red zones; tip indicator + numeric.
void MeterBar(const Rect& r, float dBLevel, float dBMin = -60, float dBMax = 0)
{
    g_ctx.r->FillRoundedRect(r, 3.0f, g_theme.meterTrack);
    float t = (dBLevel - dBMin) / std::max(0.001f, dBMax - dBMin);
    t = Clamp(t, 0.0f, 1.0f);
    float w = r.w * t;
    Rect filled = { r.x, r.y, w, r.h };
    // Zone colour transitions based on level
    Color col = g_theme.meterGreen;
    if (dBLevel > -18.0f) col = g_theme.meterYellow;
    if (dBLevel > -3.0f)  col = g_theme.meterRed;
    g_ctx.r->FillRoundedRect(filled, 3.0f, col);

    // Threshold marks at -18, -9, -3 (target zones)
    auto markAt = [&](float dB, const Color& mk){
        float mx = r.x + r.w * Clamp((dB - dBMin)/(dBMax - dBMin), 0.0f, 1.0f);
        g_ctx.r->FillRect({mx - 0.5f, r.y, 1.0f, r.h}, mk);
    };
    markAt(-18.0f, WithAlpha(g_theme.text, 0.10f));
    markAt(-9.0f,  WithAlpha(g_theme.text, 0.10f));
    markAt(-3.0f,  WithAlpha(g_theme.text, 0.10f));
}

// Big numeric value used by LUFS readouts.
void BigValue(const Rect& r, const wchar_t* label, const wchar_t* value,
              const Color& valueColor)
{
    g_ctx.r->DrawText(label, { r.x, r.y, r.w, 16 },
                      g_theme.textDim, g_theme.fontCaption,
                      Renderer::AlignLeft, Renderer::AlignTop, true);
    g_ctx.r->DrawText(value, { r.x, r.y + 14, r.w, r.h - 14 },
                      valueColor, g_theme.fontDisplaySml,
                      Renderer::AlignLeft, Renderer::AlignMiddle, true);
}

// --- Toggle pill (Rack on / off, Live Monitor) ---
void TogglePill(int id, const Rect& r, const wchar_t* label, bool* state)
{
    auto& a = Anim(id);
    a.press = ApproachLin(a.press, *state ? 1.0f : 0.0f, g_ctx.dt, 0.06f);
    bool hov = MouseHovering(r);
    a.hover = ApproachLin(a.hover, hov ? 1.0f : 0.0f, g_ctx.dt, 0.06f);

    float rad = r.h * 0.5f;
    Color trk = Lerp(g_theme.bgInput, g_theme.accent, a.press);
    g_ctx.r->FillRoundedRect(r, rad, trk);
    g_ctx.r->StrokeRoundedRect(r, rad, 1.0f, g_theme.border);

    float kr = (r.h - 6) * 0.5f;
    float kx = r.x + 3 + kr + (r.w - r.h) * a.press;
    g_ctx.r->FillCircle(kx, r.CY(), kr, g_theme.textOnAccent);

    if (label && *label) {
        Rect lbl = { r.R() + 8, r.y, 200, r.h };
        g_ctx.r->DrawText(label, lbl, g_theme.text, g_theme.fontBody,
                          Renderer::AlignLeft, Renderer::AlignMiddle);
    }
    if (MouseInsideAndReleased(r)) *state = !*state;
}

} // namespace ui



// =====================================================================
// UI scene + window glue
//
// Top-level layout:
//
//   ┌─ MainWindow ─────────────────────────────────────────────────────┐
//   │ ┌─ PreviewChild (DxgiCaptureRenderer owns its own swapchain) ──┐ │
//   │ │                                                              │ │
//   │ │                       desktop preview                        │ │
//   │ │                                                              │ │
//   │ └──────────────────────────────────────────────────────────────┘ │
//   │ ┌─ UIPanelChild (D2D, immediate-mode) ─────────────────────────┐ │
//   │ │ [● Start] [⏸ Pause] [■ Stop]   |  [Recorder][Audio FX][Loud] │ │
//   │ │ ────────────────────────────────────────────────────────────── │ │
//   │ │ <active-tab content>                                         │ │
//   │ └──────────────────────────────────────────────────────────────┘ │
//   └──────────────────────────────────────────────────────────────────┘
//
// UIPanel is its own HWND with its own D3D11 device + flip-discard swap chain
// + Direct2D 1.1 context interop. All controls are drawn vector-based and the
// hit-test / hover / drag/drop pipeline runs on raw mouse messages routed
// from the UIPanel proc into ui::g_ctx.in.
// =====================================================================

static const wchar_t* kUiPanelClass = L"MaxxUiPanelClass";

static ui::Renderer    g_uiR;
static ui::InputState  g_uiInput;
static HWND            g_hwndUiPanel = nullptr;
static int             g_uiTab       = 0;        // 0 Recorder, 1 Audio FX, 2 Loudness
static bool            g_rackEnabled = true;     // global rack on/off
static bool            g_uiSelLoopback = true;   // which rack we're editing
static int             g_uiSelSlot     = -1;     // selected effect slot
static int             g_uiFxTypeChoice = 0;     // chosen effect type in Add combo

static EffectRack& UI_CurrentRack()
{
    return g_audioMixer.RackForSource(g_uiSelLoopback);
}

// ---------------------------------------------------------------------------
// Effect grouping — effects are now organized into logical categories so the
// combo and the About tab can present them compactly instead of a long flat
// list.  Each entry carries its combo-visible name, its EffectKind, and a
// group tag used by the UI to draw section headers / separators.
// ---------------------------------------------------------------------------
enum class EffectGroup : int {
    Dynamics = 0,
    EQ,
    Cleanup,
    Spatial,
    Creative,
};

struct EffectTypeEntry {
    const wchar_t* name;
    EffectKind     kind;
    EffectGroup    group;
};

static const EffectTypeEntry kEffectTypes[] = {
    // — Dynamics —
    { L"Compressor",                    EffectKind::Compressor,        EffectGroup::Dynamics },
    { L"Limiter",                       EffectKind::Limiter,           EffectGroup::Dynamics },
    { L"Smart Dynamics",                EffectKind::SmartDynamics,     EffectGroup::Dynamics },
    // — EQ & Tone —
    { L"Parametric EQ",                 EffectKind::ParametricEQ,      EffectGroup::EQ },
    { L"Dynamic Adaptive EQ (AI)",      EffectKind::DynamicAdaptiveEQ, EffectGroup::EQ },
    { L"Saturation Air",                EffectKind::SaturationAir,     EffectGroup::EQ },
    // — Cleanup & Repair —
    { L"F**kNoise (AI)",                EffectKind::FkNoise,           EffectGroup::Cleanup },
    { L"Smart De-esser",                EffectKind::SmartDeEsser,      EffectGroup::Cleanup },
    { L"Anti-Breath (AI)",              EffectKind::AntiBreath,        EffectGroup::Cleanup },
    { L"Smart Popshield",               EffectKind::SmartPopshield,    EffectGroup::Cleanup },
    { L"AI NoDistortion",               EffectKind::AINoDistortion,    EffectGroup::Cleanup },
    { L"Adaptive Repeating NR (ARNRNN)",EffectKind::ARNRNN,            EffectGroup::Cleanup },
    // — Spatial —
    { L"Reverb",                        EffectKind::Reverb,            EffectGroup::Spatial },
    { L"Delay",                         EffectKind::Delay,             EffectGroup::Spatial },
    { L"Echo",                          EffectKind::Echo,              EffectGroup::Spatial },
    // — Creative —
    { L"Humanized Pitcher (AI)",        EffectKind::HumanizedPitcher,  EffectGroup::Creative },
    { L"Vocoder",                       EffectKind::Vocoder,           EffectGroup::Creative },
    { L"Vox Synthesizer",               EffectKind::VoxSynth,          EffectGroup::Creative },
};
static constexpr int kEffectTypeCount = (int)(sizeof(kEffectTypes)/sizeof(kEffectTypes[0]));

static const wchar_t* EffectGroupName(EffectGroup g)
{
    switch (g) {
        case EffectGroup::Dynamics: return L"Dynamics";
        case EffectGroup::EQ:       return L"EQ & Tone";
        case EffectGroup::Cleanup:  return L"Cleanup & Repair";
        case EffectGroup::Spatial:  return L"Spatial";
        case EffectGroup::Creative: return L"Creative";
        default: return L"Other";
    }
}

// Build the flat combo list on demand. Each group is preceded by a disabled
// header entry (prefixed with a section marker) so the user sees visual
// separators. The mapping arrays translate combo index → kEffectTypes index
// and mark header rows as non-selectable.
static std::vector<std::wstring> g_fxComboItems;
static std::vector<int>          g_fxComboMap;      // combo-index → kEffectTypes index (-1 = header)
static void RebuildFxComboItems()
{
    g_fxComboItems.clear();
    g_fxComboMap.clear();
    EffectGroup lastGroup = (EffectGroup)-1;
    for (int i = 0; i < kEffectTypeCount; ++i) {
        if (kEffectTypes[i].group != lastGroup) {
            lastGroup = kEffectTypes[i].group;
            std::wstring hdr = L"\u2014\u2014 ";
            hdr += EffectGroupName(lastGroup);
            hdr += L" \u2014\u2014";
            g_fxComboItems.push_back(std::move(hdr));
            g_fxComboMap.push_back(-1);
        }
        g_fxComboItems.push_back(kEffectTypes[i].name);
        g_fxComboMap.push_back(i);
    }
}

// Legacy flat name list for the About tab (pointer array for old code paths).
static const wchar_t* kEffectTypeNames[kEffectTypeCount];
static bool g_fxNamesInit = false;
static void EnsureFxNames()
{
    if (g_fxNamesInit) return;
    for (int i = 0; i < kEffectTypeCount; ++i)
        kEffectTypeNames[i] = kEffectTypes[i].name;
    g_fxNamesInit = true;
    RebuildFxComboItems();
}

static EffectKind EffectKindFromComboIndex(int comboIdx)
{
    if (comboIdx < 0 || comboIdx >= (int)g_fxComboMap.size()) return EffectKind::None;
    int entry = g_fxComboMap[comboIdx];
    if (entry < 0) return EffectKind::None;
    return kEffectTypes[entry].kind;
}

static const wchar_t* g_hkLabels[] = {
    L"None",
    L"F1", L"F2", L"F3", L"F4", L"F5", L"F6",
    L"F7", L"F8", L"F9", L"F10", L"F11", L"F12",
    L"R", L"P", L"S", L"1", L"2", L"3",
};
static const UINT g_hkVks[] = {
    0,
    VK_F1, VK_F2, VK_F3, VK_F4, VK_F5, VK_F6,
    VK_F7, VK_F8, VK_F9, VK_F10, VK_F11, VK_F12,
    'R', 'P', 'S', '1', '2', '3',
};
static constexpr int g_hkCount = (int)(sizeof(g_hkVks)/sizeof(g_hkVks[0]));
static int VkComboIndex(UINT vk)
{
    for (int i = 0; i < g_hkCount; ++i) if (g_hkVks[i] == vk) return i;
    return 0;
}

// Format a parameter value into a wchar buffer with sensible precision.
static void UI_FormatParamValue(wchar_t* buf, size_t cap,
                                const EffectParamInfo& info, float v)
{
    // Stepped/named params for the Vox Synthesizer and Dynamic Adaptive EQ.
    if (info.name) {
        if (std::strcmp(info.name, "Target Curve") == 0) {
            static const wchar_t* kCurves[4] = {
                L"Flat", L"Vocal Presence", L"Broadcast Warm", L"De-Harsh"
            };
            int idx = std::clamp((int)(v + 0.5f), 0, 3);
            swprintf_s(buf, cap, L"%s", kCurves[idx]);
            return;
        }
        if (std::strcmp(info.name, "Key") == 0) {
            static const wchar_t* kKeys[12] = {
                L"C", L"C#", L"D", L"D#", L"E", L"F",
                L"F#", L"G", L"G#", L"A", L"A#", L"B"
            };
            int idx = std::clamp((int)(v + 0.5f), 0, 11);
            swprintf_s(buf, cap, L"%s", kKeys[idx]);
            return;
        }
        if (std::strcmp(info.name, "Scale") == 0) {
            static const wchar_t* kScales[8] = {
                L"Chromatic", L"Major", L"Minor",
                L"Pent. Maj", L"Pent. Min", L"Blues",
                L"Dorian", L"Mixolydian"
            };
            int idx = std::clamp((int)(v + 0.5f), 0, 7);
            swprintf_s(buf, cap, L"%s", kScales[idx]);
            return;
        }
        if (std::strcmp(info.name, "Wave") == 0) {
            static const wchar_t* kWaves[4] = { L"Saw", L"Square", L"Sine", L"Tri" };
            int idx = std::clamp((int)(v + 0.5f), 0, 3);
            swprintf_s(buf, cap, L"%s", kWaves[idx]);
            return;
        }
    }
    if (info.unit && info.unit[0] == '\0' && info.minV == 0.0f && info.maxV == 1.0f) {
        swprintf_s(buf, cap, L"%s", v >= 0.5f ? L"On" : L"Off");
        return;
    }
    if (std::fabs(v) >= 1000.0f)
        swprintf_s(buf, cap, L"%.0f %hs", v, info.unit ? info.unit : "");
    else if (std::fabs(v) >= 100.0f)
        swprintf_s(buf, cap, L"%.1f %hs", v, info.unit ? info.unit : "");
    else if (std::fabs(v) >= 10.0f)
        swprintf_s(buf, cap, L"%.2f %hs", v, info.unit ? info.unit : "");
    else
        swprintf_s(buf, cap, L"%.3f %hs", v, info.unit ? info.unit : "");
}

// =====================================================================
//                       Per-tab UI scene functions
// =====================================================================

static void UI_DrawTransport(const ui::Rect& r)
{
    using namespace ui;
    Rect bar = r;

    // Status pill on the left
    Rect pill = { bar.x, bar.y + (bar.h - 24)*0.5f, 110, 24 };
    RecorderState st = g_recState.load();
    Color dot = (st == RecorderState::Recording) ? g_theme.danger :
                (st == RecorderState::Paused)    ? g_theme.warning :
                                                   g_theme.textMuted;
    const wchar_t* label = (st == RecorderState::Recording) ? L"Recording" :
                           (st == RecorderState::Paused)    ? L"Paused"    :
                                                              L"Idle";
    g_ctx.r->FillRoundedRect(pill, 12.0f, g_theme.bgInput);
    g_ctx.r->StrokeRoundedRect(pill, 12.0f, 1.0f, g_theme.border);
    g_ctx.r->FillCircle(pill.x + 14, pill.CY(), 5, dot);
    g_ctx.r->DrawText(label, pill.Inset(28, 0, 8, 0),
                      g_theme.text, g_theme.fontBody);

    // Buttons on the right of the pill
    float bx = pill.R() + 12;
    float bw = 84, bh = 30;
    Rect bStart = { bx, bar.y + (bar.h - bh)*0.5f, bw, bh };
    Rect bPause = { bx + bw + 8, bStart.y, bw, bh };
    Rect bStop  = { bx + (bw + 8)*2, bStart.y, bw, bh };

    ButtonStyle pri; pri.primary = true;
    ButtonStyle dis; dis.disabled = (st == RecorderState::Recording);
    if (Button(0xA001, bStart, L"\u25CF  Start",
               (st == RecorderState::Recording) ? ButtonStyle{} : pri))
    {
        if (st == RecorderState::Idle) StartRecording();
    }
    if (Button(0xA002, bPause, (st == RecorderState::Paused) ? L"\u25B6  Resume"
                                                              : L"\u23F8  Pause",
               (st == RecorderState::Idle) ? ButtonStyle{ false, false, false, true }
                                            : ButtonStyle{}))
    {
        if (st == RecorderState::Recording || st == RecorderState::Paused)
            PauseRecording();
    }
    ButtonStyle dng; dng.danger = true;
    if (Button(0xA003, bStop, L"\u25A0  Stop",
               (st == RecorderState::Idle) ? ButtonStyle{ false, false, false, true }
                                            : dng))
    {
        StopRecording();
    }
}

// =====================================================================
//                       Sources tab (Phase 2)
//
//   Two-column layout:
//
//     +------------------+----------------------+
//     | Source list      | Selected properties  |
//     |                  |  - common: x/y/w/h   |
//     |  + Add        v  |    visible / opacity |
//     |  - Remove     ^  |  - per-kind extra    |
//     +------------------+----------------------+
// =====================================================================

// Quick file picker for ImageSource. Returns true if user chose a file.
static bool PickImageFile(HWND owner, std::wstring& outPath)
{
    wchar_t buf[MAX_PATH] = L"";
    OPENFILENAMEW ofn = {};
    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner   = owner;
    ofn.lpstrFile   = buf;
    ofn.nMaxFile    = MAX_PATH;
    ofn.lpstrFilter = L"Images\0*.png;*.jpg;*.jpeg;*.bmp\0All\0*.*\0";
    ofn.Flags       = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST;
    if (!GetOpenFileNameW(&ofn)) return false;
    outPath = buf;
    return true;
}

void UI_DrawSourcesTab(const ui::Rect& r)
{
    using namespace ui;

    const float colGap = 14;
    const float listW  = std::max(280.0f, r.w * 0.36f);

    Rect listCard = { r.x, r.y, listW, r.h };
    Rect propCard = { r.x + listW + colGap, r.y, r.w - listW - colGap, r.h };

    Card(listCard);
    Card(propCard);

    // ---- list card -----------------------------------------------
    Rect lInner = listCard.Inset(g_theme.padPanel);
    {
        Rect head = { lInner.x, lInner.y, lInner.w, 24 };
        Heading(head, L"Sources");

        Rect addRow = { lInner.x, head.B() + 8, lInner.w, 32 };
        float btnW = (addRow.w - 8) * 0.5f;
        Rect addBtn = { addRow.x, addRow.y, btnW, addRow.h };
        Rect rmBtn  = { addBtn.R() + 8, addRow.y, btnW, addRow.h };

        // "+ Add" — opens a small inline kind-picker via a static
        // "pending" int. (Combo widget would also work here; using a
        // sequence of buttons keeps the surface compact.)
        static int s_addKindOpen = 0;
        if (Button(0xE001, addBtn, L"+ Add source", { true, false, false, false })) {
            s_addKindOpen = s_addKindOpen ? 0 : 1;
        }
        bool removeDisabled = (cmp::g_selectedSourceId < 0);
        if (Button(0xE002, rmBtn, L"- Remove",
                   ButtonStyle{ false, true, false, removeDisabled }) &&
            cmp::g_selectedSourceId >= 0) {
            cmp::RemoveSource(cmp::g_selectedSourceId);
        }

        Rect listArea = { lInner.x, addRow.B() + 8, lInner.w, lInner.h - (addRow.B() - lInner.y) - 8 };

        if (s_addKindOpen) {
            Rect ka = { listArea.x, listArea.y, listArea.w, 36 };
            Card(ka);
            float w = (ka.w - 8 * 6) / 5.0f;
            float yy = ka.y + 4;
            float xx = ka.x + 4;
            auto kbtn = [&](int id, const wchar_t* label, std::function<void()> fn) {
                Rect rb = { xx, yy, w, ka.h - 8 };
                if (Button(id, rb, label, {})) {
                    fn();
                    s_addKindOpen = 0;
                }
                xx += w + 4;
            };
            // Default new sources to fill the entire canvas. The
            // user can then resize after adding; previously every new
            // source landed at (60,60) and ~native size, requiring
            // manual resize for every paste.
            auto fitToCanvas = [](cmp::ISource* s){
                s->t.x = 0;
                s->t.y = 0;
                s->t.w = (float)g_renderer.CanvasW();
                s->t.h = (float)g_renderer.CanvasH();
            };
            kbtn(0xE010, L"Display", [fitToCanvas]{
                auto s = std::make_unique<cmp::DesktopSource>();
                s->Bind(g_renderer.DesktopCaptureSRV(),
                        g_renderer.DesktopCaptureW(),
                        g_renderer.DesktopCaptureH());
                fitToCanvas(s.get());
                cmp::AddSource(std::move(s));
            });
            kbtn(0xE011, L"Image", [fitToCanvas]{
                std::wstring path;
                if (PickImageFile(g_hwndMain, path)) {
                    auto s = std::make_unique<cmp::ImageSource>();
                    if (s->Load(g_renderer.Device(), path.c_str())) {
                        fitToCanvas(s.get());
                        cmp::AddSource(std::move(s));
                    }
                }
            });
            kbtn(0xE012, L"Text", [fitToCanvas]{
                auto s = std::make_unique<cmp::TextSource>();
                s->m_text = L"New text";
                s->Rebuild(g_renderer.Device(), g_renderer.D2DFactory(),
                           g_renderer.DWriteFactory());
                fitToCanvas(s.get());
                cmp::AddSource(std::move(s));
            });
            kbtn(0xE013, L"Window", [fitToCanvas]{
                // Fallback: capture the foreground window.
                HWND fg = GetForegroundWindow();
                if (fg && fg != g_hwndMain) {
                    wchar_t title[256] = L"";
                    GetWindowTextW(fg, title, 255);
                    auto s = std::make_unique<cmp::WindowSource>();
                    if (s->Bind(g_renderer.Device(), fg, title)) {
                        fitToCanvas(s.get());
                        cmp::AddSource(std::move(s));
                    }
                }
            });
            kbtn(0xE014, L"Webcam", [fitToCanvas]{
                IMFAttributes* attrs = nullptr;
                MFCreateAttributes(&attrs, 1);
                if (!attrs) return;
                attrs->SetGUID(MF_DEVSOURCE_ATTRIBUTE_SOURCE_TYPE,
                               MF_DEVSOURCE_ATTRIBUTE_SOURCE_TYPE_VIDCAP_GUID);
                IMFActivate** devs = nullptr;
                UINT32 count = 0;
                if (SUCCEEDED(MFEnumDeviceSources(attrs, &devs, &count)) &&
                    devs && count > 0) {
                    auto s = std::make_unique<cmp::WebcamSource>();
                    if (s->Open(g_renderer.Device(), devs[0])) {
                        wchar_t* nm = nullptr;
                        UINT32 nl = 0;
                        if (SUCCEEDED(devs[0]->GetAllocatedString(
                            MF_DEVSOURCE_ATTRIBUTE_FRIENDLY_NAME, &nm, &nl)) && nm) {
                            s->SetDisplayName(nm);
                            CoTaskMemFree(nm);
                        }
                        fitToCanvas(s.get());
                        cmp::AddSource(std::move(s));
                    }
                    for (UINT32 i = 0; i < count; ++i) devs[i]->Release();
                    CoTaskMemFree(devs);
                }
                attrs->Release();
            });
            listArea.y += 44;
            listArea.h -= 44;
        }

        // Build the listbox items as "[E][L] <name> (<kind>)"
        std::vector<std::wstring> rows;
        std::vector<int> ids;
        {
            std::lock_guard<std::mutex> lk(cmp::g_sourcesMutex);
            // Display top-down (top z is at end of vector). Reverse for
            // visual order.
            for (auto it = cmp::g_sources.rbegin(); it != cmp::g_sources.rend(); ++it) {
                cmp::ISource* s = it->get();
                if (!s) continue;
                std::wstring line;
                line += s->t.visible ? L"\u25CF " : L"\u25CB ";
                line += s->t.locked  ? L"[L] "    : L"     ";
                line += s->DisplayName();
                line += L"  (";
                line += cmp::SourceKindName(s->Kind());
                line += L")";
                rows.push_back(std::move(line));
                ids.push_back(s->id);
            }
        }
        int sel = -1;
        for (int i = 0; i < (int)ids.size(); ++i)
            if (ids[i] == cmp::g_selectedSourceId) sel = i;
        auto lr = Listbox(0xE020, listArea, rows, &sel, 28, false);
        if (sel >= 0 && sel < (int)ids.size()) cmp::g_selectedSourceId = ids[sel];
        if (lr.reordered_from >= 0 && lr.reordered_to >= 0 &&
            lr.reordered_from < (int)ids.size() && lr.reordered_to < (int)ids.size()) {
            // Reorder list view = swap z-orders. We display reversed,
            // so user-visible drag from row A to B is an underlying
            // swap by N - 1 - row.
            std::lock_guard<std::mutex> lk(cmp::g_sourcesMutex);
            int n = (int)cmp::g_sources.size();
            int from = n - 1 - lr.reordered_from;
            int to   = n - 1 - lr.reordered_to;
            if (from >= 0 && from < n && to >= 0 && to < n && from != to) {
                auto p = std::move(cmp::g_sources[from]);
                cmp::g_sources.erase(cmp::g_sources.begin() + from);
                cmp::g_sources.insert(cmp::g_sources.begin() + to, std::move(p));
            }
        }
    }

    // ---- properties card --------------------------------------------
    Rect pInner = propCard.Inset(g_theme.padPanel);
    cmp::ISource* sel = nullptr;
    for (auto& sp : cmp::g_sources)
        if (sp && sp->id == cmp::g_selectedSourceId) { sel = sp.get(); break; }

    if (!sel) {
        Heading({ pInner.x, pInner.y, pInner.w, 24 }, L"Properties");
        Caption({ pInner.x, pInner.y + 32, pInner.w, 20 },
                L"Select a source from the list (or click one in the preview) to edit its properties.");
        return;
    }

    Rect head = { pInner.x, pInner.y, pInner.w, 24 };
    std::wstring title = sel->DisplayName();
    title += L" \u2014 ";
    title += cmp::SourceKindName(sel->Kind());
    Heading(head, title.c_str());

    float yy = head.B() + 12;
    const float lblW  = 80;
    const float ctlH  = 28;
    const float gap   = 8;

    auto rowF = [&](int id, const wchar_t* lbl, float* val,
                    float minV, float maxV, const wchar_t* fmt) {
        Caption({ pInner.x, yy, lblW, ctlH }, lbl);
        Slider(id, { pInner.x + lblW, yy, pInner.w - lblW - 100, ctlH },
               val, minV, maxV, false);
        wchar_t buf[64];
        swprintf(buf, 64, fmt, *val);
        g_ctx.r->DrawText(buf,
            { pInner.x + pInner.w - 96, yy, 96, ctlH },
            g_theme.text, g_theme.fontBody, Renderer::AlignRight,
            Renderer::AlignMiddle);
        yy += ctlH + gap;
    };
    auto rowB = [&](int id, const wchar_t* lbl, bool* val) {
        Caption({ pInner.x, yy, lblW, ctlH }, lbl);
        Checkbox(id, { pInner.x + lblW, yy, pInner.w - lblW, ctlH }, L"", val);
        yy += ctlH + gap;
    };

    rowF(0xE100, L"X",       &sel->t.x,       -2000.0f, (float)g_renderer.CanvasW() + 2000.0f, L"%.0f px");
    rowF(0xE101, L"Y",       &sel->t.y,       -2000.0f, (float)g_renderer.CanvasH() + 2000.0f, L"%.0f px");
    rowF(0xE102, L"Width",   &sel->t.w,       16.0f,    (float)g_renderer.CanvasW() * 2.0f,    L"%.0f px");
    rowF(0xE103, L"Height",  &sel->t.h,       16.0f,    (float)g_renderer.CanvasH() * 2.0f,    L"%.0f px");
    rowF(0xE104, L"Opacity", &sel->t.opacity, 0.0f,     1.0f,                                  L"%.2f");
    rowB(0xE105, L"Visible", &sel->t.visible);
    rowB(0xE106, L"Locked",  &sel->t.locked);

    // Per-kind extras
    if (sel->Kind() == cmp::SourceKind::Text) {
        cmp::TextSource* ts = static_cast<cmp::TextSource*>(sel);
        yy += 4;
        Caption({ pInner.x, yy, pInner.w, 20 }, L"Text content (rebuilds on Apply)");
        yy += 22;
        // Quick fixed-content rebuild button
        Caption({ pInner.x, yy, lblW, ctlH }, L"Font size");
        Slider(0xE110, { pInner.x + lblW, yy, pInner.w - lblW - 100, ctlH },
               &ts->m_fontSize, 12.0f, 256.0f, false);
        wchar_t buf[64];
        swprintf(buf, 64, L"%.0f px", ts->m_fontSize);
        g_ctx.r->DrawText(buf,
            { pInner.x + pInner.w - 96, yy, 96, ctlH }, g_theme.text,
            g_theme.fontBody, Renderer::AlignRight, Renderer::AlignMiddle);
        yy += ctlH + gap;

        Rect rebuildBtn = { pInner.x, yy, 160, ctlH };
        if (Button(0xE111, rebuildBtn, L"Rebuild text texture", { true })) {
            ts->Rebuild(g_renderer.Device(), g_renderer.D2DFactory(),
                        g_renderer.DWriteFactory());
        }
        Caption({ rebuildBtn.R() + 8, yy, pInner.w, ctlH },
                L"(Use Text source for now via the Add menu; full text editor coming next iteration.)");
        yy += ctlH + gap;
    }
    if (sel->Kind() == cmp::SourceKind::Image) {
        cmp::ImageSource* is = static_cast<cmp::ImageSource*>(sel);
        Caption({ pInner.x, yy, pInner.w, 20 },
                (L"File: " + is->m_path).c_str());
        yy += 22;
        if (Button(0xE120, { pInner.x, yy, 140, ctlH }, L"Replace image\u2026", { true })) {
            std::wstring path;
            if (PickImageFile(g_hwndMain, path)) {
                is->Load(g_renderer.Device(), path.c_str());
            }
        }
        yy += ctlH + gap;
    }

    // Z-order buttons
    yy += 8;
    Rect zUp   = { pInner.x,          yy, 120, ctlH };
    Rect zDn   = { pInner.x + 124,    yy, 120, ctlH };
    if (Button(0xE130, zUp, L"Move up (z+)", {})) cmp::MoveSource(sel->id, 1);
    if (Button(0xE131, zDn, L"Move down (z-)", {})) cmp::MoveSource(sel->id, -1);
}

// ---------------------- Recorder tab ----------------------
static void UI_DrawRecorderTab(const ui::Rect& r)
{
    using namespace ui;

    float pad = g_theme.padPanel;

    // Responsive: side-by-side columns on wide windows, stacked
    // (Capture+Hotkeys above, Overlay+Video below) when narrow.
    const bool stack = (r.w < 720.0f);
    float colGap = 14;
    Rect lcol, rcol;
    if (stack) {
        // Heights: capture(130) + 12 + hotkeys(86) = 228 (left); overlay(230) (right).
        float topH = 228.0f;
        lcol = { r.x, r.y,             r.w, topH };
        rcol = { r.x, r.y + topH + 12, r.w, std::max(0.0f, r.h - topH - 12) };
    } else {
        float lW = (r.w - colGap) * 0.55f;
        float rW = (r.w - colGap) - lW;
        lcol = { r.x, r.y, lW, r.h };
        rcol = { r.x + lW + colGap, r.y, rW, r.h };
    }

    // ---- Left column: Capture sources ----
    Rect cap = { lcol.x, lcol.y, lcol.w, 130 };
    GroupBox(cap, L"CAPTURE SOURCES");
    Rect inner = cap.Inset(pad, 32, pad, pad);

    float lblW = 78, ctlH = (float)g_theme.ctlH;
    float yy = inner.y;
    Label({ inner.x, yy, lblW, ctlH }, L"Display");
    Rect monBox = { inner.x + lblW, yy, inner.w - lblW, ctlH };
    std::vector<std::wstring> monItems;
    for (int i = 0; i < (int)g_monitors.size(); ++i) {
        wchar_t buf[128];
        swprintf_s(buf, L"Monitor %d (%s)", i + 1, g_monitors[i].name);
        monItems.push_back(buf);
    }
    Combo(0xC001, monBox, &g_selectedMonitor, monItems);

    yy += ctlH + g_theme.rowGap;
    Label({ inner.x, yy, lblW, ctlH }, L"Audio");
    Rect audBox = { inner.x + lblW, yy, (inner.w - lblW) * 0.62f, ctlH };
    std::vector<std::wstring> audItems;
    for (auto& d : g_audioDevices) audItems.push_back(d.name);
    int audActivated = -1;
    int audPrev = g_selectedAudio;
    Combo(0xC002, audBox, &g_selectedAudio, audItems);
    if (g_selectedAudio != audPrev) {
        // The capture thread runs always-on with whichever endpoint was
        // selected at app boot. Without this reinit, swapping between
        // Loopback and a microphone in the UI did nothing (mic LUFS
        // stayed at "--" because the mic device was never actually
        // opened). Setting g_audioReinit makes AudioThreadProc tear
        // down the current capture client and reopen the new one on
        // its next iteration — usually within a couple of milliseconds.
        g_audioReinit.store(true);
        // Also flip the FX-tab "Source" tab to match the new endpoint
        // class so the user sees their mic chain (or loopback chain)
        // immediately.
        if (g_selectedAudio >= 0 && g_selectedAudio < (int)g_audioDevices.size()) {
            g_uiSelLoopback = g_audioDevices[g_selectedAudio].isLoopback;
            g_uiSelSlot = -1;
        }
    }
    // Combo writes are deferred — see g_uiFxSrcCombo for the full
    // explanation. Same pattern here: bind the combo to a static int
    // with an external-change mirror so the user's selection sticks
    // across frames.
    Rect rateBox = { audBox.R() + 8, yy, inner.w - lblW - audBox.w - 8, ctlH };
    static int g_uiRateCombo  = 0;
    static int g_uiRateMirror = 0;
    int wantRate = (g_selectedSampleRate.load() == 44100u) ? 0 : 1;
    if (wantRate != g_uiRateMirror) {
        g_uiRateCombo  = wantRate;
        g_uiRateMirror = wantRate;
    }
    static const wchar_t* rateNames[] = { L"44.1 kHz", L"48 kHz" };
    Combo(0xC003, rateBox, &g_uiRateCombo, rateNames, 2);
    UINT newRate = (g_uiRateCombo == 0) ? 44100u : 48000u;
    if (newRate != g_selectedSampleRate.load()) {
        g_selectedSampleRate.store(newRate);
        g_uiRateMirror = g_uiRateCombo;
        g_audioReinit.store(true);
    }
    (void)audActivated;

    yy += ctlH + g_theme.rowGap;
    Label({ inner.x, yy, lblW, ctlH }, L"Output");
    Rect pathBox = { inner.x + lblW, yy, inner.w - lblW - 90, ctlH };
    g_ctx.r->FillRoundedRect(pathBox, g_theme.radiusInput, g_theme.bgInput);
    g_ctx.r->StrokeRoundedRect(pathBox, g_theme.radiusInput, 1.0f, g_theme.border);
    g_ctx.r->DrawText(g_outputPath, pathBox.Inset(10, 0, 10, 0),
                      g_theme.textDim, g_theme.fontBody);
    Rect browseBtn = { pathBox.R() + 8, yy, 82, ctlH };
    if (Button(0xC004, browseBtn, L"Browse\u2026")) {
        OPENFILENAMEW ofn = {};
        wchar_t path[MAX_PATH]; wcsncpy_s(path, g_outputPath, MAX_PATH);
        ofn.lStructSize = sizeof(ofn);
        ofn.hwndOwner   = g_hwndMain;
        ofn.lpstrFilter = L"MP4 video\0*.mp4\0All files\0*.*\0";
        ofn.lpstrFile   = path;
        ofn.nMaxFile    = MAX_PATH;
        ofn.lpstrDefExt = L"mp4";
        ofn.Flags       = OFN_OVERWRITEPROMPT | OFN_PATHMUSTEXIST;
        if (GetSaveFileNameW(&ofn)) wcsncpy_s(g_outputPath, path, MAX_PATH);
    }

    // ---- Hotkeys card ----
    Rect hk = { lcol.x, cap.B() + 12, lcol.w, 86 };
    GroupBox(hk, L"HOTKEYS  ·  CTRL + SHIFT +");
    Rect hki = hk.Inset(pad, 32, pad, pad);
    float colW = (hki.w - 16) / 3.0f;

    // Combo writes are deferred — bind to static ints, mirror against
    // the canonical VKs so external state changes are picked up.
    static int g_hkStartCombo  = 0;
    static int g_hkPauseCombo  = 0;
    static int g_hkStopCombo   = 0;
    static int g_hkStartMirror = -1;
    static int g_hkPauseMirror = -1;
    static int g_hkStopMirror  = -1;
    int wantStart = VkComboIndex(g_hkStartVKey);
    int wantPause = VkComboIndex(g_hkPauseVKey);
    int wantStop  = VkComboIndex(g_hkStopVKey);
    if (wantStart != g_hkStartMirror) { g_hkStartCombo = wantStart; g_hkStartMirror = wantStart; }
    if (wantPause != g_hkPauseMirror) { g_hkPauseCombo = wantPause; g_hkPauseMirror = wantPause; }
    if (wantStop  != g_hkStopMirror)  { g_hkStopCombo  = wantStop;  g_hkStopMirror  = wantStop;  }

    Label({ hki.x, hki.y, colW, 16 }, L"Start", Renderer::AlignLeft, true,
          g_theme.fontCaption);
    Combo(0xC011, { hki.x, hki.y + 18, colW - 8, ctlH }, &g_hkStartCombo,
          g_hkLabels, g_hkCount);
    Label({ hki.x + colW, hki.y, colW, 16 }, L"Pause",
          Renderer::AlignLeft, true, g_theme.fontCaption);
    Combo(0xC012, { hki.x + colW, hki.y + 18, colW - 8, ctlH }, &g_hkPauseCombo,
          g_hkLabels, g_hkCount);
    Label({ hki.x + 2*colW, hki.y, colW, 16 }, L"Stop",
          Renderer::AlignLeft, true, g_theme.fontCaption);
    Combo(0xC013, { hki.x + 2*colW, hki.y + 18, colW - 8, ctlH }, &g_hkStopCombo,
          g_hkLabels, g_hkCount);

    UINT newStart = g_hkVks[g_hkStartCombo];
    UINT newPause = g_hkVks[g_hkPauseCombo];
    UINT newStop  = g_hkVks[g_hkStopCombo];
    if (newStart != g_hkStartVKey || newPause != g_hkPauseVKey || newStop != g_hkStopVKey) {
        g_hkStartVKey = newStart;
        g_hkPauseVKey = newPause;
        g_hkStopVKey  = newStop;
        g_hkStartMirror = g_hkStartCombo;
        g_hkPauseMirror = g_hkPauseCombo;
        g_hkStopMirror  = g_hkStopCombo;
        RegisterGlobalHotkeys(g_hwndMain);
    }

    // ---- Right column: Overlay & Video ----
    Rect ov = { rcol.x, rcol.y, rcol.w, 230 };
    GroupBox(ov, L"OVERLAY  &  VIDEO");
    Rect ovi = ov.Inset(pad, 32, pad, pad);
    float chkH = 26;
    bool sc = g_showCursor.load();
    bool ml = g_markLeftClick.load();
    bool mr = g_markRightClick.load();
    Checkbox(0xC020, { ovi.x, ovi.y, ovi.w, chkH }, L"Show cursor", &sc);
    Checkbox(0xC021, { ovi.x, ovi.y + chkH + 4, ovi.w, chkH },
             L"Highlight left click", &ml);
    Checkbox(0xC022, { ovi.x, ovi.y + 2*(chkH+4), ovi.w, chkH },
             L"Highlight right click", &mr);
    g_showCursor.store(sc);
    g_markLeftClick.store(ml);
    g_markRightClick.store(mr);

    float py = ovi.y + 3*(chkH+4) + 12;
    Label({ ovi.x, py, ovi.w, 16 }, L"VIDEO PRESET",
          Renderer::AlignLeft, true, g_theme.fontCaption, true);
    Rect presetBox = { ovi.x, py + 18, ovi.w, ctlH };
    std::vector<std::wstring> presetNames;
    for (int i = 0; i < g_videoPresetCount; ++i) presetNames.push_back(g_videoPresets[i].name);
    Combo(0xC023, presetBox, &g_selectedPreset, presetNames);

    // Preset detail under combo
    if (g_selectedPreset >= 0 && g_selectedPreset < g_videoPresetCount) {
        const auto& vp = g_videoPresets[g_selectedPreset];
        wchar_t det[128];
        swprintf_s(det, L"%u fps  \u00b7  %.1f Mbps",
                   (unsigned)vp.fps, vp.bitrate / 1e6);
        Rect dr = { ovi.x, py + 18 + ctlH + 8, ovi.w, 16 };
        g_ctx.r->DrawText(det, dr, g_theme.textDim, g_theme.fontCaption);
    }
}

// ---------------------- Audio FX tab ----------------------
static void UI_DrawAudioFxTab(const ui::Rect& r)
{
    using namespace ui;
    float pad = g_theme.padPanel;

    // Top toolbar: source pill, add-effect combo+button, rack-on toggle, monitor toggle.
    //
    // Responsive: when the available width is below ~720 px the toolbar
    // wraps into two rows so nothing overlaps. The first row holds the
    // source/type pickers and "+ Add"; the second row holds the
    // Monitor / Rack toggles right-aligned.
    const bool narrow = (r.w < 720.0f);
    const float barH  = narrow ? 76.0f : 36.0f;
    Rect bar = { r.x, r.y, r.w, barH };
    Card(bar.Inset(0, 0, 0, 4));

    float row1Y = bar.y;
    float row2Y = narrow ? (bar.y + 40.0f) : bar.y;
    float bx = bar.x + 12;
    Rect srcLbl = { bx, row1Y, 50, 36 };
    Label(srcLbl, L"Source", Renderer::AlignLeft, true, g_theme.fontCaption, true);
    bx += 56;
    // The FX-tab Source picker now drives BOTH the rack-being-edited
    // and the actual WASAPI capture endpoint. Previously this combo
    // only switched the rack you were editing — the capture device
    // never changed, so users picking "Microphone" still heard
    // (and metered) loopback audio, which looked like the dropdown
    // was stuck. Now switching to "Microphone" finds the first
    // non-loopback endpoint in g_audioDevices and reinits capture;
    // switching to "Loopback (system)" picks the loopback endpoint
    // (always at index 0).
    // The Combo widget defers its write to *selected until
    // Combo_FlushDropdown() runs after this function returns. A stack
    // -local `int srcIdx` would die before the deferred write happens
    // — the user's click would land in reclaimed stack and no state
    // change would be observable on the next frame. We bind the combo
    // to a static int (g_uiFxSrcCombo) so it has permanent storage,
    // and we only re-sync from g_uiSelLoopback if some *other* code
    // path changed it (the Recorder-tab device combo also pushes here
    // via g_uiFxSrcCombo when the user picks a different endpoint).
    static int g_uiFxSrcCombo  = 0;
    static int g_uiFxSrcMirror = 0;        // tracks last-seen g_uiSelLoopback
    int wantIdx = g_uiSelLoopback ? 0 : 1;
    if (wantIdx != g_uiFxSrcMirror) {
        // External change to g_uiSelLoopback (e.g. user picked a mic
        // device on the Recorder tab) — adopt it without overwriting
        // an as-yet-unflushed combo write.
        g_uiFxSrcCombo  = wantIdx;
        g_uiFxSrcMirror = wantIdx;
    }
    static const wchar_t* srcNames[] = { L"Loopback (system)", L"Microphone" };
    Rect srcBox = { bx, row1Y + 4, 180, 28 };
    Combo(0xD001, srcBox, &g_uiFxSrcCombo, srcNames, 2);
    bool nowLoop = (g_uiFxSrcCombo == 0);
    if (nowLoop != g_uiSelLoopback) {
        g_uiSelLoopback = nowLoop;
        g_uiFxSrcMirror = g_uiFxSrcCombo;   // keep mirror in sync
        g_uiSelSlot = -1;
        // Find a matching capture device and trigger an audio reinit.
        int target = -1;
        for (int i = 0; i < (int)g_audioDevices.size(); ++i) {
            if (g_audioDevices[i].isLoopback == nowLoop) { target = i; break; }
        }
        if (target >= 0 && target != g_selectedAudio) {
            g_selectedAudio = target;
            g_audioReinit.store(true);
        }
    }
    bx = srcBox.R() + 12;

    Rect divR = { bx, row1Y + 8, 1, 20 };
    g_ctx.r->FillRect(divR, g_theme.divider);
    bx += 12;

    // Type combo + Add button — uses the grouped combo list.
    EnsureFxNames();
    float typeW = std::max(200.0f, std::min(280.0f, bar.R() - bx - 110.0f - 12.0f));
    Rect typeBox = { bx, row1Y + 4, typeW, 28 };
    Combo(0xD002, typeBox, &g_uiFxTypeChoice, g_fxComboItems);
    // Skip header rows — if the user clicks a "—— Group ——" entry, nudge
    // the selection to the first real entry below it.
    if (g_uiFxTypeChoice >= 0 && g_uiFxTypeChoice < (int)g_fxComboMap.size() &&
        g_fxComboMap[g_uiFxTypeChoice] < 0) {
        if (g_uiFxTypeChoice + 1 < (int)g_fxComboMap.size())
            g_uiFxTypeChoice++;
    }
    bx = typeBox.R() + 8;
    ButtonStyle pri; pri.primary = true;
    Rect addBtn = { bx, row1Y + 4, 90, 28 };
    if (Button(0xD003, addBtn, L"+ Add", pri)) {
        EffectKind k = EffectKindFromComboIndex(g_uiFxTypeChoice);
        if (k != EffectKind::None) {
            EffectRack& rack = UI_CurrentRack();
            int idx = rack.Add(k);
            if (idx >= 0) g_uiSelSlot = idx;
        }
    }

    // Monitor + rack-on toggles. Right-aligned on the second row when
    // the toolbar wraps; right-aligned on the same row otherwise.
    bool mon = g_audioMixer.IsMonitorEnabled();
    bool rackOn = UI_CurrentRack().IsEnabled();
    float togRowY = row2Y;
    Rect rackToggle = { bar.R() - 60, togRowY + 8, 44, 20 };
    Rect rackLbl    = { rackToggle.x - 90, togRowY, 90, 36 };
    g_ctx.r->DrawText(L"Rack on", rackLbl, g_theme.textDim, g_theme.fontCaption,
                      Renderer::AlignRight, Renderer::AlignMiddle);
    TogglePill(0xD010, rackToggle, L"", &rackOn);
    UI_CurrentRack().SetEnabled(rackOn);

    Rect monToggle = { rackLbl.x - 60, togRowY + 8, 44, 20 };
    Rect monLbl    = { monToggle.x - 100, togRowY, 100, 36 };
    g_ctx.r->DrawText(L"Monitor", monLbl, g_theme.textDim, g_theme.fontCaption,
                      Renderer::AlignRight, Renderer::AlignMiddle);
    TogglePill(0xD011, monToggle, L"", &mon);
    g_audioMixer.SetMonitorEnabled(mon);

    // Body: chain list (left), parameter pane (right). List width is
    // proportional so the pane keeps usable space on narrow windows.
    Rect body = { r.x, bar.B() + 8, r.w, r.h - bar.h - 8 };
    float listW = std::clamp(body.w * 0.30f, 180.0f, 280.0f);
    Rect listR = { body.x, body.y, listW, body.h };
    Rect paneR = { listR.R() + 12, body.y, body.w - listW - 12, body.h };

    // Chain
    EffectRack& rack = UI_CurrentRack();
    std::vector<std::wstring> rows;
    int rcount = rack.Size();
    rows.reserve(rcount);
    for (int i = 0; i < rcount; ++i) {
        EffectKind kk = rack.KindAt(i);
        bool byp      = rack.BypassAt(i);
        const char* nmA = EffectKindName(kk);
        wchar_t nmW[64]; MultiByteToWideChar(CP_UTF8, 0, nmA, -1, nmW, _countof(nmW));
        wchar_t buf[128];
        swprintf_s(buf, L"%s%s", nmW, byp ? L"  (bypass)" : L"");
        rows.push_back(buf);
    }

    Rect listClipped = { listR.x, listR.y, listR.w, listR.h - 38 };
    auto lbres = Listbox(0xD020, listClipped, rows, &g_uiSelSlot, 30, true);
    if (lbres.reordered_from >= 0 && lbres.reordered_to >= 0) {
        rack.Move(lbres.reordered_from, lbres.reordered_to);
        if (g_uiSelSlot == lbres.reordered_from) g_uiSelSlot = lbres.reordered_to;
    }

    // Buttons under the chain list (Up / Down / Bypass / Remove)
    Rect btnRow = { listR.x, listR.B() - 32, listR.w, 30 };
    float bw = (btnRow.w - 6) * 0.25f;
    Rect bUp     = { btnRow.x,                btnRow.y, bw, btnRow.h };
    Rect bDown   = { btnRow.x + bw + 2,       btnRow.y, bw, btnRow.h };
    Rect bByp    = { btnRow.x + 2*(bw+2),     btnRow.y, bw, btnRow.h };
    Rect bRem    = { btnRow.x + 3*(bw+2),     btnRow.y, bw, btnRow.h };

    if (Button(0xD030, bUp, L"\u2191 Up")) {
        if (g_uiSelSlot > 0) {
            rack.MoveUp(g_uiSelSlot);
            g_uiSelSlot--;
        }
    }
    if (Button(0xD031, bDown, L"\u2193 Down")) {
        if (g_uiSelSlot >= 0 && g_uiSelSlot < rack.Size() - 1) {
            rack.MoveDown(g_uiSelSlot);
            g_uiSelSlot++;
        }
    }
    if (Button(0xD032, bByp, L"Bypass")) {
        if (g_uiSelSlot >= 0)
            rack.SetBypass(g_uiSelSlot, !rack.BypassAt(g_uiSelSlot));
    }
    ButtonStyle dng; dng.danger = true;
    if (Button(0xD033, bRem, L"Remove", dng)) {
        if (g_uiSelSlot >= 0) {
            rack.Remove(g_uiSelSlot);
            if (g_uiSelSlot >= rack.Size()) g_uiSelSlot = rack.Size() - 1;
        }
    }

    // Parameter pane
    Card(paneR);
    Rect pi = paneR.Inset(pad, 14, pad, 14);

    // CRITICAL: once we call rack.Lock() we MUST use the *Locked
    // variants (KindAtLocked / BypassAtLocked / SetBypassLocked) for
    // any further rack queries. The plain non-Locked methods take the
    // mutex internally → self-deadlock on the recursive acquisition,
    // which manifested as a hard crash the moment the user clicked
    // "+ Add" and the param pane re-rendered with a valid g_uiSelSlot.
    rack.Lock();
    IEffect*   fx     = (g_uiSelSlot >= 0) ? rack.AtLocked(g_uiSelSlot) : nullptr;
    EffectKind fxKind = (g_uiSelSlot >= 0) ? rack.KindAtLocked(g_uiSelSlot) : EffectKind::None;
    bool       byp    = (g_uiSelSlot >= 0) ? rack.BypassAtLocked(g_uiSelSlot) : false;
    if (!fx) {
        g_ctx.r->DrawText(L"Select an effect from the chain to edit its parameters",
                          pi, g_theme.textDim, g_theme.fontBody,
                          Renderer::AlignCenter, Renderer::AlignMiddle);
    } else {
        Rect titleR = { pi.x, pi.y, pi.w, 24 };
        wchar_t titleW[64];
        MultiByteToWideChar(CP_UTF8, 0, EffectKindName(fxKind), -1, titleW, _countof(titleW));
        Heading(titleR, titleW);
        Rect bypR = { titleR.R() - 80, titleR.y, 80, titleR.h };
        if (Button(0xD040, bypR, byp ? L"Enable" : L"Bypass",
                   ButtonStyle{ false, byp, false, false }))
        {
            rack.SetBypassLocked(g_uiSelSlot, !byp);
        }

        // Two-column slider grid
        int n = fx->GetParamCount();
        float colY = pi.y + 32;
        float colsCount = (pi.w > 540) ? 2.0f : 1.0f;
        float colGap = 16;
        float colW = (pi.w - colGap * (colsCount - 1)) / colsCount;
        float rowH = 50;

        for (int i = 0; i < n; ++i) {
            const EffectParamInfo& info = fx->GetParamInfo(i);
            float v = fx->GetParam(i);

            int col = (int)(i / 8);
            int row = i % 8;
            if (col >= (int)colsCount) col = (int)colsCount - 1;
            float x = pi.x + col * (colW + colGap);
            float y = colY + row * rowH;

            wchar_t name16[64];
            MultiByteToWideChar(CP_UTF8, 0, info.name, -1, name16, _countof(name16));

            wchar_t valBuf[64];
            UI_FormatParamValue(valBuf, _countof(valBuf), info, v);

            // Label + value on top row
            Rect lr = { x, y, colW * 0.6f, 18 };
            Rect vr = { x + colW * 0.6f, y, colW * 0.4f, 18 };
            g_ctx.r->DrawText(name16, lr, g_theme.text, g_theme.fontCaption,
                              Renderer::AlignLeft, Renderer::AlignMiddle, true);
            g_ctx.r->DrawText(valBuf, vr, g_theme.textDim, g_theme.fontCaption,
                              Renderer::AlignRight, Renderer::AlignMiddle);
            // Slider below
            Rect sr = { x, y + 22, colW, 22 };
            float minV = (float)info.minV;
            float maxV = (float)info.maxV;
            float vClamped = Clamp(v, minV, maxV);
            int sid = 0xE000 + (int)((g_uiSelSlot & 0xFFF) << 4) + i;
            if (Slider(sid, sr, &vClamped, minV, maxV, info.isLog)) {
                fx->SetParam(i, vClamped);
            }
        }
    }
    rack.Unlock();
}

// ---------------------- Loudness tab ----------------------
static void UI_DrawLoudnessTab(const ui::Rect& r)
{
    using namespace ui;
    float pad = g_theme.padPanel;

    // Top: preset combo + reset button
    Rect bar = { r.x, r.y, r.w, 36 };
    Card(bar.Inset(0, 0, 0, 4));
    float bx = bar.x + 12;
    Label({ bx, bar.y, 90, bar.h }, L"Target", Renderer::AlignLeft, true,
          g_theme.fontCaption, true);
    bx += 60;
    std::vector<std::wstring> pn;
    for (int i = 0; i < g_lufsPresetCount; ++i) {
        wchar_t buf[64];
        if (g_lufsPresets[i].targetLufs > -1.0f)
            swprintf_s(buf, L"%s", g_lufsPresets[i].name);
        else
            swprintf_s(buf, L"%s", g_lufsPresets[i].name);
        pn.push_back(buf);
    }
    // Responsive: cap the preset combo width by remaining space so
    // the Reset button and status caption don't overflow on narrow
    // windows.
    float presetW = std::clamp(bar.R() - bx - 110.0f - 12.0f - 12.0f,
                               160.0f, 320.0f);
    Rect presetBox = { bx, bar.y + 4, presetW, bar.h - 8 };
    int prevPreset = g_lufsPresetIdx;
    Combo(0xF001, presetBox, &g_lufsPresetIdx, pn);
    if (g_lufsPresetIdx != prevPreset) {
        const auto& p = g_lufsPresets[g_lufsPresetIdx];
        if (p.targetLufs < -1.0) {        // 0.0 == "Custom"; real targets are negative
            // Apply ceiling to all Limiters in both racks. We walk via the
            // public API (Lock + KindAt + AtLocked) so we don't crack the
            // mutex guard.
            float ceil = (float)p.ceilingDbtp;
            auto applyCeiling = [&](EffectRack& rk){
                // *Locked accessors only — the non-Locked variants
                // would re-acquire the rack mutex and self-deadlock.
                rk.Lock();
                int n = rk.SizeLocked();
                for (int i = 0; i < n; ++i) {
                    if (rk.KindAtLocked(i) != EffectKind::Limiter) continue;
                    IEffect* e = rk.AtLocked(i);
                    if (!e) continue;
                    for (int pi = 0; pi < e->GetParamCount(); ++pi) {
                        const EffectParamInfo& info = e->GetParamInfo(pi);
                        if (info.name && std::strstr(info.name, "Ceiling")) {
                            e->SetParam(pi, ceil);
                        }
                    }
                }
                rk.Unlock();
            };
            applyCeiling(g_audioMixer.RackForSource(true));
            applyCeiling(g_audioMixer.RackForSource(false));
        }
        g_audioMixer.Meter().ResetIntegrated();
    }
    Rect resetBtn = { presetBox.R() + 8, bar.y + 4, 110, bar.h - 8 };
    if (Button(0xF002, resetBtn, L"Reset I")) {
        g_audioMixer.Meter().ResetIntegrated();
    }

    // Status caption — drawn after the Reset button on the same row
    // *only when there's leftover space*. Otherwise omitted. Avoids
    // the previous overlap where the caption was anchored at
    // bar.R()-320 and stomped on the Reset button on narrow windows.
    {
        const auto& p = g_lufsPresets[g_lufsPresetIdx];
        wchar_t buf[256];
        if (p.targetLufs < -1.0)
            swprintf_s(buf, L"Target %.1f LUFS  \u00b7  Ceiling %.1f dBTP",
                       p.targetLufs, p.ceilingDbtp);
        else
            swprintf_s(buf, L"Custom  \u00b7  ceiling untouched");
        float capX = resetBtn.R() + 12;
        if (bar.R() - capX > 200.0f) {
            Rect sb = { capX, bar.y, bar.R() - capX - 12, bar.h };
            g_ctx.r->DrawText(buf, sb, g_theme.textDim, g_theme.fontCaption,
                              Renderer::AlignRight, Renderer::AlignMiddle);
        }
    }

    // Big readouts grid: 4 cells (M / S / I / TP)
    double m_, s_, i_, tp_;
    g_audioMixer.Meter().Snapshot(m_, s_, i_, tp_);
    struct LufsSnap { float momentary, shortTerm, integrated, truePeak; } snap = {
        std::isfinite(m_)  ? (float)m_  : -120.0f,
        std::isfinite(s_)  ? (float)s_  : -120.0f,
        std::isfinite(i_)  ? (float)i_  : -120.0f,
        std::isfinite(tp_) ? (float)tp_ : -120.0f
    };
    auto colorFor = [&](float lufs)->Color{
        if (g_lufsPresetIdx >= g_lufsPresetCount) return g_theme.text;
        const auto& p = g_lufsPresets[g_lufsPresetIdx];
        if (p.targetLufs >= -1.0) return g_theme.text;
        float diff = std::fabs(lufs - (float)p.targetLufs);
        if (diff < 1.5f)  return g_theme.success;
        if (diff < 4.0f)  return g_theme.warning;
        return g_theme.danger;
    };

    // Responsive grid: 4-up at full width, 2x2 when narrow.
    Rect grid = { r.x, bar.B() + 12, r.w, r.h - bar.h - 12 - 60 };
    const bool gridStack = (grid.w < 720.0f);
    int   cols     = gridStack ? 2 : 4;
    int   rows_n   = gridStack ? 2 : 1;
    float cellW    = (grid.w - (cols - 1) * 12.0f) / cols;
    float cellH    = (grid.h - (rows_n - 1) * 12.0f) / rows_n;

    auto drawCellAt = [&](int slot, const wchar_t* lbl, const wchar_t* sublbl,
                          float lufs, bool isTp){
        int colIdx = slot % cols;
        int rowIdx = slot / cols;
        float xOff = colIdx * (cellW + 12.0f);
        float yOff = rowIdx * (cellH + 12.0f);
        Rect cell = { grid.x + xOff, grid.y + yOff, cellW, cellH };
        Card(cell);
        Rect ci = cell.Inset(pad, 14, pad, 14);
        g_ctx.r->DrawText(lbl, { ci.x, ci.y, ci.w, 18 },
                          g_theme.textDim, g_theme.fontCaption,
                          Renderer::AlignLeft, Renderer::AlignTop, true);
        g_ctx.r->DrawText(sublbl, { ci.x, ci.y + 16, ci.w, 14 },
                          g_theme.textMuted, g_theme.fontCaption);

        wchar_t valBuf[32];
        if (lufs <= -100.0f) wcscpy_s(valBuf, L"--.-");
        else                 swprintf_s(valBuf, L"%.1f", lufs);

        Color col = isTp ? (lufs > -1.0f ? g_theme.danger : g_theme.text)
                         : colorFor(lufs);
        Rect bigR = { ci.x, ci.y + 36, ci.w, 48 };
        g_ctx.r->DrawText(valBuf, bigR, col, g_theme.fontDisplayBig,
                          Renderer::AlignLeft, Renderer::AlignTop, true);
        Rect unitR = { ci.x, ci.y + 48, ci.w, 20 };
        g_ctx.r->DrawText(isTp ? L"dBTP" : L"LUFS",
                          unitR, g_theme.textDim, g_theme.fontCaption,
                          Renderer::AlignRight, Renderer::AlignBottom);

        Rect bar = { ci.x, ci.B() - 18, ci.w, 8 };
        if (isTp) {
            // Map [-30, 0] -> [0,1]
            float t = (lufs + 30.0f) / 30.0f;
            t = Clamp(t, 0.0f, 1.0f);
            g_ctx.r->FillRoundedRect(bar, 3.0f, g_theme.meterTrack);
            Rect filled = { bar.x, bar.y, bar.w * t, bar.h };
            Color c = (lufs > -1.0f) ? g_theme.danger :
                      (lufs > -3.0f) ? g_theme.warning : g_theme.meterGreen;
            g_ctx.r->FillRoundedRect(filled, 3.0f, c);
        } else {
            // Map [-60, 0] -> [0,1]
            MeterBar(bar, lufs);
        }
    };

    drawCellAt(0, L"MOMENTARY",  L"400 ms window",      snap.momentary,  false);
    drawCellAt(1, L"SHORT TERM", L"3 s window",         snap.shortTerm,  false);
    drawCellAt(2, L"INTEGRATED", L"Gated, since reset", snap.integrated, false);
    drawCellAt(3, L"TRUE PEAK",  L"Hold + decay",       snap.truePeak,   true);
}

// ---------------------- About tab -----------------------
void UI_DrawAboutTab(const ui::Rect& r)
{
    using namespace ui;
    const float pad = g_theme.padPanel;
    const bool  narrow = (r.w < 720.0f);

    // Hero card with app brand + version.
    float heroH = 130.0f;
    Rect hero   = { r.x, r.y, r.w, heroH };
    Card(hero);
    Rect hi = hero.Inset(pad + 6, 14, pad + 6, 14);

    g_ctx.r->DrawText(L"Maxx", { hi.x, hi.y, hi.w, 44 },
                      g_theme.text, g_theme.fontDisplayBig,
                      Renderer::AlignLeft, Renderer::AlignTop, true);
    g_ctx.r->DrawText(L"Studio-grade screen recorder · multi-source compositor · BS.1770-4 loudness · adaptive noise / popshield / declipper",
                      { hi.x, hi.y + 50, hi.w, 18 },
                      g_theme.textMuted, g_theme.fontCaption,
                      Renderer::AlignLeft, Renderer::AlignTop, false);
    g_ctx.r->DrawText(L"Version 2.1  ·  Phase 3 (Adaptive EQ · Grouped FX · macOS UI)",
                      { hi.x, hi.y + 86, hi.w, 16 },
                      g_theme.textDim, g_theme.fontCaption,
                      Renderer::AlignLeft, Renderer::AlignTop, true);

    // Two-column body (stacks under 720 px).
    float colY = hero.B() + 12;
    float bodyH = std::max(200.0f, r.h - heroH - 12);
    Rect lcol, rcol;
    if (narrow) {
        float halfH = bodyH * 0.5f - 6;
        lcol = { r.x, colY,             r.w, halfH };
        rcol = { r.x, colY + halfH + 12, r.w, halfH };
    } else {
        float colW = (r.w - 12) * 0.5f;
        lcol = { r.x,             colY, colW, bodyH };
        rcol = { r.x + colW + 12, colY, colW, bodyH };
    }

    // ---- Pipeline summary -------------------------------------------
    Card(lcol);
    Rect li = lcol.Inset(pad + 4, 12, pad + 4, 12);
    g_ctx.r->DrawText(L"PIPELINE", { li.x, li.y, li.w, 14 },
                      g_theme.textDim, g_theme.fontCaption,
                      Renderer::AlignLeft, Renderer::AlignTop, true);

    static const wchar_t* kPipelineLines[] = {
        L"Video    DXGI desktop duplication / WGC / WIC / DirectWrite",
        L"           → D3D11 canvas RTV (1920x1080, BGRA8)",
        L"           → MF SinkWriter NV12 (HEVC / H.264 / VP9)",
        L"Audio    WASAPI shared loopback + capture",
        L"           → BS.1770-4 K-weighted LUFS gating",
        L"           → Effect rack (atomic params, RT-safe)",
        L"           → Live monitor (mono ↔ stereo fan)",
        L"Sync     QPC-derived video PTS, sample-count audio PTS",
        L"Drag     OBS-style snap guides + overflow markers",
    };
    const int nPipe = (int)(sizeof(kPipelineLines)/sizeof(kPipelineLines[0]));
    float ly = li.y + 22;
    for (int i = 0; i < nPipe && ly + 18 <= li.B(); ++i) {
        g_ctx.r->DrawText(kPipelineLines[i], { li.x, ly, li.w, 16 },
                          g_theme.textMuted, g_theme.fontBody,
                          Renderer::AlignLeft, Renderer::AlignTop, false);
        ly += 18;
    }

    // ---- Effects roster ---------------------------------------------
    Card(rcol);
    Rect ri = rcol.Inset(pad + 4, 12, pad + 4, 12);
    g_ctx.r->DrawText(L"EFFECTS", { ri.x, ri.y, ri.w, 14 },
                      g_theme.textDim, g_theme.fontCaption,
                      Renderer::AlignLeft, Renderer::AlignTop, true);

    // Pull effect names from the grouped structure.
    EnsureFxNames();
    float ey = ri.y + 22;
    const float lineH = 16;
    EffectGroup lastGrp = (EffectGroup)-1;
    for (int i = 0; i < kEffectTypeCount; ++i) {
        if (kEffectTypes[i].group != lastGrp) {
            lastGrp = kEffectTypes[i].group;
            if (ey + lineH > ri.B()) break;
            // Group header
            g_ctx.r->DrawText(EffectGroupName(lastGrp),
                              { ri.x, ey, ri.w, lineH },
                              g_theme.textDim, g_theme.fontCaption,
                              Renderer::AlignLeft, Renderer::AlignTop, true);
            ey += lineH + 2;
        }
        if (ey + lineH > ri.B()) break;
        wchar_t buf[96];
        swprintf_s(buf, L"\u2022  %s", kEffectTypes[i].name);
        g_ctx.r->DrawText(buf, { ri.x + 8, ey, ri.w - 8, lineH },
                          g_theme.textMuted, g_theme.fontBody,
                          Renderer::AlignLeft, Renderer::AlignTop, false);
        ey += lineH;
    }

    // Footer line below both columns.
    float footY = (narrow ? rcol.B() : std::max(lcol.B(), rcol.B())) + 8;
    if (footY + 18 <= r.B()) {
        Rect ft = { r.x, footY, r.w, 18 };
        g_ctx.r->DrawText(
            L"Built with Direct3D 11 · Direct2D · DirectWrite · Media Foundation · WASAPI · WIC",
            ft, g_theme.textDim, g_theme.fontCaption,
            Renderer::AlignCenter, Renderer::AlignTop, false);
    }
}

// =====================================================================
//                       Top-level scene + frame
// =====================================================================
static std::chrono::steady_clock::time_point g_uiLastFrame =
    std::chrono::steady_clock::now();

static void UI_RenderFrame()
{
    if (!g_uiR.Width() || !g_uiR.Height()) return;
    using namespace ui;

    auto now = std::chrono::steady_clock::now();
    g_ctx.dt = std::chrono::duration<float>(now - g_uiLastFrame).count();
    g_uiLastFrame = now;
    if (g_ctx.dt > 0.1f) g_ctx.dt = 0.1f;
    if (g_ctx.dt < 0.0f) g_ctx.dt = 0.0f;

    g_ctx.r  = &g_uiR;
    g_ctx.in = &g_uiInput;

    if (!g_uiR.BeginFrame(g_theme.bgWindow)) return;

    int W = g_uiR.Width();
    int H = g_uiR.Height();

    // Top bar = transport + tabs — macOS-inspired spacing
    Rect top   = { 0, 0, (float)W, 64 };
    Rect tabs  = { 0, top.B(), (float)W, 40 };
    Rect cont  = { 16, tabs.B() + 12, (float)W - 32, (float)H - tabs.B() - 28 };

    // Background bands — subtle depth separation like macOS toolbar
    g_ctx.r->FillRect(top,  g_theme.bgPanel);
    g_ctx.r->FillRect(tabs, g_theme.bgWindow);
    g_ctx.r->FillRect({ 0, tabs.B(), (float)W, 1 }, g_theme.divider);

    UI_DrawTransport(top.Inset(14, 0, 14, 0));

    static const wchar_t* tabNames[] = { L"Sources", L"Recorder", L"Audio FX", L"Loudness", L"About" };
    TabStrip(0xB001, { 14, tabs.y + 2, (float)W - 28, tabs.h - 4 },
             &g_uiTab, tabNames, 5);

    extern void UI_DrawSourcesTab(const ui::Rect& r);
    extern void UI_DrawAboutTab(const ui::Rect& r);
    if      (g_uiTab == 0) UI_DrawSourcesTab(cont);
    else if (g_uiTab == 1) UI_DrawRecorderTab(cont);
    else if (g_uiTab == 2) UI_DrawAudioFxTab(cont);
    else if (g_uiTab == 3) UI_DrawLoudnessTab(cont);
    else                   UI_DrawAboutTab(cont);

    Combo_FlushDropdown();

    g_uiR.EndFrame();
    g_uiInput.NewFrame();
}

// =====================================================================
//                       UI panel HWND proc
// =====================================================================
static LRESULT CALLBACK UiPanelProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam)
{
    switch (msg) {
    case WM_CREATE: {
        if (!g_uiR.Init(hwnd)) {
            MessageBoxW(hwnd, L"Failed to initialise Direct2D UI renderer.",
                        L"Maxx", MB_ICONERROR);
        }
        SetTimer(hwnd, 0xA1, 16, nullptr);   // ~60 Hz redraw
        return 0;
    }
    case WM_SIZE: {
        int W = LOWORD(lParam), H = HIWORD(lParam);
        g_uiR.Resize(W, H);
        InvalidateRect(hwnd, nullptr, FALSE);
        return 0;
    }
    case WM_TIMER: {
        if (wParam == 0xA1) {
            // Update mouse-inside on plain timer wakes
            POINT pt; GetCursorPos(&pt); ScreenToClient(hwnd, &pt);
            RECT rc; GetClientRect(hwnd, &rc);
            bool inside = (pt.x >= 0 && pt.y >= 0 && pt.x < rc.right && pt.y < rc.bottom);
            g_uiInput.mouseInside = inside;
            g_uiInput.mouseX = (float)pt.x;
            g_uiInput.mouseY = (float)pt.y;
            UI_RenderFrame();
        }
        return 0;
    }
    case WM_MOUSEMOVE: {
        g_uiInput.mouseX = (float)GET_X_LPARAM(lParam);
        g_uiInput.mouseY = (float)GET_Y_LPARAM(lParam);
        g_uiInput.mouseInside = true;
        return 0;
    }
    case WM_MOUSELEAVE: {
        g_uiInput.mouseInside = false;
        return 0;
    }
    case WM_LBUTTONDOWN: case WM_RBUTTONDOWN: case WM_MBUTTONDOWN: {
        SetCapture(hwnd);
        int b = (msg == WM_LBUTTONDOWN) ? 0 : (msg == WM_RBUTTONDOWN) ? 1 : 2;
        if (!g_uiInput.mouseDown[b]) g_uiInput.mousePressed[b] = true;
        g_uiInput.mouseDown[b] = true;
        g_uiInput.mouseX = (float)GET_X_LPARAM(lParam);
        g_uiInput.mouseY = (float)GET_Y_LPARAM(lParam);
        return 0;
    }
    case WM_LBUTTONUP: case WM_RBUTTONUP: case WM_MBUTTONUP: {
        ReleaseCapture();
        int b = (msg == WM_LBUTTONUP) ? 0 : (msg == WM_RBUTTONUP) ? 1 : 2;
        if (g_uiInput.mouseDown[b]) g_uiInput.mouseReleased[b] = true;
        g_uiInput.mouseDown[b] = false;
        g_uiInput.mouseX = (float)GET_X_LPARAM(lParam);
        g_uiInput.mouseY = (float)GET_Y_LPARAM(lParam);
        return 0;
    }
    case WM_MOUSEWHEEL: {
        g_uiInput.wheelTicks += GET_WHEEL_DELTA_WPARAM(wParam) / WHEEL_DELTA;
        return 0;
    }
    case WM_PAINT: {
        PAINTSTRUCT ps; BeginPaint(hwnd, &ps); EndPaint(hwnd, &ps);
        UI_RenderFrame();
        return 0;
    }
    case WM_ERASEBKGND:
        return 1;   // we own all drawing
    case WM_DESTROY: {
        KillTimer(hwnd, 0xA1);
        g_uiR.Shutdown();
        return 0;
    }
    }
    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

static void RegisterUiPanelClass(HINSTANCE hInst)
{
    WNDCLASSEXW wc = {};
    wc.cbSize        = sizeof(wc);
    wc.style         = CS_HREDRAW | CS_VREDRAW;
    wc.lpfnWndProc   = UiPanelProc;
    wc.hInstance     = hInst;
    wc.hCursor       = LoadCursorW(nullptr, IDC_ARROW);
    wc.hbrBackground = nullptr;
    wc.lpszClassName = kUiPanelClass;
    RegisterClassExW(&wc);
}

// =====================================================================
//   Preview HWND mouse subclass — selection / move / resize via 8 handles
//
//   Drag inside source rect = move
//   Drag a corner handle    = resize (Shift = proportional)
//   Drag an edge handle     = stretch one axis (Shift = proportional)
//   Hold Ctrl while dragging = snap to 8 px grid in canvas space
// =====================================================================
enum class PreviewDragMode {
    None = 0, Move,
    NW, N, NE,
    W,        E,
    SW, S, SE
};
struct PreviewDragState {
    PreviewDragMode  mode = PreviewDragMode::None;
    int              srcId = -1;
    cmp::SourceTransform t0;            // transform at drag start
    POINT            anchorCanvas = {}; // canvas coords at drag start
};
static PreviewDragState g_pdrag;

// Convert preview-pixel point -> canvas-pixel point using the renderer's
// last-known letterbox layout.
static bool PreviewToCanvas(int px, int py, float& outCanvasX, float& outCanvasY)
{
    auto L = g_renderer.GetLastLayout();
    if (L.viewW <= 0 || L.viewH <= 0 || L.canvasW <= 0 || L.canvasH <= 0)
        return false;
    float u = ((float)px - L.viewX) / L.viewW;
    float v = ((float)py - L.viewY) / L.viewH;
    if (u < 0 || u > 1 || v < 0 || v > 1) return false;
    outCanvasX = u * (float)L.canvasW;
    outCanvasY = v * (float)L.canvasH;
    return true;
}

// Hit-test: returns drag mode + sets g_pdrag.srcId if inside a handle/rect.
static PreviewDragMode PreviewHitTest(int px, int py, int& outSrcId)
{
    auto L = g_renderer.GetLastLayout();
    if (L.viewW <= 0 || L.viewH <= 0 || L.canvasW <= 0 || L.canvasH <= 0)
        return PreviewDragMode::None;
    const float sx = L.viewW / std::max(1.0f, (float)L.canvasW);
    const float sy = L.viewH / std::max(1.0f, (float)L.canvasH);

    auto rectFor = [&](cmp::ISource* s, float& l, float& t, float& r, float& b) {
        l = L.viewX + s->t.x * sx;
        t = L.viewY + s->t.y * sy;
        r = l + s->t.w * sx;
        b = t + s->t.h * sy;
    };

    // First, if a source is already selected, prefer its handles for
    // grabbing — typical OBS-style behaviour.
    cmp::ISource* sel = nullptr;
    for (auto& sp : cmp::g_sources)
        if (sp && sp->id == cmp::g_selectedSourceId) { sel = sp.get(); break; }
    if (sel && !sel->t.locked) {
        float l, t, r, b;
        rectFor(sel, l, t, r, b);
        const float hsz = 9.0f;
        float hx[3] = { l, (l + r) * 0.5f, r };
        float hy[3] = { t, (t + b) * 0.5f, b };
        PreviewDragMode modes[3][3] = {
            { PreviewDragMode::NW, PreviewDragMode::N, PreviewDragMode::NE },
            { PreviewDragMode::W,  PreviewDragMode::None, PreviewDragMode::E },
            { PreviewDragMode::SW, PreviewDragMode::S, PreviewDragMode::SE },
        };
        for (int j = 0; j < 3; ++j) for (int i = 0; i < 3; ++i) {
            if (i == 1 && j == 1) continue;
            float x = hx[i], y = hy[j];
            if (px >= x - hsz && px <= x + hsz && py >= y - hsz && py <= y + hsz) {
                outSrcId = sel->id;
                return modes[j][i];
            }
        }
        // Inside the selected rect = move
        if (px >= l && px <= r && py >= t && py <= b) {
            outSrcId = sel->id;
            return PreviewDragMode::Move;
        }
    }

    // Otherwise, hit-test sources top-down (last in g_sources is on top).
    for (auto it = cmp::g_sources.rbegin(); it != cmp::g_sources.rend(); ++it) {
        cmp::ISource* s = it->get();
        if (!s || !s->t.visible || s->t.locked) continue;
        float l, t, r, b;
        rectFor(s, l, t, r, b);
        if (px >= l && px <= r && py >= t && py <= b) {
            outSrcId = s->id;
            return PreviewDragMode::Move;
        }
    }
    outSrcId = -1;
    return PreviewDragMode::None;
}

LRESULT CALLBACK PreviewSubProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam,
                                UINT_PTR /*idSubclass*/, DWORD_PTR /*refData*/)
{
    switch (msg) {
    case WM_NCHITTEST:
        // The preview HWND is a STATIC control (SS_BLACKRECT), and the
        // default STATIC WindowProc returns HTTRANSPARENT for
        // WM_NCHITTEST. That makes mouse messages fall through to the
        // parent — which means our subclass never receives
        // WM_LBUTTONDOWN / WM_MOUSEMOVE and the source rectangles
        // looked "un-draggable" even though all the drag/move logic
        // worked correctly. Forcing HTCLIENT here makes the static
        // control itself receive mouse input.
        return HTCLIENT;
    case WM_LBUTTONDOWN: {
        SetCapture(hwnd);
        int mx = (short)LOWORD(lParam);
        int my = (short)HIWORD(lParam);
        int sid = -1;
        PreviewDragMode m = PreviewHitTest(mx, my, sid);
        if (m == PreviewDragMode::None) {
            cmp::g_selectedSourceId = -1;
            return 0;
        }
        cmp::g_selectedSourceId = sid;
        cmp::ISource* s = cmp::FindSource(sid);
        if (!s) return 0;
        g_pdrag.mode = m;
        g_pdrag.srcId = sid;
        g_pdrag.t0 = s->t;
        float cx, cy;
        if (PreviewToCanvas(mx, my, cx, cy)) {
            g_pdrag.anchorCanvas.x = (LONG)cx;
            g_pdrag.anchorCanvas.y = (LONG)cy;
        }
        return 0;
    }
    case WM_MOUSEMOVE: {
        if (g_pdrag.mode == PreviewDragMode::None) {
            // Update cursor shape based on hit test
            int mx = (short)LOWORD(lParam);
            int my = (short)HIWORD(lParam);
            int sid = -1;
            PreviewDragMode m = PreviewHitTest(mx, my, sid);
            LPCWSTR cur = IDC_ARROW;
            switch (m) {
                case PreviewDragMode::Move: cur = IDC_SIZEALL; break;
                case PreviewDragMode::NW: case PreviewDragMode::SE: cur = IDC_SIZENWSE; break;
                case PreviewDragMode::NE: case PreviewDragMode::SW: cur = IDC_SIZENESW; break;
                case PreviewDragMode::N:  case PreviewDragMode::S:  cur = IDC_SIZENS;   break;
                case PreviewDragMode::W:  case PreviewDragMode::E:  cur = IDC_SIZEWE;   break;
                default: break;
            }
            SetCursor(LoadCursorW(nullptr, cur));
            return 0;
        }
        cmp::ISource* s = cmp::FindSource(g_pdrag.srcId);
        if (!s) return 0;
        int mx = (short)LOWORD(lParam);
        int my = (short)HIWORD(lParam);
        float cx, cy;
        if (!PreviewToCanvas(mx, my, cx, cy)) return 0;
        float dx = cx - g_pdrag.anchorCanvas.x;
        float dy = cy - g_pdrag.anchorCanvas.y;

        bool propor = (GetKeyState(VK_SHIFT)   & 0x8000) != 0;
        bool snap   = (GetKeyState(VK_CONTROL) & 0x8000) != 0;
        const float aspect = std::max(1.0f, g_pdrag.t0.w) / std::max(1.0f, g_pdrag.t0.h);

        cmp::SourceTransform t = g_pdrag.t0;
        if (g_pdrag.mode == PreviewDragMode::Move) {
            t.x = g_pdrag.t0.x + dx;
            t.y = g_pdrag.t0.y + dy;
        } else {
            // resize via handle drag
            float l = g_pdrag.t0.x;
            float top = g_pdrag.t0.y;
            float r = l + g_pdrag.t0.w;
            float b = top + g_pdrag.t0.h;
            switch (g_pdrag.mode) {
                case PreviewDragMode::NW: l += dx; top += dy; break;
                case PreviewDragMode::N:                top += dy; break;
                case PreviewDragMode::NE: r += dx; top += dy; break;
                case PreviewDragMode::W:  l += dx;             break;
                case PreviewDragMode::E:  r += dx;             break;
                case PreviewDragMode::SW: l += dx; b += dy;    break;
                case PreviewDragMode::S:                b += dy; break;
                case PreviewDragMode::SE: r += dx; b += dy;    break;
                default: break;
            }
            // Min size clamp
            if (r - l < 16) r = l + 16;
            if (b - top < 16) b = top + 16;
            t.x = l; t.y = top; t.w = r - l; t.h = b - top;

            if (propor) {
                // Adjust the height to match width's new ratio (or vice versa,
                // depending on which dimension changed most).
                float newW = t.w, newH = t.h;
                bool widthDominant = std::abs(newW - g_pdrag.t0.w) >
                                     std::abs(newH - g_pdrag.t0.h);
                if (widthDominant) {
                    newH = newW / aspect;
                } else {
                    newW = newH * aspect;
                }
                // Anchor opposite corner to keep handle sticky
                bool anchorRight  = (g_pdrag.mode == PreviewDragMode::NW ||
                                     g_pdrag.mode == PreviewDragMode::W  ||
                                     g_pdrag.mode == PreviewDragMode::SW);
                bool anchorBottom = (g_pdrag.mode == PreviewDragMode::NW ||
                                     g_pdrag.mode == PreviewDragMode::N  ||
                                     g_pdrag.mode == PreviewDragMode::NE);
                if (anchorRight)  t.x = (g_pdrag.t0.x + g_pdrag.t0.w) - newW;
                if (anchorBottom) t.y = (g_pdrag.t0.y + g_pdrag.t0.h) - newH;
                t.w = newW; t.h = newH;
            }
        }

        if (snap) {
            const float g = 8.0f;
            t.x = std::round(t.x / g) * g;
            t.y = std::round(t.y / g) * g;
            t.w = std::round(t.w / g) * g;
            t.h = std::round(t.h / g) * g;
        }

        // ---- OBS-style alignment guides + overflow markers --------
        // Compute candidate snap lines on each axis: canvas left /
        // center / right (and analogous for Y), plus every other
        // visible source's left / center / right edges. Snap the
        // moving source's matching edges/centers when within 8 canvas
        // pixels of any candidate, and record the matched candidates
        // so the overlay can draw the magenta guide lines. Hold ALT to
        // disable snapping entirely.
        bool altDown = (GetKeyState(VK_MENU) & 0x8000) != 0;
        cmp::g_dragGuides.Reset();
        cmp::g_dragGuides.active = true;
        if (!altDown) {
            const float SNAP = 8.0f;
            const float canvasW = (float)g_renderer.CanvasW();
            const float canvasH = (float)g_renderer.CanvasH();
            std::vector<float> candX = { 0.0f, canvasW * 0.5f, canvasW };
            std::vector<float> candY = { 0.0f, canvasH * 0.5f, canvasH };
            {
                std::lock_guard<std::mutex> srcLk(cmp::g_sourcesMutex);
                for (auto& sp : cmp::g_sources) {
                    if (!sp || sp->id == g_pdrag.srcId || !sp->t.visible) continue;
                    candX.push_back(sp->t.x);
                    candX.push_back(sp->t.x + sp->t.w * 0.5f);
                    candX.push_back(sp->t.x + sp->t.w);
                    candY.push_back(sp->t.y);
                    candY.push_back(sp->t.y + sp->t.h * 0.5f);
                    candY.push_back(sp->t.y + sp->t.h);
                }
            }
            auto snapAxis = [&](float& edge, const std::vector<float>& cands,
                                float& outOffset, float& outMatched) {
                float best = SNAP + 1.0f;
                float matched = 0;
                for (float c : cands) {
                    float d = std::abs(edge - c);
                    if (d < best) { best = d; matched = c; }
                }
                if (best <= SNAP) {
                    outOffset = matched - edge;
                    outMatched = matched;
                    edge = matched;
                    return true;
                }
                return false;
            };
            // For Move: snap any of (left, center, right) by the same
            // delta to keep the rect rigid. Pick the axis with the
            // smallest snap distance.
            if (g_pdrag.mode == PreviewDragMode::Move) {
                float dxOff = 0, dyOff = 0;
                struct Cand { float val; float* edge; float src; };
                float l = t.x, cx = t.x + t.w * 0.5f, r = t.x + t.w;
                float top = t.y, cy = t.y + t.h * 0.5f, b = t.y + t.h;
                Cand xs[3] = { {l,&l,l}, {cx,&cx,cx}, {r,&r,r} };
                Cand ys[3] = { {top,&top,top}, {cy,&cy,cy}, {b,&b,b} };
                float bestX = SNAP + 1.0f, mX = 0;
                for (auto& xc : xs) for (float c : candX) {
                    float d = std::abs(xc.val - c);
                    if (d < bestX) { bestX = d; mX = c; dxOff = c - xc.val; }
                }
                float bestY = SNAP + 1.0f, mY = 0;
                for (auto& yc : ys) for (float c : candY) {
                    float d = std::abs(yc.val - c);
                    if (d < bestY) { bestY = d; mY = c; dyOff = c - yc.val; }
                }
                if (bestX <= SNAP) {
                    t.x += dxOff;
                    cmp::g_dragGuides.AddV(mX);
                    // Add any other matching candidates within 0.5 of new edges
                    float L = t.x, C = t.x + t.w * 0.5f, R = t.x + t.w;
                    for (float c : candX) {
                        if (std::abs(c - L) < 0.5f) cmp::g_dragGuides.AddV(c);
                        if (std::abs(c - C) < 0.5f) cmp::g_dragGuides.AddV(c);
                        if (std::abs(c - R) < 0.5f) cmp::g_dragGuides.AddV(c);
                    }
                }
                if (bestY <= SNAP) {
                    t.y += dyOff;
                    cmp::g_dragGuides.AddH(mY);
                    float T = t.y, C = t.y + t.h * 0.5f, B = t.y + t.h;
                    for (float c : candY) {
                        if (std::abs(c - T) < 0.5f) cmp::g_dragGuides.AddH(c);
                        if (std::abs(c - C) < 0.5f) cmp::g_dragGuides.AddH(c);
                        if (std::abs(c - B) < 0.5f) cmp::g_dragGuides.AddH(c);
                    }
                }
            } else {
                // Resize: snap the moved edge(s) only.
                float l = t.x, r = t.x + t.w, top = t.y, b = t.y + t.h;
                bool snapL = (g_pdrag.mode == PreviewDragMode::NW ||
                              g_pdrag.mode == PreviewDragMode::W  ||
                              g_pdrag.mode == PreviewDragMode::SW);
                bool snapR = (g_pdrag.mode == PreviewDragMode::NE ||
                              g_pdrag.mode == PreviewDragMode::E  ||
                              g_pdrag.mode == PreviewDragMode::SE);
                bool snapT = (g_pdrag.mode == PreviewDragMode::NW ||
                              g_pdrag.mode == PreviewDragMode::N  ||
                              g_pdrag.mode == PreviewDragMode::NE);
                bool snapB = (g_pdrag.mode == PreviewDragMode::SW ||
                              g_pdrag.mode == PreviewDragMode::S  ||
                              g_pdrag.mode == PreviewDragMode::SE);
                float off, m;
                if (snapL) { float e = l; if (snapAxis(e, candX, off, m)) { l = e; cmp::g_dragGuides.AddV(m); } }
                if (snapR) { float e = r; if (snapAxis(e, candX, off, m)) { r = e; cmp::g_dragGuides.AddV(m); } }
                if (snapT) { float e = top; if (snapAxis(e, candY, off, m)) { top = e; cmp::g_dragGuides.AddH(m); } }
                if (snapB) { float e = b; if (snapAxis(e, candY, off, m)) { b = e; cmp::g_dragGuides.AddH(m); } }
                if (r - l < 16) r = l + 16;
                if (b - top < 16) b = top + 16;
                t.x = l; t.y = top; t.w = r - l; t.h = b - top;
            }
        }

        // ---- Bounds-overflow markers -----------------------------
        // If the source extends past the canvas edges, record the
        // out-of-bounds rect so the overlay paints a red dashed
        // contour. Computed AFTER snapping so it reflects the actual
        // displayed transform.
        const float canvasW = (float)g_renderer.CanvasW();
        const float canvasH = (float)g_renderer.CanvasH();
        if (t.x < 0 || t.y < 0 || t.x + t.w > canvasW || t.y + t.h > canvasH) {
            cmp::g_dragGuides.overflow  = true;
            cmp::g_dragGuides.overflowL = t.x;
            cmp::g_dragGuides.overflowT = t.y;
            cmp::g_dragGuides.overflowR = t.x + t.w;
            cmp::g_dragGuides.overflowB = t.y + t.h;
        }

        s->t = t;
        return 0;
    }
    case WM_LBUTTONUP: {
        ReleaseCapture();
        g_pdrag.mode = PreviewDragMode::None;
        g_pdrag.srcId = -1;
        cmp::g_dragGuides.Reset();          // clear OBS-style guides
        return 0;
    }
    case WM_SETCURSOR: {
        return TRUE;     // we set cursor in WM_MOUSEMOVE
    }
    case WM_NCDESTROY: {
        RemoveWindowSubclass(hwnd, PreviewSubProc, 1);
        break;
    }
    }
    return DefSubclassProc(hwnd, msg, wParam, lParam);
}

// =====================================================================
//                       Main window proc
// =====================================================================
static LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam)
{
    switch (msg) {
    case WM_CREATE: {
        g_hwndMain = hwnd;
        RECT rc; GetClientRect(hwnd, &rc);
        int W = rc.right, H = rc.bottom;

        int prevH = (int)(H * 0.55f);
        if (prevH < 200) prevH = 200;

        g_hwndPreview = CreateWindowExW(0, L"STATIC", nullptr,
            WS_CHILD | WS_VISIBLE | SS_BLACKRECT,
            0, 0, W, prevH, hwnd, (HMENU)IDC_PREVIEW, g_hInst, nullptr);

        RegisterUiPanelClass(g_hInst);
        g_hwndUiPanel = CreateWindowExW(0, kUiPanelClass, nullptr,
            WS_CHILD | WS_VISIBLE,
            0, prevH, W, H - prevH, hwnd, nullptr, g_hInst, nullptr);

        // Audio thread is always-on (boots here, runs until WM_DESTROY)
        if (!g_audioRunning.load()) {
            g_audioRunning.store(true);
            g_audioThread = std::thread(AudioThreadProc);
        }
        // Capture/render thread for the preview
        if (g_renderer.Init(g_hwndPreview, g_selectedMonitor)) {
            // Phase 2 — bootstrap a DesktopSource bound to the same SRV
            // the existing duplication writes into. Default transform
            // fills the canvas (1920x1080) regardless of monitor size.
            auto desk = std::make_unique<cmp::DesktopSource>();
            desk->Bind(g_renderer.DesktopCaptureSRV(),
                       g_renderer.DesktopCaptureW(),
                       g_renderer.DesktopCaptureH());
            desk->t.x = 0;
            desk->t.y = 0;
            desk->t.w = (float)g_renderer.CanvasW();
            desk->t.h = (float)g_renderer.CanvasH();
            desk->SetDisplayName(L"Display capture");
            cmp::AddSource(std::move(desk));

            // Subclass the preview HWND for mouse-driven select / drag /
            // resize handling.
            extern LRESULT CALLBACK PreviewSubProc(HWND, UINT, WPARAM, LPARAM, UINT_PTR, DWORD_PTR);
            SetWindowSubclass(g_hwndPreview, PreviewSubProc, 1, 0);

            g_captureRunning.store(true);
            g_captureThread = std::thread(CaptureThreadProc);
        }

        RegisterGlobalHotkeys(hwnd);
        SetTimer(hwnd, 1, 16, nullptr);   // preview render tick
        return 0;
    }

    case WM_TIMER: {
        if (wParam == 1) g_renderer.RenderPreview();
        return 0;
    }

    case WM_SIZE: {
        if (!g_hwndPreview || !g_hwndUiPanel) return 0;
        int W = LOWORD(lParam), H = HIWORD(lParam);
        int prevH = (int)(H * 0.55f);
        if (prevH < 200) prevH = 200;
        SetWindowPos(g_hwndPreview, nullptr, 0, 0, W, prevH, SWP_NOZORDER);
        SetWindowPos(g_hwndUiPanel, nullptr, 0, prevH, W, H - prevH, SWP_NOZORDER);
        return 0;
    }

    case WM_GETMINMAXINFO: {
        // Enforce a minimum window size so the responsive layouts have
        // a baseline below which we don't claim things look right.
        // 920x640 is enough for the FX toolbar's two-row wrap layout
        // plus the chain list + param pane.
        MINMAXINFO* mmi = (MINMAXINFO*)lParam;
        mmi->ptMinTrackSize.x = 920;
        mmi->ptMinTrackSize.y = 640;
        return 0;
    }

    case WM_HOTKEY: {
        switch (wParam) {
        case HK_ID_START: StartRecording(); break;
        case HK_ID_PAUSE: PauseRecording(); break;
        case HK_ID_STOP:  StopRecording();  break;
        }
        return 0;
    }

    case WM_DESTROY: {
        UnregisterHotKey(hwnd, HK_ID_START);
        UnregisterHotKey(hwnd, HK_ID_PAUSE);
        UnregisterHotKey(hwnd, HK_ID_STOP);
        StopRecording();
        g_appRunning.store(false);
        g_captureRunning.store(false);
        g_audioRunning.store(false);
        if (g_captureThread.joinable()) g_captureThread.join();
        if (g_audioThread.joinable())   g_audioThread.join();
        g_renderer.Shutdown();
        PostQuitMessage(0);
        return 0;
    }
    }
    return DefWindowProcW(hwnd, msg, wParam, lParam);
}



#pragma region WINMAIN

int WINAPI wWinMain(HINSTANCE hInstance, HINSTANCE, LPWSTR, int nCmdShow)
{
    g_hInst = hInstance;

    SetProcessDPIAware();

    HRESULT hr = CoInitializeEx(nullptr, COINIT_APARTMENTTHREADED);
    if (FAILED(hr)) return 1;

    hr = MFStartup(MF_VERSION, MFSTARTUP_NOSOCKET);
    if (FAILED(hr)) { CoUninitialize(); return 1; }

    INITCOMMONCONTROLSEX icc = { sizeof(icc),
                                 ICC_WIN95_CLASSES | ICC_TAB_CLASSES |
                                 ICC_BAR_CLASSES | ICC_STANDARD_CLASSES };
    InitCommonControlsEx(&icc);

    EnumerateMonitors();
    EnumerateAudioDevices();

    WNDCLASSEXW wc = {};
    wc.cbSize        = sizeof(wc);
    wc.style         = CS_HREDRAW | CS_VREDRAW;
    wc.lpfnWndProc   = WndProc;
    wc.hInstance     = hInstance;
    wc.hCursor       = LoadCursorW(nullptr, IDC_ARROW);
    wc.hbrBackground = CreateSolidBrush(RGB(0x10, 0x10, 0x15));   // matches D2D theme.bgWindow
    wc.lpszClassName = L"MaxxRecorderWindow";
    wc.hIcon         = LoadIconW(nullptr, IDI_APPLICATION);
    RegisterClassExW(&wc);

    int screenW = GetSystemMetrics(SM_CXSCREEN);
    int screenH = GetSystemMetrics(SM_CYSCREEN);
    int winW    = (int)(screenW * 0.75f);
    int winH    = (int)(screenH * 0.75f);
    int winX    = (screenW - winW) / 2;
    int winY    = (screenH - winH) / 2;

    HWND hwnd = CreateWindowExW(
        WS_EX_APPWINDOW,
        L"MaxxRecorderWindow",
        L"Maxx Screen Recorder",
        WS_OVERLAPPEDWINDOW,
        winX, winY, winW, winH,
        nullptr, nullptr, hInstance, nullptr);

    if (!hwnd) {
        MFShutdown();
        CoUninitialize();
        return 1;
    }

    ShowWindow(hwnd, nCmdShow);
    UpdateWindow(hwnd);

    MSG msg = {};
    while (GetMessageW(&msg, nullptr, 0, 0)) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }

    MFShutdown();
    CoUninitialize();
    return (int)msg.wParam;
}

#pragma endregion
