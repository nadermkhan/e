#pragma once
#include <string>
#include <string_view>
#include <vector>
#include <unordered_map>
#include <optional>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <cstdint>
#include <cstddef>
#include <cstring>
#include <stdexcept>
#include <algorithm>
#include <sstream>
#include <iostream>
#include <cctype>

// User initializer code

    // =====================================================================
    // Elegant V1 Grammar -> C++/WinRT AST Builder
    // Injected directly into the EvoParser namespace
    // =====================================================================
    // Helper function to extract array elements safely within Evo's arena
    std::vector<Value> extractElements(ParseContext& ctx, const Value& arr) {
        std::vector<Value> res;
        if (arr.type == ValueType::Array) {
            auto view = ctx.getArrayElements(arr);
            for (const auto& v : view) res.push_back(v);
        }
        return res;
    }


namespace EvoParser {

struct Position {
    size_t offset = 0;
    size_t line = 1;
    size_t column = 1;
};

struct Span {
    Position start;
    Position end;
};

struct ParseError : public std::exception {
    std::string message;
    Position pos;
    std::string expected;
    std::string full_msg; // No longer mutable
    
    void build_message() {
        full_msg = message + " at line " + std::to_string(pos.line) + ", col " + std::to_string(pos.column);
        if (!expected.empty()) full_msg += " (Expected: " + expected + ")";
    }
    
    const char* what() const noexcept override {
        return full_msg.c_str();
    }
};

enum class ValueType { Null, StringView, Array, Int, Float, Bool };

struct Value {
    union {
        struct { const char* ptr; size_t len; } str;
        struct { size_t arena_start; size_t length; } arr;
        int64_t i;
        double f;
        bool b;
    } data;
    uint32_t line = 0;
    uint32_t col = 0;
    uint32_t length = 0;
    ValueType type = ValueType::Null;
    
    Value() : line(0), col(0), length(0), type(ValueType::Null) { data.str = {nullptr, 0}; }
    Value(std::nullptr_t) : Value() {}
    Value(std::string_view s) : Value() { type = ValueType::StringView; data.str = {s.data(), s.length()}; }
    Value(const char* s) : Value() { type = ValueType::StringView; data.str = {s, std::strlen(s)}; }
    Value(const std::string&) = delete; // Prevent dangling pointers
    Value(int64_t v) : Value() { type = ValueType::Int; data.i = v; }
    Value(int v) : Value() { type = ValueType::Int; data.i = v; }
    Value(unsigned int v) : Value() { type = ValueType::Int; data.i = static_cast<int64_t>(v); }
    Value(unsigned long v) : Value() { type = ValueType::Int; data.i = static_cast<int64_t>(v); }
    Value(unsigned long long v) : Value() { type = ValueType::Int; data.i = static_cast<int64_t>(v); }
    Value(double v) : Value() { type = ValueType::Float; data.f = v; }
    Value(bool v) : Value() { type = ValueType::Bool; data.b = v; }
    Value(const Value&) = default;
    Value& operator=(const Value&) = default;
};

// WARNING: Deeply nested left-recursive expressions may temporarily orphan AST nodes in this arena,
// increasing memory consumption during parsing. The arena is only reset upon full parse failure.
class ValueArena {
public:
    std::vector<std::unique_ptr<std::string>> string_pool;
    std::vector<Value> buffer;
    size_t head = 0;
    ValueArena(size_t capacity = 100000) { buffer.resize(capacity); }
    ValueArena(ValueArena&&) noexcept = default;
    ValueArena& operator=(ValueArena&&) noexcept = default;
    ValueArena(const ValueArena&) = delete;
    ValueArena& operator=(const ValueArena&) = delete;
    size_t allocate(const std::vector<Value>& nodes) {
        if (head + nodes.size() > buffer.size()) buffer.resize(std::max(buffer.size() * 2, head + nodes.size()));
        size_t start = head;
        for(const auto& n : nodes) buffer[head++] = n;
        return start;
    }
    void push_back(const Value& val) {
        if (head >= buffer.size()) buffer.resize(buffer.size() == 0 ? 128 : buffer.size() * 2);
        buffer[head++] = val;
    }
    size_t save() const { return head; }
    void restore(size_t saved_head) { head = saved_head; }
    const Value* get_array(size_t start) const { return buffer.data() + start; }
    std::string_view allocateString(std::string s) {
        string_pool.push_back(std::make_unique<std::string>(std::move(s)));
        return *string_pool.back();
    }
};

inline Value makeString(std::string_view s) { return Value(s); }
inline Value makeDynamicString(ValueArena& arena, std::string s) {
    return Value(arena.allocateString(std::move(s)));
}
inline Value makeInt(int64_t v) { return Value(v); }
inline Value makeFloat(double v) { return Value(v); }
inline Value makeBool(bool v) { return Value(v); }
inline Value makeNull() { return Value(nullptr); }

inline std::string_view toString(const Value& v) { return std::string_view(v.data.str.ptr, v.data.str.len); }
inline int64_t toInt(const Value& v) { return v.data.i; }
inline double toFloat(const Value& v) { return v.data.f; }
inline bool toBool(const Value& v) { return v.data.b; }
inline bool isNull(const Value& v) { return v.type == ValueType::Null; }

struct ArrayView {
    const ValueArena* arena;
    size_t start;
    size_t size;
    
    struct Iterator {
        const ValueArena* arena;
        size_t idx;
        bool operator!=(const Iterator& o) const { return idx != o.idx; }
        Iterator& operator++() { idx++; return *this; }
        const Value& operator*() const { return arena->buffer[idx]; }
    };
    
    Iterator begin() const { return {arena, start}; }
    Iterator end() const { return {arena, start + size}; }
    const Value& operator[](size_t i) const { return arena->buffer[start + i]; }
};

struct ParseContext {
    Value root;
    ValueArena arena;
    
    ParseContext() = default;
    ParseContext(Value r, ValueArena&& a) : root(r), arena(std::move(a)) {}
    
    ArrayView getArrayElements(const Value& v) const {
        if (v.type != ValueType::Array) return {nullptr, 0, 0};
        return {&arena, v.data.arr.arena_start, v.data.arr.length};
    }
};

class Parser {
public:
    struct Result {
        bool success = false;
        Value value;
        size_t end_cursor = 0;
        uint32_t end_line = 1;
        uint32_t end_col = 1;
    };
    
    ParseContext parse(std::string_view input) {
        input_ = input;
        cursor_ = 0;
        line_ = 1;
        col_ = 1;
        current_depth_ = 0; // ADD THIS: Reset depth guard on recycle
        if (memo_cache_.empty()) memo_cache_.resize(MEMO_SIZE);
        parse_generation_++;
        if (parse_generation_ == 0) {
            std::fill(memo_cache_.begin(), memo_cache_.end(), MemoEntry{});
            parse_generation_ = 1;
        }
        arena_ = ValueArena(100000);
        max_fail_pos_ = 0;
        max_fail_line_ = 1;
        max_fail_col_ = 1;
        expected_.clear();
        auto r = parse_Program();
        if (r.success) {
            if (cursor_ == input_.size()) return ParseContext(r.value, std::move(arena_));
            else fail("End of File (trailing characters found)");
        }
        ParseError err;
        err.message = "Syntax error";
        err.pos = {max_fail_pos_, max_fail_line_, max_fail_col_};
        if (!expected_.empty()) {
            for (size_t i = 0; i < expected_.size(); i++) {
                if (i > 0) err.expected += ", ";
                err.expected += std::string(expected_[i]);
            }
        }
        err.build_message();
        throw err;
    }
    
    bool try_parse(std::string_view input, ParseContext& out, ParseError& err) {
        try { out = parse(input); return true; }
        catch (const ParseError& e) { err = e; return false; }
        catch (...) { return false; }
    }
    
    bool try_parse(std::string_view input, ParseContext& out) {
        ParseError ignored;
        return try_parse(input, out, ignored);
    }
    
    // Prevent dangling pointers from temporary strings in the zero-copy architecture
    ParseContext parse(std::string&&) = delete;
    bool try_parse(std::string&&, ParseContext&, ParseError&) = delete;
    bool try_parse(std::string&&, ParseContext&) = delete;
    
    size_t max_fail_pos() const { return max_fail_pos_; }
    size_t max_fail_line() const { return max_fail_line_; }
    size_t max_fail_col() const { return max_fail_col_; }
    Value createArray(const std::vector<Value>& elements) {
        Value val;
        val.type = ValueType::Array;
        val.data.arr.arena_start = arena_.allocate(elements);
        val.data.arr.length = static_cast<uint32_t>(elements.size());
        return val;
    }
    
    ArrayView getArrayElements(const Value& v) const {
        if (v.type != ValueType::Array) return {nullptr, 0, 0};
        return {&arena_, v.data.arr.arena_start, v.data.arr.length};
    }
    

private:
    std::string_view input_;
    size_t cursor_ = 0;
    size_t line_ = 1;
    size_t col_ = 1;
    size_t max_fail_pos_ = 0;
    size_t max_fail_line_ = 1;
    size_t max_fail_col_ = 1;
    std::vector<std::string_view> expected_;
    
    static constexpr size_t MEMO_SIZE = 1024 * 1024;
    static constexpr size_t MEMO_MASK = MEMO_SIZE - 1;
    struct MemoEntry {
        uint64_t key = 0;
        size_t generation = 0;
        bool active = false; // O(1) Cycle Detection Tracker
        Result result;
    };
    std::vector<MemoEntry> memo_cache_;
    ValueArena arena_;
    size_t parse_generation_ = 0;
    size_t current_depth_ = 0;
    static constexpr size_t MAX_DEPTH = 2000;
    
    bool at_end() const { return cursor_ >= input_.size(); }
    char peek() const { return at_end() ? '\0' : input_[cursor_]; }
    
    char advance_char() {
        char c = input_[cursor_++];
        if (c == '\n') { line_++; col_ = 1; }
        else if ((static_cast<unsigned char>(c) & 0xC0) != 0x80) { col_++; } // UTF-8 safe column tracking
        return c;
    }
    
    void save(size_t& c, size_t& l, size_t& co, size_t& ar) const { c = cursor_; l = line_; co = col_; ar = arena_.save(); }
    void restore(size_t c, size_t l, size_t co, size_t ar) { cursor_ = c; line_ = l; col_ = co; (void)ar; /* Arena is monotonic to preserve memoized ASTs */ }
    
    void fail(std::string_view exp) {
        if (cursor_ > max_fail_pos_) {
            max_fail_pos_ = cursor_;
            max_fail_line_ = line_;
            max_fail_col_ = col_;
            expected_.clear();
            expected_.push_back(exp);
        } else if (cursor_ == max_fail_pos_) {
            if (std::find(expected_.begin(), expected_.end(), exp) == expected_.end()) {
                expected_.push_back(exp);
            }
        }
    }
    
    std::string_view text_at(size_t start, size_t end) const {
        return input_.substr(start, end - start);
    }
    
    Result parse_Program() {
        uint64_t memo_key = (static_cast<uint64_t>(0ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 0ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v0_ok = true;
            Value v0_val = makeNull();
            {
                size_t rep_start = arena_.head;
                size_t rep_count = 0;
                for (;;) {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    auto v1_r = parse_Declaration();
                    bool v1_ok = v1_r.success;
                    Value v1_val = v1_r.value;
                    if (!v1_ok) { restore(rc, rl, rco, rar); break; }
                    if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                    arena_.push_back(v1_val);
                    rep_count++;
                }
                v0_val.type = ValueType::Array;
                v0_val.data.arr.arena_start = rep_start;
                v0_val.data.arr.length = static_cast<uint32_t>(rep_count);
            }
            if (v0_ok) return {true, v0_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Program");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_Declaration() {
        uint64_t memo_key = (static_cast<uint64_t>(1ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 1ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v2_ok = false;
            Value v2_val = makeNull();
            {
                size_t cc = 0, cl = 0, cco = 0, car = 0;
                save(cc, cl, cco, car);
                if (!v2_ok) {
                    {
                        auto v3_r = parse_ImportDecl();
                        bool v3_ok = v3_r.success;
                        Value v3_val = v3_r.value;
                        if (v3_ok) { v2_ok = true; v2_val = v3_val; }
                    }
                }
                if (!v2_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v4_r = parse_ClassDecl();
                        bool v4_ok = v4_r.success;
                        Value v4_val = v4_r.value;
                        if (v4_ok) { v2_ok = true; v2_val = v4_val; }
                    }
                }
                if (!v2_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v5_r = parse_StructDecl();
                        bool v5_ok = v5_r.success;
                        Value v5_val = v5_r.value;
                        if (v5_ok) { v2_ok = true; v2_val = v5_val; }
                    }
                }
                if (!v2_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v6_r = parse_FuncDecl();
                        bool v6_ok = v6_r.success;
                        Value v6_val = v6_r.value;
                        if (v6_ok) { v2_ok = true; v2_val = v6_val; }
                    }
                }
                if (!v2_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v7_r = parse_PropertyDecl();
                        bool v7_ok = v7_r.success;
                        Value v7_val = v7_r.value;
                        if (v7_ok) { v2_ok = true; v2_val = v7_val; }
                    }
                }
            }
            if (v2_ok) return {true, v2_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Declaration");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_ImportDecl() {
        uint64_t memo_key = (static_cast<uint64_t>(2ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 2ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v8_start = cursor_;
            size_t v8_startLine = line_;
            size_t v8_startCol = col_;
            bool v9_ok = true;
            Value v9_val = makeNull();
            size_t v9_ss = 0, v9_sls = 0, v9_scs = 0, v9_sars = 0;
            save(v9_ss, v9_sls, v9_scs, v9_sars);
            Value v9_elems[2];
            Value lbl_d = makeNull();
            if (v9_ok) {
                bool v10_ok = false;
                Value v10_val = makeNull();
                {
                    bool match = cursor_ + 6 <= input_.size();
                    if (match) {
                        for (size_t i = 0; i < 6; i++) {
                            if (std::tolower(static_cast<unsigned char>(input_[cursor_ + i])) != std::tolower(static_cast<unsigned char>("import"[i]))) { match = false; break; }
                        }
                    }
                    if (match) {
                        size_t s = cursor_; (void)s;
                        for (size_t i = 0; i < 6; i++) advance_char();
                        v10_ok = true;
                        v10_val = makeString(text_at(s, cursor_));
                    } else {
                        fail("\"import\"");
                    }
                }
                if (!v10_ok) { v9_ok = false; restore(v9_ss, v9_sls, v9_scs, v9_sars); }
                else { v9_elems[0] = v10_val; }
            }
            if (v9_ok) {
                auto v11_r = parse_Identifier();
                bool v11_ok = v11_r.success;
                Value v11_val = v11_r.value;
                if (!v11_ok) { v9_ok = false; restore(v9_ss, v9_sls, v9_scs, v9_sars); }
                else { v9_elems[1] = v11_val; }
                if (v9_ok) lbl_d = v9_elems[1];
            }
            if (v9_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v9_elems[0]);
                arena_.push_back(v9_elems[1]);
                v9_val.type = ValueType::Array;
                v9_val.data.arr.arena_start = seq_start;
                v9_val.data.arr.length = static_cast<uint32_t>(2);
            }
            (void)lbl_d;
            bool v8_ok = v9_ok;
            (void)v9_val;
            Value v8_val = makeNull();
            if (v8_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v8_start, cursor_);
                };
                (void)_text;
                auto& d = lbl_d;
                (void)d;
                v8_val = [&]() -> Value {
                    return createArray({ makeString("Import"), id });
                }();
                if (v8_val.line == 0) {
                    v8_val.line = static_cast<uint32_t>(v8_startLine);
                    v8_val.col = static_cast<uint32_t>(v8_startCol);
                    v8_val.length = static_cast<uint32_t>(cursor_ - v8_start);
                }
            }
            if (v8_ok) return {true, v8_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Import");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_ClassDecl() {
        uint64_t memo_key = (static_cast<uint64_t>(3ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 3ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v12_start = cursor_;
            size_t v12_startLine = line_;
            size_t v12_startCol = col_;
            bool v13_ok = true;
            Value v13_val = makeNull();
            size_t v13_ss = 0, v13_sls = 0, v13_scs = 0, v13_sars = 0;
            save(v13_ss, v13_sls, v13_scs, v13_sars);
            Value v13_elems[7];
            Value lbl_name = makeNull();
            Value lbl_superclass = makeNull();
            Value lbl_members = makeNull();
            if (v13_ok) {
                bool v14_ok = true;
                Value v14_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    bool v15_ok = false;
                    Value v15_val = makeNull();
                    if (cursor_ + 6 <= input_.size() && input_.substr(cursor_, 6) == std::string_view("public", 6)) {
                        size_t s = cursor_; (void)s;
                        for (size_t i = 0; i < 6; i++) advance_char();
                        v15_ok = true;
                        v15_val = makeString("public");
                    } else {
                        fail("\"public\"");
                    }
                    if (v15_ok) { v14_val = v15_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v14_ok) { v13_ok = false; restore(v13_ss, v13_sls, v13_scs, v13_sars); }
                else { v13_elems[0] = v14_val; }
            }
            if (v13_ok) {
                bool v16_ok = false;
                Value v16_val = makeNull();
                if (cursor_ + 5 <= input_.size() && input_.substr(cursor_, 5) == std::string_view("class", 5)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 5; i++) advance_char();
                    v16_ok = true;
                    v16_val = makeString("class");
                } else {
                    fail("\"class\"");
                }
                if (!v16_ok) { v13_ok = false; restore(v13_ss, v13_sls, v13_scs, v13_sars); }
                else { v13_elems[1] = v16_val; }
            }
            if (v13_ok) {
                auto v17_r = parse_Identifier();
                bool v17_ok = v17_r.success;
                Value v17_val = v17_r.value;
                if (!v17_ok) { v13_ok = false; restore(v13_ss, v13_sls, v13_scs, v13_sars); }
                else { v13_elems[2] = v17_val; }
                if (v13_ok) lbl_name = v13_elems[2];
            }
            if (v13_ok) {
                bool v18_ok = true;
                Value v18_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    auto v19_r = parse_InheritanceClause();
                    bool v19_ok = v19_r.success;
                    Value v19_val = v19_r.value;
                    if (v19_ok) { v18_val = v19_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v18_ok) { v13_ok = false; restore(v13_ss, v13_sls, v13_scs, v13_sars); }
                else { v13_elems[3] = v18_val; }
                if (v13_ok) lbl_superclass = v13_elems[3];
            }
            if (v13_ok) {
                bool v20_ok = false;
                Value v20_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("{", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v20_ok = true;
                    v20_val = makeString("{");
                } else {
                    fail("\"{\"");
                }
                if (!v20_ok) { v13_ok = false; restore(v13_ss, v13_sls, v13_scs, v13_sars); }
                else { v13_elems[4] = v20_val; }
            }
            if (v13_ok) {
                bool v21_ok = true;
                Value v21_val = makeNull();
                {
                    size_t rep_start = arena_.head;
                    size_t rep_count = 0;
                    for (;;) {
                        size_t rc = 0, rl = 0, rco = 0, rar = 0;
                        save(rc, rl, rco, rar);
                        auto v22_r = parse_ClassMember();
                        bool v22_ok = v22_r.success;
                        Value v22_val = v22_r.value;
                        if (!v22_ok) { restore(rc, rl, rco, rar); break; }
                        if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                        arena_.push_back(v22_val);
                        rep_count++;
                    }
                    v21_val.type = ValueType::Array;
                    v21_val.data.arr.arena_start = rep_start;
                    v21_val.data.arr.length = static_cast<uint32_t>(rep_count);
                }
                if (!v21_ok) { v13_ok = false; restore(v13_ss, v13_sls, v13_scs, v13_sars); }
                else { v13_elems[5] = v21_val; }
                if (v13_ok) lbl_members = v13_elems[5];
            }
            if (v13_ok) {
                bool v23_ok = false;
                Value v23_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("}", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v23_ok = true;
                    v23_val = makeString("}");
                } else {
                    fail("\"}\"");
                }
                if (!v23_ok) { v13_ok = false; restore(v13_ss, v13_sls, v13_scs, v13_sars); }
                else { v13_elems[6] = v23_val; }
            }
            if (v13_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v13_elems[0]);
                arena_.push_back(v13_elems[1]);
                arena_.push_back(v13_elems[2]);
                arena_.push_back(v13_elems[3]);
                arena_.push_back(v13_elems[4]);
                arena_.push_back(v13_elems[5]);
                arena_.push_back(v13_elems[6]);
                v13_val.type = ValueType::Array;
                v13_val.data.arr.arena_start = seq_start;
                v13_val.data.arr.length = static_cast<uint32_t>(7);
            }
            (void)lbl_name;
            (void)lbl_superclass;
            (void)lbl_members;
            bool v12_ok = v13_ok;
            (void)v13_val;
            Value v12_val = makeNull();
            if (v12_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v12_start, cursor_);
                };
                (void)_text;
                auto& name = lbl_name;
                (void)name;
                auto& superclass = lbl_superclass;
                (void)superclass;
                auto& members = lbl_members;
                (void)members;
                v12_val = [&]() -> Value {
                    return createArray({ 
        makeString("Class"), 
        name, 
        superclass.value_or(makeNull()), 
        members 
    });
                }();
                if (v12_val.line == 0) {
                    v12_val.line = static_cast<uint32_t>(v12_startLine);
                    v12_val.col = static_cast<uint32_t>(v12_startCol);
                    v12_val.length = static_cast<uint32_t>(cursor_ - v12_start);
                }
            }
            if (v12_ok) return {true, v12_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Class Declaration");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_StructDecl() {
        uint64_t memo_key = (static_cast<uint64_t>(4ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 4ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v24_start = cursor_;
            size_t v24_startLine = line_;
            size_t v24_startCol = col_;
            bool v25_ok = true;
            Value v25_val = makeNull();
            size_t v25_ss = 0, v25_sls = 0, v25_scs = 0, v25_sars = 0;
            save(v25_ss, v25_sls, v25_scs, v25_sars);
            Value v25_elems[7];
            Value lbl_name = makeNull();
            Value lbl_superclass = makeNull();
            Value lbl_members = makeNull();
            if (v25_ok) {
                bool v26_ok = true;
                Value v26_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    bool v27_ok = false;
                    Value v27_val = makeNull();
                    if (cursor_ + 6 <= input_.size() && input_.substr(cursor_, 6) == std::string_view("public", 6)) {
                        size_t s = cursor_; (void)s;
                        for (size_t i = 0; i < 6; i++) advance_char();
                        v27_ok = true;
                        v27_val = makeString("public");
                    } else {
                        fail("\"public\"");
                    }
                    if (v27_ok) { v26_val = v27_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v26_ok) { v25_ok = false; restore(v25_ss, v25_sls, v25_scs, v25_sars); }
                else { v25_elems[0] = v26_val; }
            }
            if (v25_ok) {
                bool v28_ok = false;
                Value v28_val = makeNull();
                if (cursor_ + 6 <= input_.size() && input_.substr(cursor_, 6) == std::string_view("struct", 6)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 6; i++) advance_char();
                    v28_ok = true;
                    v28_val = makeString("struct");
                } else {
                    fail("\"struct\"");
                }
                if (!v28_ok) { v25_ok = false; restore(v25_ss, v25_sls, v25_scs, v25_sars); }
                else { v25_elems[1] = v28_val; }
            }
            if (v25_ok) {
                auto v29_r = parse_Identifier();
                bool v29_ok = v29_r.success;
                Value v29_val = v29_r.value;
                if (!v29_ok) { v25_ok = false; restore(v25_ss, v25_sls, v25_scs, v25_sars); }
                else { v25_elems[2] = v29_val; }
                if (v25_ok) lbl_name = v25_elems[2];
            }
            if (v25_ok) {
                bool v30_ok = true;
                Value v30_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    auto v31_r = parse_InheritanceClause();
                    bool v31_ok = v31_r.success;
                    Value v31_val = v31_r.value;
                    if (v31_ok) { v30_val = v31_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v30_ok) { v25_ok = false; restore(v25_ss, v25_sls, v25_scs, v25_sars); }
                else { v25_elems[3] = v30_val; }
                if (v25_ok) lbl_superclass = v25_elems[3];
            }
            if (v25_ok) {
                bool v32_ok = false;
                Value v32_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("{", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v32_ok = true;
                    v32_val = makeString("{");
                } else {
                    fail("\"{\"");
                }
                if (!v32_ok) { v25_ok = false; restore(v25_ss, v25_sls, v25_scs, v25_sars); }
                else { v25_elems[4] = v32_val; }
            }
            if (v25_ok) {
                bool v33_ok = true;
                Value v33_val = makeNull();
                {
                    size_t rep_start = arena_.head;
                    size_t rep_count = 0;
                    for (;;) {
                        size_t rc = 0, rl = 0, rco = 0, rar = 0;
                        save(rc, rl, rco, rar);
                        auto v34_r = parse_ClassMember();
                        bool v34_ok = v34_r.success;
                        Value v34_val = v34_r.value;
                        if (!v34_ok) { restore(rc, rl, rco, rar); break; }
                        if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                        arena_.push_back(v34_val);
                        rep_count++;
                    }
                    v33_val.type = ValueType::Array;
                    v33_val.data.arr.arena_start = rep_start;
                    v33_val.data.arr.length = static_cast<uint32_t>(rep_count);
                }
                if (!v33_ok) { v25_ok = false; restore(v25_ss, v25_sls, v25_scs, v25_sars); }
                else { v25_elems[5] = v33_val; }
                if (v25_ok) lbl_members = v25_elems[5];
            }
            if (v25_ok) {
                bool v35_ok = false;
                Value v35_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("}", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v35_ok = true;
                    v35_val = makeString("}");
                } else {
                    fail("\"}\"");
                }
                if (!v35_ok) { v25_ok = false; restore(v25_ss, v25_sls, v25_scs, v25_sars); }
                else { v25_elems[6] = v35_val; }
            }
            if (v25_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v25_elems[0]);
                arena_.push_back(v25_elems[1]);
                arena_.push_back(v25_elems[2]);
                arena_.push_back(v25_elems[3]);
                arena_.push_back(v25_elems[4]);
                arena_.push_back(v25_elems[5]);
                arena_.push_back(v25_elems[6]);
                v25_val.type = ValueType::Array;
                v25_val.data.arr.arena_start = seq_start;
                v25_val.data.arr.length = static_cast<uint32_t>(7);
            }
            (void)lbl_name;
            (void)lbl_superclass;
            (void)lbl_members;
            bool v24_ok = v25_ok;
            (void)v25_val;
            Value v24_val = makeNull();
            if (v24_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v24_start, cursor_);
                };
                (void)_text;
                auto& name = lbl_name;
                (void)name;
                auto& superclass = lbl_superclass;
                (void)superclass;
                auto& members = lbl_members;
                (void)members;
                v24_val = [&]() -> Value {
                    return createArray({ makeString("Struct"), name, superclass.value_or(makeNull()), members });
                }();
                if (v24_val.line == 0) {
                    v24_val.line = static_cast<uint32_t>(v24_startLine);
                    v24_val.col = static_cast<uint32_t>(v24_startCol);
                    v24_val.length = static_cast<uint32_t>(cursor_ - v24_start);
                }
            }
            if (v24_ok) return {true, v24_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Struct Declaration");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_InheritanceClause() {
        uint64_t memo_key = (static_cast<uint64_t>(5ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 5ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v36_ok = true;
            Value v36_val = makeNull();
            size_t v36_ss = 0, v36_sls = 0, v36_scs = 0, v36_sars = 0;
            save(v36_ss, v36_sls, v36_scs, v36_sars);
            Value v36_elems[3];
            if (v36_ok) {
                bool v37_ok = false;
                Value v37_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(":", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v37_ok = true;
                    v37_val = makeString(":");
                } else {
                    fail("\":\"");
                }
                if (!v37_ok) { v36_ok = false; restore(v36_ss, v36_sls, v36_scs, v36_sars); }
                else { v36_elems[0] = v37_val; }
            }
            if (v36_ok) {
                auto v38_r = parse_Identifier();
                bool v38_ok = v38_r.success;
                Value v38_val = v38_r.value;
                if (!v38_ok) { v36_ok = false; restore(v36_ss, v36_sls, v36_scs, v36_sars); }
                else { v36_elems[1] = v38_val; }
            }
            if (v36_ok) {
                bool v39_ok = true;
                Value v39_val = makeNull();
                {
                    size_t rep_start = arena_.head;
                    size_t rep_count = 0;
                    for (;;) {
                        size_t rc = 0, rl = 0, rco = 0, rar = 0;
                        save(rc, rl, rco, rar);
                        bool v40_ok = true;
                        Value v40_val = makeNull();
                        size_t v40_ss = 0, v40_sls = 0, v40_scs = 0, v40_sars = 0;
                        save(v40_ss, v40_sls, v40_scs, v40_sars);
                        Value v40_elems[2];
                        if (v40_ok) {
                            bool v41_ok = false;
                            Value v41_val = makeNull();
                            if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(",", 1)) {
                                size_t s = cursor_; (void)s;
                                for (size_t i = 0; i < 1; i++) advance_char();
                                v41_ok = true;
                                v41_val = makeString(",");
                            } else {
                                fail("\",\"");
                            }
                            if (!v41_ok) { v40_ok = false; restore(v40_ss, v40_sls, v40_scs, v40_sars); }
                            else { v40_elems[0] = v41_val; }
                        }
                        if (v40_ok) {
                            auto v42_r = parse_Identifier();
                            bool v42_ok = v42_r.success;
                            Value v42_val = v42_r.value;
                            if (!v42_ok) { v40_ok = false; restore(v40_ss, v40_sls, v40_scs, v40_sars); }
                            else { v40_elems[1] = v42_val; }
                        }
                        if (v40_ok) {
                            size_t seq_start = arena_.head;
                            arena_.push_back(v40_elems[0]);
                            arena_.push_back(v40_elems[1]);
                            v40_val.type = ValueType::Array;
                            v40_val.data.arr.arena_start = seq_start;
                            v40_val.data.arr.length = static_cast<uint32_t>(2);
                        }
                        if (!v40_ok) { restore(rc, rl, rco, rar); break; }
                        if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                        arena_.push_back(v40_val);
                        rep_count++;
                    }
                    v39_val.type = ValueType::Array;
                    v39_val.data.arr.arena_start = rep_start;
                    v39_val.data.arr.length = static_cast<uint32_t>(rep_count);
                }
                if (!v39_ok) { v36_ok = false; restore(v36_ss, v36_sls, v36_scs, v36_sars); }
                else { v36_elems[2] = v39_val; }
            }
            if (v36_ok) {
                v36_val = v36_elems[1];
            }
            if (v36_ok) return {true, v36_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Inheritance");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_ClassMember() {
        uint64_t memo_key = (static_cast<uint64_t>(6ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 6ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v43_ok = false;
            Value v43_val = makeNull();
            {
                size_t cc = 0, cl = 0, cco = 0, car = 0;
                save(cc, cl, cco, car);
                if (!v43_ok) {
                    {
                        auto v44_r = parse_PropertyDecl();
                        bool v44_ok = v44_r.success;
                        Value v44_val = v44_r.value;
                        if (v44_ok) { v43_ok = true; v43_val = v44_val; }
                    }
                }
                if (!v43_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v45_r = parse_FuncDecl();
                        bool v45_ok = v45_r.success;
                        Value v45_val = v45_r.value;
                        if (v45_ok) { v43_ok = true; v43_val = v45_val; }
                    }
                }
                if (!v43_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v46_r = parse_ViewBodyDecl();
                        bool v46_ok = v46_r.success;
                        Value v46_val = v46_r.value;
                        if (v46_ok) { v43_ok = true; v43_val = v46_val; }
                    }
                }
            }
            if (v43_ok) return {true, v43_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Member");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_PropertyDecl() {
        uint64_t memo_key = (static_cast<uint64_t>(7ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 7ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v47_start = cursor_;
            size_t v47_startLine = line_;
            size_t v47_startCol = col_;
            bool v48_ok = true;
            Value v48_val = makeNull();
            size_t v48_ss = 0, v48_sls = 0, v48_scs = 0, v48_sars = 0;
            save(v48_ss, v48_sls, v48_scs, v48_sars);
            Value v48_elems[5];
            Value lbl_mutability = makeNull();
            Value lbl_name = makeNull();
            Value lbl_type = makeNull();
            Value lbl_annotation = makeNull();
            if (v48_ok) {
                bool v49_ok = false;
                Value v49_val = makeNull();
                {
                    size_t cc = 0, cl = 0, cco = 0, car = 0;
                    save(cc, cl, cco, car);
                    if (!v49_ok) {
                        {
                            bool v50_ok = false;
                            Value v50_val = makeNull();
                            if (cursor_ + 3 <= input_.size() && input_.substr(cursor_, 3) == std::string_view("var", 3)) {
                                size_t s = cursor_; (void)s;
                                for (size_t i = 0; i < 3; i++) advance_char();
                                v50_ok = true;
                                v50_val = makeString("var");
                            } else {
                                fail("\"var\"");
                            }
                            if (v50_ok) { v49_ok = true; v49_val = v50_val; }
                        }
                    }
                    if (!v49_ok) {
                        restore(cc, cl, cco, car);
                        {
                            bool v51_ok = false;
                            Value v51_val = makeNull();
                            if (cursor_ + 3 <= input_.size() && input_.substr(cursor_, 3) == std::string_view("let", 3)) {
                                size_t s = cursor_; (void)s;
                                for (size_t i = 0; i < 3; i++) advance_char();
                                v51_ok = true;
                                v51_val = makeString("let");
                            } else {
                                fail("\"let\"");
                            }
                            if (v51_ok) { v49_ok = true; v49_val = v51_val; }
                        }
                    }
                }
                if (!v49_ok) { v48_ok = false; restore(v48_ss, v48_sls, v48_scs, v48_sars); }
                else { v48_elems[0] = v49_val; }
                if (v48_ok) lbl_mutability = v48_elems[0];
            }
            if (v48_ok) {
                auto v52_r = parse_Identifier();
                bool v52_ok = v52_r.success;
                Value v52_val = v52_r.value;
                if (!v52_ok) { v48_ok = false; restore(v48_ss, v48_sls, v48_scs, v48_sars); }
                else { v48_elems[1] = v52_val; }
                if (v48_ok) lbl_name = v48_elems[1];
            }
            if (v48_ok) {
                bool v53_ok = false;
                Value v53_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(":", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v53_ok = true;
                    v53_val = makeString(":");
                } else {
                    fail("\":\"");
                }
                if (!v53_ok) { v48_ok = false; restore(v48_ss, v48_sls, v48_scs, v48_sars); }
                else { v48_elems[2] = v53_val; }
            }
            if (v48_ok) {
                auto v54_r = parse_Type();
                bool v54_ok = v54_r.success;
                Value v54_val = v54_r.value;
                if (!v54_ok) { v48_ok = false; restore(v48_ss, v48_sls, v48_scs, v48_sars); }
                else { v48_elems[3] = v54_val; }
                if (v48_ok) lbl_type = v48_elems[3];
            }
            if (v48_ok) {
                bool v55_ok = true;
                Value v55_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    auto v56_r = parse_DefaultValue();
                    bool v56_ok = v56_r.success;
                    Value v56_val = v56_r.value;
                    if (v56_ok) { v55_val = v56_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v55_ok) { v48_ok = false; restore(v48_ss, v48_sls, v48_scs, v48_sars); }
                else { v48_elems[4] = v55_val; }
                if (v48_ok) lbl_annotation = v48_elems[4];
            }
            if (v48_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v48_elems[0]);
                arena_.push_back(v48_elems[1]);
                arena_.push_back(v48_elems[2]);
                arena_.push_back(v48_elems[3]);
                arena_.push_back(v48_elems[4]);
                v48_val.type = ValueType::Array;
                v48_val.data.arr.arena_start = seq_start;
                v48_val.data.arr.length = static_cast<uint32_t>(5);
            }
            (void)lbl_mutability;
            (void)lbl_name;
            (void)lbl_type;
            (void)lbl_annotation;
            bool v47_ok = v48_ok;
            (void)v48_val;
            Value v47_val = makeNull();
            if (v47_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v47_start, cursor_);
                };
                (void)_text;
                auto& mutability = lbl_mutability;
                (void)mutability;
                auto& name = lbl_name;
                (void)name;
                auto& type = lbl_type;
                (void)type;
                auto& annotation = lbl_annotation;
                (void)annotation;
                v47_val = [&]() -> Value {
                    return createArray({ makeString("Property"), mutability, name, type, annotation.value_or(makeNull()) });
                }();
                if (v47_val.line == 0) {
                    v47_val.line = static_cast<uint32_t>(v47_startLine);
                    v47_val.col = static_cast<uint32_t>(v47_startCol);
                    v47_val.length = static_cast<uint32_t>(cursor_ - v47_start);
                }
            }
            if (v47_ok) return {true, v47_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Property");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_DefaultValue() {
        uint64_t memo_key = (static_cast<uint64_t>(8ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 8ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v57_ok = true;
            Value v57_val = makeNull();
            size_t v57_ss = 0, v57_sls = 0, v57_scs = 0, v57_sars = 0;
            save(v57_ss, v57_sls, v57_scs, v57_sars);
            Value v57_elems[2];
            if (v57_ok) {
                bool v58_ok = false;
                Value v58_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("=", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v58_ok = true;
                    v58_val = makeString("=");
                } else {
                    fail("\"=\"");
                }
                if (!v58_ok) { v57_ok = false; restore(v57_ss, v57_sls, v57_scs, v57_sars); }
                else { v57_elems[0] = v58_val; }
            }
            if (v57_ok) {
                auto v59_r = parse_Expression();
                bool v59_ok = v59_r.success;
                Value v59_val = v59_r.value;
                if (!v59_ok) { v57_ok = false; restore(v57_ss, v57_sls, v57_scs, v57_sars); }
                else { v57_elems[1] = v59_val; }
            }
            if (v57_ok) {
                v57_val = v57_elems[1];
            }
            if (v57_ok) return {true, v57_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Default Value");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_ViewBodyDecl() {
        uint64_t memo_key = (static_cast<uint64_t>(9ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 9ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v60_start = cursor_;
            size_t v60_startLine = line_;
            size_t v60_startCol = col_;
            bool v61_ok = true;
            Value v61_val = makeNull();
            size_t v61_ss = 0, v61_sls = 0, v61_scs = 0, v61_sars = 0;
            save(v61_ss, v61_sls, v61_scs, v61_sars);
            Value v61_elems[8];
            Value lbl_views = makeNull();
            if (v61_ok) {
                bool v62_ok = false;
                Value v62_val = makeNull();
                if (cursor_ + 3 <= input_.size() && input_.substr(cursor_, 3) == std::string_view("var", 3)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 3; i++) advance_char();
                    v62_ok = true;
                    v62_val = makeString("var");
                } else {
                    fail("\"var\"");
                }
                if (!v62_ok) { v61_ok = false; restore(v61_ss, v61_sls, v61_scs, v61_sars); }
                else { v61_elems[0] = v62_val; }
            }
            if (v61_ok) {
                bool v63_ok = false;
                Value v63_val = makeNull();
                if (cursor_ + 4 <= input_.size() && input_.substr(cursor_, 4) == std::string_view("body", 4)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 4; i++) advance_char();
                    v63_ok = true;
                    v63_val = makeString("body");
                } else {
                    fail("\"body\"");
                }
                if (!v63_ok) { v61_ok = false; restore(v61_ss, v61_sls, v61_scs, v61_sars); }
                else { v61_elems[1] = v63_val; }
            }
            if (v61_ok) {
                bool v64_ok = false;
                Value v64_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(":", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v64_ok = true;
                    v64_val = makeString(":");
                } else {
                    fail("\":\"");
                }
                if (!v64_ok) { v61_ok = false; restore(v61_ss, v61_sls, v61_scs, v61_sars); }
                else { v61_elems[2] = v64_val; }
            }
            if (v61_ok) {
                bool v65_ok = false;
                Value v65_val = makeNull();
                if (cursor_ + 4 <= input_.size() && input_.substr(cursor_, 4) == std::string_view("some", 4)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 4; i++) advance_char();
                    v65_ok = true;
                    v65_val = makeString("some");
                } else {
                    fail("\"some\"");
                }
                if (!v65_ok) { v61_ok = false; restore(v61_ss, v61_sls, v61_scs, v61_sars); }
                else { v61_elems[3] = v65_val; }
            }
            if (v61_ok) {
                bool v66_ok = false;
                Value v66_val = makeNull();
                if (cursor_ + 4 <= input_.size() && input_.substr(cursor_, 4) == std::string_view("View", 4)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 4; i++) advance_char();
                    v66_ok = true;
                    v66_val = makeString("View");
                } else {
                    fail("\"View\"");
                }
                if (!v66_ok) { v61_ok = false; restore(v61_ss, v61_sls, v61_scs, v61_sars); }
                else { v61_elems[4] = v66_val; }
            }
            if (v61_ok) {
                bool v67_ok = false;
                Value v67_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("{", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v67_ok = true;
                    v67_val = makeString("{");
                } else {
                    fail("\"{\"");
                }
                if (!v67_ok) { v61_ok = false; restore(v61_ss, v61_sls, v61_scs, v61_sars); }
                else { v61_elems[5] = v67_val; }
            }
            if (v61_ok) {
                bool v68_ok = true;
                Value v68_val = makeNull();
                {
                    size_t rep_start = arena_.head;
                    size_t rep_count = 0;
                    for (;;) {
                        size_t rc = 0, rl = 0, rco = 0, rar = 0;
                        save(rc, rl, rco, rar);
                        auto v69_r = parse_Expression();
                        bool v69_ok = v69_r.success;
                        Value v69_val = v69_r.value;
                        if (!v69_ok) { restore(rc, rl, rco, rar); break; }
                        if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                        arena_.push_back(v69_val);
                        rep_count++;
                    }
                    v68_val.type = ValueType::Array;
                    v68_val.data.arr.arena_start = rep_start;
                    v68_val.data.arr.length = static_cast<uint32_t>(rep_count);
                }
                if (!v68_ok) { v61_ok = false; restore(v61_ss, v61_sls, v61_scs, v61_sars); }
                else { v61_elems[6] = v68_val; }
                if (v61_ok) lbl_views = v61_elems[6];
            }
            if (v61_ok) {
                bool v70_ok = false;
                Value v70_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("}", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v70_ok = true;
                    v70_val = makeString("}");
                } else {
                    fail("\"}\"");
                }
                if (!v70_ok) { v61_ok = false; restore(v61_ss, v61_sls, v61_scs, v61_sars); }
                else { v61_elems[7] = v70_val; }
            }
            if (v61_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v61_elems[0]);
                arena_.push_back(v61_elems[1]);
                arena_.push_back(v61_elems[2]);
                arena_.push_back(v61_elems[3]);
                arena_.push_back(v61_elems[4]);
                arena_.push_back(v61_elems[5]);
                arena_.push_back(v61_elems[6]);
                arena_.push_back(v61_elems[7]);
                v61_val.type = ValueType::Array;
                v61_val.data.arr.arena_start = seq_start;
                v61_val.data.arr.length = static_cast<uint32_t>(8);
            }
            (void)lbl_views;
            bool v60_ok = v61_ok;
            (void)v61_val;
            Value v60_val = makeNull();
            if (v60_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v60_start, cursor_);
                };
                (void)_text;
                auto& views = lbl_views;
                (void)views;
                v60_val = [&]() -> Value {
                    return createArray({ makeString("ViewBody"), views });
                }();
                if (v60_val.line == 0) {
                    v60_val.line = static_cast<uint32_t>(v60_startLine);
                    v60_val.col = static_cast<uint32_t>(v60_startCol);
                    v60_val.length = static_cast<uint32_t>(cursor_ - v60_start);
                }
            }
            if (v60_ok) return {true, v60_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("View Body");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_FuncDecl() {
        uint64_t memo_key = (static_cast<uint64_t>(10ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 10ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v71_start = cursor_;
            size_t v71_startLine = line_;
            size_t v71_startCol = col_;
            bool v72_ok = true;
            Value v72_val = makeNull();
            size_t v72_ss = 0, v72_sls = 0, v72_scs = 0, v72_sars = 0;
            save(v72_ss, v72_sls, v72_scs, v72_sars);
            Value v72_elems[9];
            Value lbl_name = makeNull();
            Value lbl_params = makeNull();
            Value lbl_returnType = makeNull();
            Value lbl_body = makeNull();
            if (v72_ok) {
                bool v73_ok = false;
                Value v73_val = makeNull();
                if (cursor_ + 4 <= input_.size() && input_.substr(cursor_, 4) == std::string_view("func", 4)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 4; i++) advance_char();
                    v73_ok = true;
                    v73_val = makeString("func");
                } else {
                    fail("\"func\"");
                }
                if (!v73_ok) { v72_ok = false; restore(v72_ss, v72_sls, v72_scs, v72_sars); }
                else { v72_elems[0] = v73_val; }
            }
            if (v72_ok) {
                auto v74_r = parse_Identifier();
                bool v74_ok = v74_r.success;
                Value v74_val = v74_r.value;
                if (!v74_ok) { v72_ok = false; restore(v72_ss, v72_sls, v72_scs, v72_sars); }
                else { v72_elems[1] = v74_val; }
                if (v72_ok) lbl_name = v72_elems[1];
            }
            if (v72_ok) {
                bool v75_ok = false;
                Value v75_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("(", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v75_ok = true;
                    v75_val = makeString("(");
                } else {
                    fail("\"(\"");
                }
                if (!v75_ok) { v72_ok = false; restore(v72_ss, v72_sls, v72_scs, v72_sars); }
                else { v72_elems[2] = v75_val; }
            }
            if (v72_ok) {
                bool v76_ok = true;
                Value v76_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    auto v77_r = parse_ParamList();
                    bool v77_ok = v77_r.success;
                    Value v77_val = v77_r.value;
                    if (v77_ok) { v76_val = v77_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v76_ok) { v72_ok = false; restore(v72_ss, v72_sls, v72_scs, v72_sars); }
                else { v72_elems[3] = v76_val; }
                if (v72_ok) lbl_params = v72_elems[3];
            }
            if (v72_ok) {
                bool v78_ok = false;
                Value v78_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(")", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v78_ok = true;
                    v78_val = makeString(")");
                } else {
                    fail("\")\"");
                }
                if (!v78_ok) { v72_ok = false; restore(v72_ss, v72_sls, v72_scs, v72_sars); }
                else { v72_elems[4] = v78_val; }
            }
            if (v72_ok) {
                bool v79_ok = true;
                Value v79_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    auto v80_r = parse_ReturnType();
                    bool v80_ok = v80_r.success;
                    Value v80_val = v80_r.value;
                    if (v80_ok) { v79_val = v80_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v79_ok) { v72_ok = false; restore(v72_ss, v72_sls, v72_scs, v72_sars); }
                else { v72_elems[5] = v79_val; }
                if (v72_ok) lbl_returnType = v72_elems[5];
            }
            if (v72_ok) {
                bool v81_ok = false;
                Value v81_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("{", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v81_ok = true;
                    v81_val = makeString("{");
                } else {
                    fail("\"{\"");
                }
                if (!v81_ok) { v72_ok = false; restore(v72_ss, v72_sls, v72_scs, v72_sars); }
                else { v72_elems[6] = v81_val; }
            }
            if (v72_ok) {
                bool v82_ok = true;
                Value v82_val = makeNull();
                {
                    size_t rep_start = arena_.head;
                    size_t rep_count = 0;
                    for (;;) {
                        size_t rc = 0, rl = 0, rco = 0, rar = 0;
                        save(rc, rl, rco, rar);
                        auto v83_r = parse_Statement();
                        bool v83_ok = v83_r.success;
                        Value v83_val = v83_r.value;
                        if (!v83_ok) { restore(rc, rl, rco, rar); break; }
                        if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                        arena_.push_back(v83_val);
                        rep_count++;
                    }
                    v82_val.type = ValueType::Array;
                    v82_val.data.arr.arena_start = rep_start;
                    v82_val.data.arr.length = static_cast<uint32_t>(rep_count);
                }
                if (!v82_ok) { v72_ok = false; restore(v72_ss, v72_sls, v72_scs, v72_sars); }
                else { v72_elems[7] = v82_val; }
                if (v72_ok) lbl_body = v72_elems[7];
            }
            if (v72_ok) {
                bool v84_ok = false;
                Value v84_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("}", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v84_ok = true;
                    v84_val = makeString("}");
                } else {
                    fail("\"}\"");
                }
                if (!v84_ok) { v72_ok = false; restore(v72_ss, v72_sls, v72_scs, v72_sars); }
                else { v72_elems[8] = v84_val; }
            }
            if (v72_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v72_elems[0]);
                arena_.push_back(v72_elems[1]);
                arena_.push_back(v72_elems[2]);
                arena_.push_back(v72_elems[3]);
                arena_.push_back(v72_elems[4]);
                arena_.push_back(v72_elems[5]);
                arena_.push_back(v72_elems[6]);
                arena_.push_back(v72_elems[7]);
                arena_.push_back(v72_elems[8]);
                v72_val.type = ValueType::Array;
                v72_val.data.arr.arena_start = seq_start;
                v72_val.data.arr.length = static_cast<uint32_t>(9);
            }
            (void)lbl_name;
            (void)lbl_params;
            (void)lbl_returnType;
            (void)lbl_body;
            bool v71_ok = v72_ok;
            (void)v72_val;
            Value v71_val = makeNull();
            if (v71_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v71_start, cursor_);
                };
                (void)_text;
                auto& name = lbl_name;
                (void)name;
                auto& params = lbl_params;
                (void)params;
                auto& returnType = lbl_returnType;
                (void)returnType;
                auto& body = lbl_body;
                (void)body;
                v71_val = [&]() -> Value {
                    return createArray({ 
        makeString("Function"), 
        name, 
        params.value_or(createArray({})), 
        returnType.value_or(makeNull()), 
        body 
    });
                }();
                if (v71_val.line == 0) {
                    v71_val.line = static_cast<uint32_t>(v71_startLine);
                    v71_val.col = static_cast<uint32_t>(v71_startCol);
                    v71_val.length = static_cast<uint32_t>(cursor_ - v71_start);
                }
            }
            if (v71_ok) return {true, v71_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Function");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_ParamList() {
        uint64_t memo_key = (static_cast<uint64_t>(11ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 11ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v85_ok = true;
            Value v85_val = makeNull();
            size_t v85_ss = 0, v85_sls = 0, v85_scs = 0, v85_sars = 0;
            save(v85_ss, v85_sls, v85_scs, v85_sars);
            Value v85_elems[2];
            if (v85_ok) {
                auto v86_r = parse_Param();
                bool v86_ok = v86_r.success;
                Value v86_val = v86_r.value;
                if (!v86_ok) { v85_ok = false; restore(v85_ss, v85_sls, v85_scs, v85_sars); }
                else { v85_elems[0] = v86_val; }
            }
            if (v85_ok) {
                bool v87_ok = true;
                Value v87_val = makeNull();
                {
                    size_t rep_start = arena_.head;
                    size_t rep_count = 0;
                    for (;;) {
                        size_t rc = 0, rl = 0, rco = 0, rar = 0;
                        save(rc, rl, rco, rar);
                        bool v88_ok = true;
                        Value v88_val = makeNull();
                        size_t v88_ss = 0, v88_sls = 0, v88_scs = 0, v88_sars = 0;
                        save(v88_ss, v88_sls, v88_scs, v88_sars);
                        Value v88_elems[2];
                        if (v88_ok) {
                            bool v89_ok = false;
                            Value v89_val = makeNull();
                            if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(",", 1)) {
                                size_t s = cursor_; (void)s;
                                for (size_t i = 0; i < 1; i++) advance_char();
                                v89_ok = true;
                                v89_val = makeString(",");
                            } else {
                                fail("\",\"");
                            }
                            if (!v89_ok) { v88_ok = false; restore(v88_ss, v88_sls, v88_scs, v88_sars); }
                            else { v88_elems[0] = v89_val; }
                        }
                        if (v88_ok) {
                            auto v90_r = parse_Param();
                            bool v90_ok = v90_r.success;
                            Value v90_val = v90_r.value;
                            if (!v90_ok) { v88_ok = false; restore(v88_ss, v88_sls, v88_scs, v88_sars); }
                            else { v88_elems[1] = v90_val; }
                        }
                        if (v88_ok) {
                            size_t seq_start = arena_.head;
                            arena_.push_back(v88_elems[0]);
                            arena_.push_back(v88_elems[1]);
                            v88_val.type = ValueType::Array;
                            v88_val.data.arr.arena_start = seq_start;
                            v88_val.data.arr.length = static_cast<uint32_t>(2);
                        }
                        if (!v88_ok) { restore(rc, rl, rco, rar); break; }
                        if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                        arena_.push_back(v88_val);
                        rep_count++;
                    }
                    v87_val.type = ValueType::Array;
                    v87_val.data.arr.arena_start = rep_start;
                    v87_val.data.arr.length = static_cast<uint32_t>(rep_count);
                }
                if (!v87_ok) { v85_ok = false; restore(v85_ss, v85_sls, v85_scs, v85_sars); }
                else { v85_elems[1] = v87_val; }
            }
            if (v85_ok) {
                v85_val = v85_elems[0];
            }
            if (v85_ok) return {true, v85_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Parameters");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_Param() {
        uint64_t memo_key = (static_cast<uint64_t>(12ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 12ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v91_start = cursor_;
            size_t v91_startLine = line_;
            size_t v91_startCol = col_;
            bool v92_ok = true;
            Value v92_val = makeNull();
            size_t v92_ss = 0, v92_sls = 0, v92_scs = 0, v92_sars = 0;
            save(v92_ss, v92_sls, v92_scs, v92_sars);
            Value v92_elems[4];
            Value lbl_label = makeNull();
            Value lbl_name = makeNull();
            Value lbl_type = makeNull();
            if (v92_ok) {
                bool v93_ok = true;
                Value v93_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    auto v94_r = parse_Identifier();
                    bool v94_ok = v94_r.success;
                    Value v94_val = v94_r.value;
                    if (v94_ok) { v93_val = v94_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v93_ok) { v92_ok = false; restore(v92_ss, v92_sls, v92_scs, v92_sars); }
                else { v92_elems[0] = v93_val; }
                if (v92_ok) lbl_label = v92_elems[0];
            }
            if (v92_ok) {
                auto v95_r = parse_Identifier();
                bool v95_ok = v95_r.success;
                Value v95_val = v95_r.value;
                if (!v95_ok) { v92_ok = false; restore(v92_ss, v92_sls, v92_scs, v92_sars); }
                else { v92_elems[1] = v95_val; }
                if (v92_ok) lbl_name = v92_elems[1];
            }
            if (v92_ok) {
                bool v96_ok = false;
                Value v96_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(":", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v96_ok = true;
                    v96_val = makeString(":");
                } else {
                    fail("\":\"");
                }
                if (!v96_ok) { v92_ok = false; restore(v92_ss, v92_sls, v92_scs, v92_sars); }
                else { v92_elems[2] = v96_val; }
            }
            if (v92_ok) {
                auto v97_r = parse_Type();
                bool v97_ok = v97_r.success;
                Value v97_val = v97_r.value;
                if (!v97_ok) { v92_ok = false; restore(v92_ss, v92_sls, v92_scs, v92_sars); }
                else { v92_elems[3] = v97_val; }
                if (v92_ok) lbl_type = v92_elems[3];
            }
            if (v92_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v92_elems[0]);
                arena_.push_back(v92_elems[1]);
                arena_.push_back(v92_elems[2]);
                arena_.push_back(v92_elems[3]);
                v92_val.type = ValueType::Array;
                v92_val.data.arr.arena_start = seq_start;
                v92_val.data.arr.length = static_cast<uint32_t>(4);
            }
            (void)lbl_label;
            (void)lbl_name;
            (void)lbl_type;
            bool v91_ok = v92_ok;
            (void)v92_val;
            Value v91_val = makeNull();
            if (v91_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v91_start, cursor_);
                };
                (void)_text;
                auto& label = lbl_label;
                (void)label;
                auto& name = lbl_name;
                (void)name;
                auto& type = lbl_type;
                (void)type;
                v91_val = [&]() -> Value {
                    return createArray({ label.value_or(makeNull()), name, type });
                }();
                if (v91_val.line == 0) {
                    v91_val.line = static_cast<uint32_t>(v91_startLine);
                    v91_val.col = static_cast<uint32_t>(v91_startCol);
                    v91_val.length = static_cast<uint32_t>(cursor_ - v91_start);
                }
            }
            if (v91_ok) return {true, v91_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Parameter");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_ReturnType() {
        uint64_t memo_key = (static_cast<uint64_t>(13ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 13ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v98_ok = true;
            Value v98_val = makeNull();
            size_t v98_ss = 0, v98_sls = 0, v98_scs = 0, v98_sars = 0;
            save(v98_ss, v98_sls, v98_scs, v98_sars);
            Value v98_elems[2];
            if (v98_ok) {
                bool v99_ok = false;
                Value v99_val = makeNull();
                if (cursor_ + 2 <= input_.size() && input_.substr(cursor_, 2) == std::string_view("->", 2)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 2; i++) advance_char();
                    v99_ok = true;
                    v99_val = makeString("->");
                } else {
                    fail("\"->\"");
                }
                if (!v99_ok) { v98_ok = false; restore(v98_ss, v98_sls, v98_scs, v98_sars); }
                else { v98_elems[0] = v99_val; }
            }
            if (v98_ok) {
                auto v100_r = parse_Type();
                bool v100_ok = v100_r.success;
                Value v100_val = v100_r.value;
                if (!v100_ok) { v98_ok = false; restore(v98_ss, v98_sls, v98_scs, v98_sars); }
                else { v98_elems[1] = v100_val; }
            }
            if (v98_ok) {
                v98_val = v98_elems[1];
            }
            if (v98_ok) return {true, v98_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Return Type");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_Statement() {
        uint64_t memo_key = (static_cast<uint64_t>(14ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 14ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v101_ok = false;
            Value v101_val = makeNull();
            {
                size_t cc = 0, cl = 0, cco = 0, car = 0;
                save(cc, cl, cco, car);
                if (!v101_ok) {
                    {
                        auto v102_r = parse_PropertyDecl();
                        bool v102_ok = v102_r.success;
                        Value v102_val = v102_r.value;
                        if (v102_ok) { v101_ok = true; v101_val = v102_val; }
                    }
                }
                if (!v101_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v103_r = parse_Assignment();
                        bool v103_ok = v103_r.success;
                        Value v103_val = v103_r.value;
                        if (v103_ok) { v101_ok = true; v101_val = v103_val; }
                    }
                }
                if (!v101_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v104_r = parse_ReturnStmt();
                        bool v104_ok = v104_r.success;
                        Value v104_val = v104_r.value;
                        if (v104_ok) { v101_ok = true; v101_val = v104_val; }
                    }
                }
                if (!v101_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v105_r = parse_Expression();
                        bool v105_ok = v105_r.success;
                        Value v105_val = v105_r.value;
                        if (v105_ok) { v101_ok = true; v101_val = v105_val; }
                    }
                }
            }
            if (v101_ok) return {true, v101_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Statement");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_Assignment() {
        uint64_t memo_key = (static_cast<uint64_t>(15ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 15ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v106_start = cursor_;
            size_t v106_startLine = line_;
            size_t v106_startCol = col_;
            bool v107_ok = true;
            Value v107_val = makeNull();
            size_t v107_ss = 0, v107_sls = 0, v107_scs = 0, v107_sars = 0;
            save(v107_ss, v107_sls, v107_scs, v107_sars);
            Value v107_elems[3];
            Value lbl_target = makeNull();
            Value lbl_op = makeNull();
            Value lbl_val = makeNull();
            if (v107_ok) {
                auto v108_r = parse_Identifier();
                bool v108_ok = v108_r.success;
                Value v108_val = v108_r.value;
                if (!v108_ok) { v107_ok = false; restore(v107_ss, v107_sls, v107_scs, v107_sars); }
                else { v107_elems[0] = v108_val; }
                if (v107_ok) lbl_target = v107_elems[0];
            }
            if (v107_ok) {
                auto v109_r = parse_AssignOp();
                bool v109_ok = v109_r.success;
                Value v109_val = v109_r.value;
                if (!v109_ok) { v107_ok = false; restore(v107_ss, v107_sls, v107_scs, v107_sars); }
                else { v107_elems[1] = v109_val; }
                if (v107_ok) lbl_op = v107_elems[1];
            }
            if (v107_ok) {
                auto v110_r = parse_Expression();
                bool v110_ok = v110_r.success;
                Value v110_val = v110_r.value;
                if (!v110_ok) { v107_ok = false; restore(v107_ss, v107_sls, v107_scs, v107_sars); }
                else { v107_elems[2] = v110_val; }
                if (v107_ok) lbl_val = v107_elems[2];
            }
            if (v107_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v107_elems[0]);
                arena_.push_back(v107_elems[1]);
                arena_.push_back(v107_elems[2]);
                v107_val.type = ValueType::Array;
                v107_val.data.arr.arena_start = seq_start;
                v107_val.data.arr.length = static_cast<uint32_t>(3);
            }
            (void)lbl_target;
            (void)lbl_op;
            (void)lbl_val;
            bool v106_ok = v107_ok;
            (void)v107_val;
            Value v106_val = makeNull();
            if (v106_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v106_start, cursor_);
                };
                (void)_text;
                auto& target = lbl_target;
                (void)target;
                auto& op = lbl_op;
                (void)op;
                auto& val = lbl_val;
                (void)val;
                v106_val = [&]() -> Value {
                    return createArray({ makeString("Assign"), op, target, val });
                }();
                if (v106_val.line == 0) {
                    v106_val.line = static_cast<uint32_t>(v106_startLine);
                    v106_val.col = static_cast<uint32_t>(v106_startCol);
                    v106_val.length = static_cast<uint32_t>(cursor_ - v106_start);
                }
            }
            if (v106_ok) return {true, v106_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Assignment");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_AssignOp() {
        uint64_t memo_key = (static_cast<uint64_t>(16ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 16ULL) & MEMO_MASK;
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        bool v111_ok = false;
        Value v111_val = makeNull();
        {
            size_t cc = 0, cl = 0, cco = 0, car = 0;
            save(cc, cl, cco, car);
            if (!v111_ok) {
                {
                    bool v112_ok = false;
                    Value v112_val = makeNull();
                    if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("=", 1)) {
                        size_t s = cursor_; (void)s;
                        for (size_t i = 0; i < 1; i++) advance_char();
                        v112_ok = true;
                        v112_val = makeString("=");
                    } else {
                        fail("\"=\"");
                    }
                    if (v112_ok) { v111_ok = true; v111_val = v112_val; }
                }
            }
            if (!v111_ok) {
                restore(cc, cl, cco, car);
                {
                    bool v113_ok = false;
                    Value v113_val = makeNull();
                    if (cursor_ + 2 <= input_.size() && input_.substr(cursor_, 2) == std::string_view("+=", 2)) {
                        size_t s = cursor_; (void)s;
                        for (size_t i = 0; i < 2; i++) advance_char();
                        v113_ok = true;
                        v113_val = makeString("+=");
                    } else {
                        fail("\"+=\"");
                    }
                    if (v113_ok) { v111_ok = true; v111_val = v113_val; }
                }
            }
            if (!v111_ok) {
                restore(cc, cl, cco, car);
                {
                    bool v114_ok = false;
                    Value v114_val = makeNull();
                    if (cursor_ + 2 <= input_.size() && input_.substr(cursor_, 2) == std::string_view("-=", 2)) {
                        size_t s = cursor_; (void)s;
                        for (size_t i = 0; i < 2; i++) advance_char();
                        v114_ok = true;
                        v114_val = makeString("-=");
                    } else {
                        fail("\"-=\"");
                    }
                    if (v114_ok) { v111_ok = true; v111_val = v114_val; }
                }
            }
            if (!v111_ok) {
                restore(cc, cl, cco, car);
                {
                    bool v115_ok = false;
                    Value v115_val = makeNull();
                    if (cursor_ + 2 <= input_.size() && input_.substr(cursor_, 2) == std::string_view("*=", 2)) {
                        size_t s = cursor_; (void)s;
                        for (size_t i = 0; i < 2; i++) advance_char();
                        v115_ok = true;
                        v115_val = makeString("*=");
                    } else {
                        fail("\"*=\"");
                    }
                    if (v115_ok) { v111_ok = true; v111_val = v115_val; }
                }
            }
            if (!v111_ok) {
                restore(cc, cl, cco, car);
                {
                    bool v116_ok = false;
                    Value v116_val = makeNull();
                    if (cursor_ + 2 <= input_.size() && input_.substr(cursor_, 2) == std::string_view("/=", 2)) {
                        size_t s = cursor_; (void)s;
                        for (size_t i = 0; i < 2; i++) advance_char();
                        v116_ok = true;
                        v116_val = makeString("/=");
                    } else {
                        fail("\"/=\"");
                    }
                    if (v116_ok) { v111_ok = true; v111_val = v116_val; }
                }
            }
        }
        if (v111_ok) {
            return {true, v111_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        } else {
            fail("Assignment Operator");
            restore(sc, sl, sco, sar);
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
    }
    
    Result parse_ReturnStmt() {
        uint64_t memo_key = (static_cast<uint64_t>(17ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 17ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v117_start = cursor_;
            size_t v117_startLine = line_;
            size_t v117_startCol = col_;
            bool v118_ok = true;
            Value v118_val = makeNull();
            size_t v118_ss = 0, v118_sls = 0, v118_scs = 0, v118_sars = 0;
            save(v118_ss, v118_sls, v118_scs, v118_sars);
            Value v118_elems[2];
            if (v118_ok) {
                bool v119_ok = false;
                Value v119_val = makeNull();
                if (cursor_ + 6 <= input_.size() && input_.substr(cursor_, 6) == std::string_view("return", 6)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 6; i++) advance_char();
                    v119_ok = true;
                    v119_val = makeString("return");
                } else {
                    fail("\"return\"");
                }
                if (!v119_ok) { v118_ok = false; restore(v118_ss, v118_sls, v118_scs, v118_sars); }
                else { v118_elems[0] = v119_val; }
            }
            if (v118_ok) {
                bool v120_ok = true;
                Value v120_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    auto v121_r = parse_Expression();
                    bool v121_ok = v121_r.success;
                    Value v121_val = v121_r.value;
                    if (v121_ok) { v120_val = v121_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v120_ok) { v118_ok = false; restore(v118_ss, v118_sls, v118_scs, v118_sars); }
                else { v118_elems[1] = v120_val; }
            }
            if (v118_ok) {
                v118_val = v118_elems[1];
            }
            bool v117_ok = v118_ok;
            (void)v118_val;
            Value v117_val = makeNull();
            if (v117_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v117_start, cursor_);
                };
                (void)_text;
                v117_val = [&]() -> Value {
                    return createArray({ makeString("Return"), _1.value_or(makeNull()) });
                }();
                if (v117_val.line == 0) {
                    v117_val.line = static_cast<uint32_t>(v117_startLine);
                    v117_val.col = static_cast<uint32_t>(v117_startCol);
                    v117_val.length = static_cast<uint32_t>(cursor_ - v117_start);
                }
            }
            if (v117_ok) return {true, v117_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Return");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_Expression() {
        uint64_t memo_key = (static_cast<uint64_t>(18ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 18ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v122_ok = false;
            Value v122_val = makeNull();
            {
                size_t cc = 0, cl = 0, cco = 0, car = 0;
                save(cc, cl, cco, car);
                if (!v122_ok) {
                    {
                        auto v123_r = parse_ViewInstantiation();
                        bool v123_ok = v123_r.success;
                        Value v123_val = v123_r.value;
                        if (v123_ok) { v122_ok = true; v122_val = v123_val; }
                    }
                }
                if (!v122_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v124_r = parse_CallExpr();
                        bool v124_ok = v124_r.success;
                        Value v124_val = v124_r.value;
                        if (v124_ok) { v122_ok = true; v122_val = v124_val; }
                    }
                }
                if (!v122_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v125_r = parse_BinaryExpr();
                        bool v125_ok = v125_r.success;
                        Value v125_val = v125_r.value;
                        if (v125_ok) { v122_ok = true; v122_val = v125_val; }
                    }
                }
                if (!v122_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v126_r = parse_PrimaryExpr();
                        bool v126_ok = v126_r.success;
                        Value v126_val = v126_r.value;
                        if (v126_ok) { v122_ok = true; v122_val = v126_val; }
                    }
                }
            }
            if (v122_ok) return {true, v122_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Expression");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_ViewInstantiation() {
        uint64_t memo_key = (static_cast<uint64_t>(19ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 19ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v127_start = cursor_;
            size_t v127_startLine = line_;
            size_t v127_startCol = col_;
            bool v128_ok = true;
            Value v128_val = makeNull();
            size_t v128_ss = 0, v128_sls = 0, v128_scs = 0, v128_sars = 0;
            save(v128_ss, v128_sls, v128_scs, v128_sars);
            Value v128_elems[7];
            Value lbl_name = makeNull();
            Value lbl_args = makeNull();
            Value lbl_children = makeNull();
            if (v128_ok) {
                auto v129_r = parse_Identifier();
                bool v129_ok = v129_r.success;
                Value v129_val = v129_r.value;
                if (!v129_ok) { v128_ok = false; restore(v128_ss, v128_sls, v128_scs, v128_sars); }
                else { v128_elems[0] = v129_val; }
                if (v128_ok) lbl_name = v128_elems[0];
            }
            if (v128_ok) {
                bool v130_ok = false;
                Value v130_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("(", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v130_ok = true;
                    v130_val = makeString("(");
                } else {
                    fail("\"(\"");
                }
                if (!v130_ok) { v128_ok = false; restore(v128_ss, v128_sls, v128_scs, v128_sars); }
                else { v128_elems[1] = v130_val; }
            }
            if (v128_ok) {
                bool v131_ok = true;
                Value v131_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    auto v132_r = parse_CallArgs();
                    bool v132_ok = v132_r.success;
                    Value v132_val = v132_r.value;
                    if (v132_ok) { v131_val = v132_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v131_ok) { v128_ok = false; restore(v128_ss, v128_sls, v128_scs, v128_sars); }
                else { v128_elems[2] = v131_val; }
                if (v128_ok) lbl_args = v128_elems[2];
            }
            if (v128_ok) {
                bool v133_ok = false;
                Value v133_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(")", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v133_ok = true;
                    v133_val = makeString(")");
                } else {
                    fail("\")\"");
                }
                if (!v133_ok) { v128_ok = false; restore(v128_ss, v128_sls, v128_scs, v128_sars); }
                else { v128_elems[3] = v133_val; }
            }
            if (v128_ok) {
                bool v134_ok = false;
                Value v134_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("{", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v134_ok = true;
                    v134_val = makeString("{");
                } else {
                    fail("\"{\"");
                }
                if (!v134_ok) { v128_ok = false; restore(v128_ss, v128_sls, v128_scs, v128_sars); }
                else { v128_elems[4] = v134_val; }
            }
            if (v128_ok) {
                bool v135_ok = true;
                Value v135_val = makeNull();
                {
                    size_t rep_start = arena_.head;
                    size_t rep_count = 0;
                    for (;;) {
                        size_t rc = 0, rl = 0, rco = 0, rar = 0;
                        save(rc, rl, rco, rar);
                        auto v136_r = parse_Expression();
                        bool v136_ok = v136_r.success;
                        Value v136_val = v136_r.value;
                        if (!v136_ok) { restore(rc, rl, rco, rar); break; }
                        if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                        arena_.push_back(v136_val);
                        rep_count++;
                    }
                    v135_val.type = ValueType::Array;
                    v135_val.data.arr.arena_start = rep_start;
                    v135_val.data.arr.length = static_cast<uint32_t>(rep_count);
                }
                if (!v135_ok) { v128_ok = false; restore(v128_ss, v128_sls, v128_scs, v128_sars); }
                else { v128_elems[5] = v135_val; }
                if (v128_ok) lbl_children = v128_elems[5];
            }
            if (v128_ok) {
                bool v137_ok = false;
                Value v137_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("}", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v137_ok = true;
                    v137_val = makeString("}");
                } else {
                    fail("\"}\"");
                }
                if (!v137_ok) { v128_ok = false; restore(v128_ss, v128_sls, v128_scs, v128_sars); }
                else { v128_elems[6] = v137_val; }
            }
            if (v128_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v128_elems[0]);
                arena_.push_back(v128_elems[1]);
                arena_.push_back(v128_elems[2]);
                arena_.push_back(v128_elems[3]);
                arena_.push_back(v128_elems[4]);
                arena_.push_back(v128_elems[5]);
                arena_.push_back(v128_elems[6]);
                v128_val.type = ValueType::Array;
                v128_val.data.arr.arena_start = seq_start;
                v128_val.data.arr.length = static_cast<uint32_t>(7);
            }
            (void)lbl_name;
            (void)lbl_args;
            (void)lbl_children;
            bool v127_ok = v128_ok;
            (void)v128_val;
            Value v127_val = makeNull();
            if (v127_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v127_start, cursor_);
                };
                (void)_text;
                auto& name = lbl_name;
                (void)name;
                auto& args = lbl_args;
                (void)args;
                auto& children = lbl_children;
                (void)children;
                v127_val = [&]() -> Value {
                    return createArray({ makeString("ViewNode"), name, args.value_or(makeNull()), children });
                }();
                if (v127_val.line == 0) {
                    v127_val.line = static_cast<uint32_t>(v127_startLine);
                    v127_val.col = static_cast<uint32_t>(v127_startCol);
                    v127_val.length = static_cast<uint32_t>(cursor_ - v127_start);
                }
            }
            if (v127_ok) return {true, v127_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("UI Element");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_CallExpr() {
        uint64_t memo_key = (static_cast<uint64_t>(20ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 20ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v138_start = cursor_;
            size_t v138_startLine = line_;
            size_t v138_startCol = col_;
            bool v139_ok = true;
            Value v139_val = makeNull();
            size_t v139_ss = 0, v139_sls = 0, v139_scs = 0, v139_sars = 0;
            save(v139_ss, v139_sls, v139_scs, v139_sars);
            Value v139_elems[4];
            Value lbl_target = makeNull();
            Value lbl_args = makeNull();
            if (v139_ok) {
                auto v140_r = parse_Identifier();
                bool v140_ok = v140_r.success;
                Value v140_val = v140_r.value;
                if (!v140_ok) { v139_ok = false; restore(v139_ss, v139_sls, v139_scs, v139_sars); }
                else { v139_elems[0] = v140_val; }
                if (v139_ok) lbl_target = v139_elems[0];
            }
            if (v139_ok) {
                bool v141_ok = false;
                Value v141_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("(", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v141_ok = true;
                    v141_val = makeString("(");
                } else {
                    fail("\"(\"");
                }
                if (!v141_ok) { v139_ok = false; restore(v139_ss, v139_sls, v139_scs, v139_sars); }
                else { v139_elems[1] = v141_val; }
            }
            if (v139_ok) {
                bool v142_ok = true;
                Value v142_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    auto v143_r = parse_CallArgs();
                    bool v143_ok = v143_r.success;
                    Value v143_val = v143_r.value;
                    if (v143_ok) { v142_val = v143_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v142_ok) { v139_ok = false; restore(v139_ss, v139_sls, v139_scs, v139_sars); }
                else { v139_elems[2] = v142_val; }
                if (v139_ok) lbl_args = v139_elems[2];
            }
            if (v139_ok) {
                bool v144_ok = false;
                Value v144_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(")", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v144_ok = true;
                    v144_val = makeString(")");
                } else {
                    fail("\")\"");
                }
                if (!v144_ok) { v139_ok = false; restore(v139_ss, v139_sls, v139_scs, v139_sars); }
                else { v139_elems[3] = v144_val; }
            }
            if (v139_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v139_elems[0]);
                arena_.push_back(v139_elems[1]);
                arena_.push_back(v139_elems[2]);
                arena_.push_back(v139_elems[3]);
                v139_val.type = ValueType::Array;
                v139_val.data.arr.arena_start = seq_start;
                v139_val.data.arr.length = static_cast<uint32_t>(4);
            }
            (void)lbl_target;
            (void)lbl_args;
            bool v138_ok = v139_ok;
            (void)v139_val;
            Value v138_val = makeNull();
            if (v138_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v138_start, cursor_);
                };
                (void)_text;
                auto& target = lbl_target;
                (void)target;
                auto& args = lbl_args;
                (void)args;
                v138_val = [&]() -> Value {
                    return createArray({ makeString("Call"), target, args.value_or(makeNull()) });
                }();
                if (v138_val.line == 0) {
                    v138_val.line = static_cast<uint32_t>(v138_startLine);
                    v138_val.col = static_cast<uint32_t>(v138_startCol);
                    v138_val.length = static_cast<uint32_t>(cursor_ - v138_start);
                }
            }
            if (v138_ok) return {true, v138_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Call");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_CallArgs() {
        uint64_t memo_key = (static_cast<uint64_t>(21ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 21ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v145_ok = true;
            Value v145_val = makeNull();
            size_t v145_ss = 0, v145_sls = 0, v145_scs = 0, v145_sars = 0;
            save(v145_ss, v145_sls, v145_scs, v145_sars);
            Value v145_elems[2];
            if (v145_ok) {
                auto v146_r = parse_CallArg();
                bool v146_ok = v146_r.success;
                Value v146_val = v146_r.value;
                if (!v146_ok) { v145_ok = false; restore(v145_ss, v145_sls, v145_scs, v145_sars); }
                else { v145_elems[0] = v146_val; }
            }
            if (v145_ok) {
                bool v147_ok = true;
                Value v147_val = makeNull();
                {
                    size_t rep_start = arena_.head;
                    size_t rep_count = 0;
                    for (;;) {
                        size_t rc = 0, rl = 0, rco = 0, rar = 0;
                        save(rc, rl, rco, rar);
                        bool v148_ok = true;
                        Value v148_val = makeNull();
                        size_t v148_ss = 0, v148_sls = 0, v148_scs = 0, v148_sars = 0;
                        save(v148_ss, v148_sls, v148_scs, v148_sars);
                        Value v148_elems[2];
                        if (v148_ok) {
                            bool v149_ok = false;
                            Value v149_val = makeNull();
                            if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(",", 1)) {
                                size_t s = cursor_; (void)s;
                                for (size_t i = 0; i < 1; i++) advance_char();
                                v149_ok = true;
                                v149_val = makeString(",");
                            } else {
                                fail("\",\"");
                            }
                            if (!v149_ok) { v148_ok = false; restore(v148_ss, v148_sls, v148_scs, v148_sars); }
                            else { v148_elems[0] = v149_val; }
                        }
                        if (v148_ok) {
                            auto v150_r = parse_CallArg();
                            bool v150_ok = v150_r.success;
                            Value v150_val = v150_r.value;
                            if (!v150_ok) { v148_ok = false; restore(v148_ss, v148_sls, v148_scs, v148_sars); }
                            else { v148_elems[1] = v150_val; }
                        }
                        if (v148_ok) {
                            size_t seq_start = arena_.head;
                            arena_.push_back(v148_elems[0]);
                            arena_.push_back(v148_elems[1]);
                            v148_val.type = ValueType::Array;
                            v148_val.data.arr.arena_start = seq_start;
                            v148_val.data.arr.length = static_cast<uint32_t>(2);
                        }
                        if (!v148_ok) { restore(rc, rl, rco, rar); break; }
                        if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                        arena_.push_back(v148_val);
                        rep_count++;
                    }
                    v147_val.type = ValueType::Array;
                    v147_val.data.arr.arena_start = rep_start;
                    v147_val.data.arr.length = static_cast<uint32_t>(rep_count);
                }
                if (!v147_ok) { v145_ok = false; restore(v145_ss, v145_sls, v145_scs, v145_sars); }
                else { v145_elems[1] = v147_val; }
            }
            if (v145_ok) {
                v145_val = v145_elems[0];
            }
            if (v145_ok) return {true, v145_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Call Arguments");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_CallArg() {
        uint64_t memo_key = (static_cast<uint64_t>(22ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 22ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v151_ok = true;
            Value v151_val = makeNull();
            size_t v151_ss = 0, v151_sls = 0, v151_scs = 0, v151_sars = 0;
            save(v151_ss, v151_sls, v151_scs, v151_sars);
            Value v151_elems[2];
            if (v151_ok) {
                bool v152_ok = true;
                Value v152_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    bool v153_ok = true;
                    Value v153_val = makeNull();
                    size_t v153_ss = 0, v153_sls = 0, v153_scs = 0, v153_sars = 0;
                    save(v153_ss, v153_sls, v153_scs, v153_sars);
                    Value v153_elems[2];
                    if (v153_ok) {
                        auto v154_r = parse_Identifier();
                        bool v154_ok = v154_r.success;
                        Value v154_val = v154_r.value;
                        if (!v154_ok) { v153_ok = false; restore(v153_ss, v153_sls, v153_scs, v153_sars); }
                        else { v153_elems[0] = v154_val; }
                    }
                    if (v153_ok) {
                        bool v155_ok = false;
                        Value v155_val = makeNull();
                        if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(":", 1)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 1; i++) advance_char();
                            v155_ok = true;
                            v155_val = makeString(":");
                        } else {
                            fail("\":\"");
                        }
                        if (!v155_ok) { v153_ok = false; restore(v153_ss, v153_sls, v153_scs, v153_sars); }
                        else { v153_elems[1] = v155_val; }
                    }
                    if (v153_ok) {
                        size_t seq_start = arena_.head;
                        arena_.push_back(v153_elems[0]);
                        arena_.push_back(v153_elems[1]);
                        v153_val.type = ValueType::Array;
                        v153_val.data.arr.arena_start = seq_start;
                        v153_val.data.arr.length = static_cast<uint32_t>(2);
                    }
                    if (v153_ok) { v152_val = v153_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v152_ok) { v151_ok = false; restore(v151_ss, v151_sls, v151_scs, v151_sars); }
                else { v151_elems[0] = v152_val; }
            }
            if (v151_ok) {
                auto v156_r = parse_Expression();
                bool v156_ok = v156_r.success;
                Value v156_val = v156_r.value;
                if (!v156_ok) { v151_ok = false; restore(v151_ss, v151_sls, v151_scs, v151_sars); }
                else { v151_elems[1] = v156_val; }
            }
            if (v151_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v151_elems[0]);
                arena_.push_back(v151_elems[1]);
                v151_val.type = ValueType::Array;
                v151_val.data.arr.arena_start = seq_start;
                v151_val.data.arr.length = static_cast<uint32_t>(2);
            }
            if (v151_ok) return {true, v151_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Argument");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_BinaryExpr() {
        uint64_t memo_key = (static_cast<uint64_t>(23ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 23ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v157_start = cursor_;
            size_t v157_startLine = line_;
            size_t v157_startCol = col_;
            bool v158_ok = true;
            Value v158_val = makeNull();
            size_t v158_ss = 0, v158_sls = 0, v158_scs = 0, v158_sars = 0;
            save(v158_ss, v158_sls, v158_scs, v158_sars);
            Value v158_elems[3];
            Value lbl_left = makeNull();
            Value lbl_op = makeNull();
            Value lbl_right = makeNull();
            if (v158_ok) {
                auto v159_r = parse_PrimaryExpr();
                bool v159_ok = v159_r.success;
                Value v159_val = v159_r.value;
                if (!v159_ok) { v158_ok = false; restore(v158_ss, v158_sls, v158_scs, v158_sars); }
                else { v158_elems[0] = v159_val; }
                if (v158_ok) lbl_left = v158_elems[0];
            }
            if (v158_ok) {
                auto v160_r = parse_Operator();
                bool v160_ok = v160_r.success;
                Value v160_val = v160_r.value;
                if (!v160_ok) { v158_ok = false; restore(v158_ss, v158_sls, v158_scs, v158_sars); }
                else { v158_elems[1] = v160_val; }
                if (v158_ok) lbl_op = v158_elems[1];
            }
            if (v158_ok) {
                auto v161_r = parse_Expression();
                bool v161_ok = v161_r.success;
                Value v161_val = v161_r.value;
                if (!v161_ok) { v158_ok = false; restore(v158_ss, v158_sls, v158_scs, v158_sars); }
                else { v158_elems[2] = v161_val; }
                if (v158_ok) lbl_right = v158_elems[2];
            }
            if (v158_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v158_elems[0]);
                arena_.push_back(v158_elems[1]);
                arena_.push_back(v158_elems[2]);
                v158_val.type = ValueType::Array;
                v158_val.data.arr.arena_start = seq_start;
                v158_val.data.arr.length = static_cast<uint32_t>(3);
            }
            (void)lbl_left;
            (void)lbl_op;
            (void)lbl_right;
            bool v157_ok = v158_ok;
            (void)v158_val;
            Value v157_val = makeNull();
            if (v157_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v157_start, cursor_);
                };
                (void)_text;
                auto& left = lbl_left;
                (void)left;
                auto& op = lbl_op;
                (void)op;
                auto& right = lbl_right;
                (void)right;
                v157_val = [&]() -> Value {
                    return createArray({ makeString("Binary"), op, left, right });
                }();
                if (v157_val.line == 0) {
                    v157_val.line = static_cast<uint32_t>(v157_startLine);
                    v157_val.col = static_cast<uint32_t>(v157_startCol);
                    v157_val.length = static_cast<uint32_t>(cursor_ - v157_start);
                }
            }
            if (v157_ok) return {true, v157_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Binary Operation");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_PrimaryExpr() {
        uint64_t memo_key = (static_cast<uint64_t>(24ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 24ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v162_ok = false;
            Value v162_val = makeNull();
            {
                size_t cc = 0, cl = 0, cco = 0, car = 0;
                save(cc, cl, cco, car);
                if (!v162_ok) {
                    {
                        auto v163_r = parse_Literal();
                        bool v163_ok = v163_r.success;
                        Value v163_val = v163_r.value;
                        if (v163_ok) { v162_ok = true; v162_val = v163_val; }
                    }
                }
                if (!v162_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v164_r = parse_MemberAccess();
                        bool v164_ok = v164_r.success;
                        Value v164_val = v164_r.value;
                        if (v164_ok) { v162_ok = true; v162_val = v164_val; }
                    }
                }
                if (!v162_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v165_r = parse_Identifier();
                        bool v165_ok = v165_r.success;
                        Value v165_val = v165_r.value;
                        if (v165_ok) { v162_ok = true; v162_val = v165_val; }
                    }
                }
                if (!v162_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v166_ok = true;
                        Value v166_val = makeNull();
                        size_t v166_ss = 0, v166_sls = 0, v166_scs = 0, v166_sars = 0;
                        save(v166_ss, v166_sls, v166_scs, v166_sars);
                        Value v166_elems[3];
                        if (v166_ok) {
                            bool v167_ok = false;
                            Value v167_val = makeNull();
                            if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("(", 1)) {
                                size_t s = cursor_; (void)s;
                                for (size_t i = 0; i < 1; i++) advance_char();
                                v167_ok = true;
                                v167_val = makeString("(");
                            } else {
                                fail("\"(\"");
                            }
                            if (!v167_ok) { v166_ok = false; restore(v166_ss, v166_sls, v166_scs, v166_sars); }
                            else { v166_elems[0] = v167_val; }
                        }
                        if (v166_ok) {
                            auto v168_r = parse_Expression();
                            bool v168_ok = v168_r.success;
                            Value v168_val = v168_r.value;
                            if (!v168_ok) { v166_ok = false; restore(v166_ss, v166_sls, v166_scs, v166_sars); }
                            else { v166_elems[1] = v168_val; }
                        }
                        if (v166_ok) {
                            bool v169_ok = false;
                            Value v169_val = makeNull();
                            if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(")", 1)) {
                                size_t s = cursor_; (void)s;
                                for (size_t i = 0; i < 1; i++) advance_char();
                                v169_ok = true;
                                v169_val = makeString(")");
                            } else {
                                fail("\")\"");
                            }
                            if (!v169_ok) { v166_ok = false; restore(v166_ss, v166_sls, v166_scs, v166_sars); }
                            else { v166_elems[2] = v169_val; }
                        }
                        if (v166_ok) {
                            v166_val = v166_elems[1];
                        }
                        if (v166_ok) { v162_ok = true; v162_val = v166_val; }
                    }
                }
            }
            if (v162_ok) return {true, v162_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Primary");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_MemberAccess() {
        uint64_t memo_key = (static_cast<uint64_t>(25ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 25ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v170_ok = false;
            Value v170_val = makeNull();
            {
                size_t cc = 0, cl = 0, cco = 0, car = 0;
                save(cc, cl, cco, car);
                if (!v170_ok) {
                    {
                        size_t v171_start = cursor_;
                        size_t v171_startLine = line_;
                        size_t v171_startCol = col_;
                        bool v172_ok = true;
                        Value v172_val = makeNull();
                        size_t v172_ss = 0, v172_sls = 0, v172_scs = 0, v172_sars = 0;
                        save(v172_ss, v172_sls, v172_scs, v172_sars);
                        Value v172_elems[2];
                        Value lbl_prop = makeNull();
                        if (v172_ok) {
                            bool v173_ok = false;
                            Value v173_val = makeNull();
                            if (cursor_ + 5 <= input_.size() && input_.substr(cursor_, 5) == std::string_view("self.", 5)) {
                                size_t s = cursor_; (void)s;
                                for (size_t i = 0; i < 5; i++) advance_char();
                                v173_ok = true;
                                v173_val = makeString("self.");
                            } else {
                                fail("\"self.\"");
                            }
                            if (!v173_ok) { v172_ok = false; restore(v172_ss, v172_sls, v172_scs, v172_sars); }
                            else { v172_elems[0] = v173_val; }
                        }
                        if (v172_ok) {
                            auto v174_r = parse_Identifier();
                            bool v174_ok = v174_r.success;
                            Value v174_val = v174_r.value;
                            if (!v174_ok) { v172_ok = false; restore(v172_ss, v172_sls, v172_scs, v172_sars); }
                            else { v172_elems[1] = v174_val; }
                            if (v172_ok) lbl_prop = v172_elems[1];
                        }
                        if (v172_ok) {
                            size_t seq_start = arena_.head;
                            arena_.push_back(v172_elems[0]);
                            arena_.push_back(v172_elems[1]);
                            v172_val.type = ValueType::Array;
                            v172_val.data.arr.arena_start = seq_start;
                            v172_val.data.arr.length = static_cast<uint32_t>(2);
                        }
                        (void)lbl_prop;
                        bool v171_ok = v172_ok;
                        (void)v172_val;
                        Value v171_val = makeNull();
                        if (v171_ok) {
                            auto _text = [&]() -> std::string_view {
                                (void)0;
                                return text_at(v171_start, cursor_);
                            };
                            (void)_text;
                            auto& prop = lbl_prop;
                            (void)prop;
                            v171_val = [&]() -> Value {
                                return createArray({ makeString("SelfAccess"), prop });
                            }();
                            if (v171_val.line == 0) {
                                v171_val.line = static_cast<uint32_t>(v171_startLine);
                                v171_val.col = static_cast<uint32_t>(v171_startCol);
                                v171_val.length = static_cast<uint32_t>(cursor_ - v171_start);
                            }
                        }
                        if (v171_ok) { v170_ok = true; v170_val = v171_val; }
                    }
                }
                if (!v170_ok) {
                    restore(cc, cl, cco, car);
                    {
                        size_t v175_start = cursor_;
                        size_t v175_startLine = line_;
                        size_t v175_startCol = col_;
                        bool v176_ok = true;
                        Value v176_val = makeNull();
                        size_t v176_ss = 0, v176_sls = 0, v176_scs = 0, v176_sars = 0;
                        save(v176_ss, v176_sls, v176_scs, v176_sars);
                        Value v176_elems[3];
                        Value lbl_base = makeNull();
                        Value lbl_prop = makeNull();
                        if (v176_ok) {
                            auto v177_r = parse_Identifier();
                            bool v177_ok = v177_r.success;
                            Value v177_val = v177_r.value;
                            if (!v177_ok) { v176_ok = false; restore(v176_ss, v176_sls, v176_scs, v176_sars); }
                            else { v176_elems[0] = v177_val; }
                            if (v176_ok) lbl_base = v176_elems[0];
                        }
                        if (v176_ok) {
                            bool v178_ok = false;
                            Value v178_val = makeNull();
                            if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(".", 1)) {
                                size_t s = cursor_; (void)s;
                                for (size_t i = 0; i < 1; i++) advance_char();
                                v178_ok = true;
                                v178_val = makeString(".");
                            } else {
                                fail("\".\"");
                            }
                            if (!v178_ok) { v176_ok = false; restore(v176_ss, v176_sls, v176_scs, v176_sars); }
                            else { v176_elems[1] = v178_val; }
                        }
                        if (v176_ok) {
                            auto v179_r = parse_Identifier();
                            bool v179_ok = v179_r.success;
                            Value v179_val = v179_r.value;
                            if (!v179_ok) { v176_ok = false; restore(v176_ss, v176_sls, v176_scs, v176_sars); }
                            else { v176_elems[2] = v179_val; }
                            if (v176_ok) lbl_prop = v176_elems[2];
                        }
                        if (v176_ok) {
                            size_t seq_start = arena_.head;
                            arena_.push_back(v176_elems[0]);
                            arena_.push_back(v176_elems[1]);
                            arena_.push_back(v176_elems[2]);
                            v176_val.type = ValueType::Array;
                            v176_val.data.arr.arena_start = seq_start;
                            v176_val.data.arr.length = static_cast<uint32_t>(3);
                        }
                        (void)lbl_base;
                        (void)lbl_prop;
                        bool v175_ok = v176_ok;
                        (void)v176_val;
                        Value v175_val = makeNull();
                        if (v175_ok) {
                            auto _text = [&]() -> std::string_view {
                                (void)0;
                                return text_at(v175_start, cursor_);
                            };
                            (void)_text;
                            auto& base = lbl_base;
                            (void)base;
                            auto& prop = lbl_prop;
                            (void)prop;
                            v175_val = [&]() -> Value {
                                return createArray({ makeString("MemberAccess"), base, prop });
                            }();
                            if (v175_val.line == 0) {
                                v175_val.line = static_cast<uint32_t>(v175_startLine);
                                v175_val.col = static_cast<uint32_t>(v175_startCol);
                                v175_val.length = static_cast<uint32_t>(cursor_ - v175_start);
                            }
                        }
                        if (v175_ok) { v170_ok = true; v170_val = v175_val; }
                    }
                }
            }
            if (v170_ok) return {true, v170_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Member Access");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_Type() {
        uint64_t memo_key = (static_cast<uint64_t>(26ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 26ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v180_ok = true;
            Value v180_val = makeNull();
            size_t v180_ss = 0, v180_sls = 0, v180_scs = 0, v180_sars = 0;
            save(v180_ss, v180_sls, v180_scs, v180_sars);
            Value v180_elems[2];
            if (v180_ok) {
                auto v181_r = parse_Identifier();
                bool v181_ok = v181_r.success;
                Value v181_val = v181_r.value;
                if (!v181_ok) { v180_ok = false; restore(v180_ss, v180_sls, v180_scs, v180_sars); }
                else { v180_elems[0] = v181_val; }
            }
            if (v180_ok) {
                bool v182_ok = true;
                Value v182_val = makeNull();
                {
                    size_t rc = 0, rl = 0, rco = 0, rar = 0;
                    save(rc, rl, rco, rar);
                    bool v183_ok = false;
                    Value v183_val = makeNull();
                    {
                        size_t cc = 0, cl = 0, cco = 0, car = 0;
                        save(cc, cl, cco, car);
                        if (!v183_ok) {
                            {
                                bool v184_ok = false;
                                Value v184_val = makeNull();
                                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("?", 1)) {
                                    size_t s = cursor_; (void)s;
                                    for (size_t i = 0; i < 1; i++) advance_char();
                                    v184_ok = true;
                                    v184_val = makeString("?");
                                } else {
                                    fail("\"?\"");
                                }
                                if (v184_ok) { v183_ok = true; v183_val = v184_val; }
                            }
                        }
                        if (!v183_ok) {
                            restore(cc, cl, cco, car);
                            {
                                bool v185_ok = false;
                                Value v185_val = makeNull();
                                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("!", 1)) {
                                    size_t s = cursor_; (void)s;
                                    for (size_t i = 0; i < 1; i++) advance_char();
                                    v185_ok = true;
                                    v185_val = makeString("!");
                                } else {
                                    fail("\"!\"");
                                }
                                if (v185_ok) { v183_ok = true; v183_val = v185_val; }
                            }
                        }
                    }
                    if (v183_ok) { v182_val = v183_val; }
                    else { restore(rc, rl, rco, rar); }
                }
                if (!v182_ok) { v180_ok = false; restore(v180_ss, v180_sls, v180_scs, v180_sars); }
                else { v180_elems[1] = v182_val; }
            }
            if (v180_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v180_elems[0]);
                arena_.push_back(v180_elems[1]);
                v180_val.type = ValueType::Array;
                v180_val.data.arr.arena_start = seq_start;
                v180_val.data.arr.length = static_cast<uint32_t>(2);
            }
            if (v180_ok) return {true, v180_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Type");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_Identifier() {
        uint64_t memo_key = (static_cast<uint64_t>(27ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 27ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v186_ok = false;
            Value v186_val = makeNull();
            {
                size_t ts = cursor_;
                bool v187_ok = true;
                Value v187_val = makeNull();
                size_t v187_ss = 0, v187_sls = 0, v187_scs = 0, v187_sars = 0;
                save(v187_ss, v187_sls, v187_scs, v187_sars);
                Value v187_elems[2];
                if (v187_ok) {
                    bool v188_ok = false;
                    Value v188_val = makeNull();
                    if (!at_end()) {
                        unsigned char v188_ch = static_cast<unsigned char>(peek());
                        bool match = false;
                        switch (v188_ch) {
                            case 65:
                            case 66:
                            case 67:
                            case 68:
                            case 69:
                            case 70:
                            case 71:
                            case 72:
                            case 73:
                            case 74:
                            case 75:
                            case 76:
                            case 77:
                            case 78:
                            case 79:
                            case 80:
                            case 81:
                            case 82:
                            case 83:
                            case 84:
                            case 85:
                            case 86:
                            case 87:
                            case 88:
                            case 89:
                            case 90:
                            case 95:
                            case 97:
                            case 98:
                            case 99:
                            case 100:
                            case 101:
                            case 102:
                            case 103:
                            case 104:
                            case 105:
                            case 106:
                            case 107:
                            case 108:
                            case 109:
                            case 110:
                            case 111:
                            case 112:
                            case 113:
                            case 114:
                            case 115:
                            case 116:
                            case 117:
                            case 118:
                            case 119:
                            case 120:
                            case 121:
                            case 122:
                                match = true; break;
                        }
                        if (match) {
                            size_t start_c = cursor_; (void)start_c;
                            advance_char();
                            v188_ok = true;
                            v188_val = makeString(text_at(start_c, cursor_));
                        } else {
                            fail("[a-zA-Z_]");
                        }
                    } else {
                        fail("[a-zA-Z_]");
                    }
                    if (!v188_ok) { v187_ok = false; restore(v187_ss, v187_sls, v187_scs, v187_sars); }
                    else { v187_elems[0] = v188_val; }
                }
                if (v187_ok) {
                    bool v189_ok = true;
                    Value v189_val = makeNull();
                    {
                        size_t rep_start = arena_.head;
                        size_t rep_count = 0;
                        for (;;) {
                            size_t rc = 0, rl = 0, rco = 0, rar = 0;
                            save(rc, rl, rco, rar);
                            bool v190_ok = false;
                            Value v190_val = makeNull();
                            if (!at_end()) {
                                unsigned char v190_ch = static_cast<unsigned char>(peek());
                                bool match = false;
                                switch (v190_ch) {
                                    case 48:
                                    case 49:
                                    case 50:
                                    case 51:
                                    case 52:
                                    case 53:
                                    case 54:
                                    case 55:
                                    case 56:
                                    case 57:
                                    case 65:
                                    case 66:
                                    case 67:
                                    case 68:
                                    case 69:
                                    case 70:
                                    case 71:
                                    case 72:
                                    case 73:
                                    case 74:
                                    case 75:
                                    case 76:
                                    case 77:
                                    case 78:
                                    case 79:
                                    case 80:
                                    case 81:
                                    case 82:
                                    case 83:
                                    case 84:
                                    case 85:
                                    case 86:
                                    case 87:
                                    case 88:
                                    case 89:
                                    case 90:
                                    case 95:
                                    case 97:
                                    case 98:
                                    case 99:
                                    case 100:
                                    case 101:
                                    case 102:
                                    case 103:
                                    case 104:
                                    case 105:
                                    case 106:
                                    case 107:
                                    case 108:
                                    case 109:
                                    case 110:
                                    case 111:
                                    case 112:
                                    case 113:
                                    case 114:
                                    case 115:
                                    case 116:
                                    case 117:
                                    case 118:
                                    case 119:
                                    case 120:
                                    case 121:
                                    case 122:
                                        match = true; break;
                                }
                                if (match) {
                                    size_t start_c = cursor_; (void)start_c;
                                    advance_char();
                                    v190_ok = true;
                                    v190_val = makeString(text_at(start_c, cursor_));
                                } else {
                                    fail("[a-zA-Z0-9_]");
                                }
                            } else {
                                fail("[a-zA-Z0-9_]");
                            }
                            if (!v190_ok) { restore(rc, rl, rco, rar); break; }
                            if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                            arena_.push_back(v190_val);
                            rep_count++;
                        }
                        v189_val.type = ValueType::Array;
                        v189_val.data.arr.arena_start = rep_start;
                        v189_val.data.arr.length = static_cast<uint32_t>(rep_count);
                    }
                    if (!v189_ok) { v187_ok = false; restore(v187_ss, v187_sls, v187_scs, v187_sars); }
                    else { v187_elems[1] = v189_val; }
                }
                if (v187_ok) {
                    size_t seq_start = arena_.head;
                    arena_.push_back(v187_elems[0]);
                    arena_.push_back(v187_elems[1]);
                    v187_val.type = ValueType::Array;
                    v187_val.data.arr.arena_start = seq_start;
                    v187_val.data.arr.length = static_cast<uint32_t>(2);
                }
                if (v187_ok) {
                    (void)v187_val;
                    v186_ok = true;
                    v186_val = makeString(text_at(ts, cursor_));
                }
            }
            if (v186_ok) return {true, v186_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Identifier");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_Operator() {
        uint64_t memo_key = (static_cast<uint64_t>(28ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 28ULL) & MEMO_MASK;
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        bool v191_ok = false;
        Value v191_val = makeNull();
        {
            size_t ts = cursor_;
            bool v192_ok = false;
            Value v192_val = makeNull();
            {
                size_t cc = 0, cl = 0, cco = 0, car = 0;
                save(cc, cl, cco, car);
                if (!v192_ok) {
                    {
                        bool v193_ok = false;
                        Value v193_val = makeNull();
                        if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("+", 1)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 1; i++) advance_char();
                            v193_ok = true;
                            v193_val = makeString("+");
                        } else {
                            fail("\"+\"");
                        }
                        if (v193_ok) { v192_ok = true; v192_val = v193_val; }
                    }
                }
                if (!v192_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v194_ok = false;
                        Value v194_val = makeNull();
                        if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("-", 1)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 1; i++) advance_char();
                            v194_ok = true;
                            v194_val = makeString("-");
                        } else {
                            fail("\"-\"");
                        }
                        if (v194_ok) { v192_ok = true; v192_val = v194_val; }
                    }
                }
                if (!v192_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v195_ok = false;
                        Value v195_val = makeNull();
                        if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("*", 1)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 1; i++) advance_char();
                            v195_ok = true;
                            v195_val = makeString("*");
                        } else {
                            fail("\"*\"");
                        }
                        if (v195_ok) { v192_ok = true; v192_val = v195_val; }
                    }
                }
                if (!v192_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v196_ok = false;
                        Value v196_val = makeNull();
                        if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("/", 1)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 1; i++) advance_char();
                            v196_ok = true;
                            v196_val = makeString("/");
                        } else {
                            fail("\"/\"");
                        }
                        if (v196_ok) { v192_ok = true; v192_val = v196_val; }
                    }
                }
                if (!v192_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v197_ok = false;
                        Value v197_val = makeNull();
                        if (cursor_ + 2 <= input_.size() && input_.substr(cursor_, 2) == std::string_view("==", 2)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 2; i++) advance_char();
                            v197_ok = true;
                            v197_val = makeString("==");
                        } else {
                            fail("\"==\"");
                        }
                        if (v197_ok) { v192_ok = true; v192_val = v197_val; }
                    }
                }
                if (!v192_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v198_ok = false;
                        Value v198_val = makeNull();
                        if (cursor_ + 2 <= input_.size() && input_.substr(cursor_, 2) == std::string_view("!=", 2)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 2; i++) advance_char();
                            v198_ok = true;
                            v198_val = makeString("!=");
                        } else {
                            fail("\"!=\"");
                        }
                        if (v198_ok) { v192_ok = true; v192_val = v198_val; }
                    }
                }
                if (!v192_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v199_ok = false;
                        Value v199_val = makeNull();
                        if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(">", 1)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 1; i++) advance_char();
                            v199_ok = true;
                            v199_val = makeString(">");
                        } else {
                            fail("\">\"");
                        }
                        if (v199_ok) { v192_ok = true; v192_val = v199_val; }
                    }
                }
                if (!v192_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v200_ok = false;
                        Value v200_val = makeNull();
                        if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("<", 1)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 1; i++) advance_char();
                            v200_ok = true;
                            v200_val = makeString("<");
                        } else {
                            fail("\"<\"");
                        }
                        if (v200_ok) { v192_ok = true; v192_val = v200_val; }
                    }
                }
                if (!v192_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v201_ok = false;
                        Value v201_val = makeNull();
                        if (cursor_ + 2 <= input_.size() && input_.substr(cursor_, 2) == std::string_view(">=", 2)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 2; i++) advance_char();
                            v201_ok = true;
                            v201_val = makeString(">=");
                        } else {
                            fail("\">=\"");
                        }
                        if (v201_ok) { v192_ok = true; v192_val = v201_val; }
                    }
                }
                if (!v192_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v202_ok = false;
                        Value v202_val = makeNull();
                        if (cursor_ + 2 <= input_.size() && input_.substr(cursor_, 2) == std::string_view("<=", 2)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 2; i++) advance_char();
                            v202_ok = true;
                            v202_val = makeString("<=");
                        } else {
                            fail("\"<=\"");
                        }
                        if (v202_ok) { v192_ok = true; v192_val = v202_val; }
                    }
                }
            }
            if (v192_ok) {
                (void)v192_val;
                v191_ok = true;
                v191_val = makeString(text_at(ts, cursor_));
            }
        }
        if (v191_ok) {
            return {true, v191_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        } else {
            fail("Operator");
            restore(sc, sl, sco, sar);
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
    }
    
    Result parse_Literal() {
        uint64_t memo_key = (static_cast<uint64_t>(29ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 29ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            bool v203_ok = false;
            Value v203_val = makeNull();
            {
                size_t cc = 0, cl = 0, cco = 0, car = 0;
                save(cc, cl, cco, car);
                if (!v203_ok) {
                    {
                        auto v204_r = parse_StringLiteral();
                        bool v204_ok = v204_r.success;
                        Value v204_val = v204_r.value;
                        if (v204_ok) { v203_ok = true; v203_val = v204_val; }
                    }
                }
                if (!v203_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v205_r = parse_FloatLiteral();
                        bool v205_ok = v205_r.success;
                        Value v205_val = v205_r.value;
                        if (v205_ok) { v203_ok = true; v203_val = v205_val; }
                    }
                }
                if (!v203_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v206_r = parse_IntLiteral();
                        bool v206_ok = v206_r.success;
                        Value v206_val = v206_r.value;
                        if (v206_ok) { v203_ok = true; v203_val = v206_val; }
                    }
                }
                if (!v203_ok) {
                    restore(cc, cl, cco, car);
                    {
                        auto v207_r = parse_BoolLiteral();
                        bool v207_ok = v207_r.success;
                        Value v207_val = v207_r.value;
                        if (v207_ok) { v203_ok = true; v203_val = v207_val; }
                    }
                }
            }
            if (v203_ok) return {true, v203_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Literal");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_StringLiteral() {
        uint64_t memo_key = (static_cast<uint64_t>(30ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 30ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v208_start = cursor_;
            size_t v208_startLine = line_;
            size_t v208_startCol = col_;
            bool v209_ok = true;
            Value v209_val = makeNull();
            size_t v209_ss = 0, v209_sls = 0, v209_scs = 0, v209_sars = 0;
            save(v209_ss, v209_sls, v209_scs, v209_sars);
            Value v209_elems[3];
            if (v209_ok) {
                bool v210_ok = false;
                Value v210_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("\"", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v210_ok = true;
                    v210_val = makeString("\"");
                } else {
                    fail("\"\"\"");
                }
                if (!v210_ok) { v209_ok = false; restore(v209_ss, v209_sls, v209_scs, v209_sars); }
                else { v209_elems[0] = v210_val; }
            }
            if (v209_ok) {
                bool v211_ok = false;
                Value v211_val = makeNull();
                {
                    size_t ts = cursor_;
                    bool v212_ok = true;
                    Value v212_val = makeNull();
                    {
                        size_t rep_start = arena_.head;
                        size_t rep_count = 0;
                        for (;;) {
                            size_t rc = 0, rl = 0, rco = 0, rar = 0;
                            save(rc, rl, rco, rar);
                            bool v213_ok = false;
                            Value v213_val = makeNull();
                            if (!at_end()) {
                                unsigned char v213_ch = static_cast<unsigned char>(peek());
                                bool match = false;
                                switch (v213_ch) {
                                    case 34:
                                        match = true; break;
                                }
                                if (!match) {
                                    size_t start_c = cursor_; (void)start_c;
                                    advance_char();
                                    v213_ok = true;
                                    v213_val = makeString(text_at(start_c, cursor_));
                                } else {
                                    fail("[^\\\"]");
                                }
                            } else {
                                fail("[^\\\"]");
                            }
                            if (!v213_ok) { restore(rc, rl, rco, rar); break; }
                            if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                            arena_.push_back(v213_val);
                            rep_count++;
                        }
                        v212_val.type = ValueType::Array;
                        v212_val.data.arr.arena_start = rep_start;
                        v212_val.data.arr.length = static_cast<uint32_t>(rep_count);
                    }
                    if (v212_ok) {
                        (void)v212_val;
                        v211_ok = true;
                        v211_val = makeString(text_at(ts, cursor_));
                    }
                }
                if (!v211_ok) { v209_ok = false; restore(v209_ss, v209_sls, v209_scs, v209_sars); }
                else { v209_elems[1] = v211_val; }
            }
            if (v209_ok) {
                bool v214_ok = false;
                Value v214_val = makeNull();
                if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view("\"", 1)) {
                    size_t s = cursor_; (void)s;
                    for (size_t i = 0; i < 1; i++) advance_char();
                    v214_ok = true;
                    v214_val = makeString("\"");
                } else {
                    fail("\"\"\"");
                }
                if (!v214_ok) { v209_ok = false; restore(v209_ss, v209_sls, v209_scs, v209_sars); }
                else { v209_elems[2] = v214_val; }
            }
            if (v209_ok) {
                size_t seq_start = arena_.head;
                arena_.push_back(v209_elems[0]);
                arena_.push_back(v209_elems[1]);
                arena_.push_back(v209_elems[2]);
                v209_val.type = ValueType::Array;
                v209_val.data.arr.arena_start = seq_start;
                v209_val.data.arr.length = static_cast<uint32_t>(3);
            }
            bool v208_ok = v209_ok;
            (void)v209_val;
            Value v208_val = makeNull();
            if (v208_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v208_start, cursor_);
                };
                (void)_text;
                v208_val = [&]() -> Value {
                    return createArray({ makeString("String"), _text });
                }();
                if (v208_val.line == 0) {
                    v208_val.line = static_cast<uint32_t>(v208_startLine);
                    v208_val.col = static_cast<uint32_t>(v208_startCol);
                    v208_val.length = static_cast<uint32_t>(cursor_ - v208_start);
                }
            }
            if (v208_ok) return {true, v208_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("String");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_FloatLiteral() {
        uint64_t memo_key = (static_cast<uint64_t>(31ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 31ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v215_start = cursor_;
            size_t v215_startLine = line_;
            size_t v215_startCol = col_;
            bool v216_ok = false;
            Value v216_val = makeNull();
            {
                size_t ts = cursor_;
                bool v217_ok = true;
                Value v217_val = makeNull();
                size_t v217_ss = 0, v217_sls = 0, v217_scs = 0, v217_sars = 0;
                save(v217_ss, v217_sls, v217_scs, v217_sars);
                Value v217_elems[3];
                if (v217_ok) {
                    bool v218_ok = false;
                    Value v218_val = makeNull();
                    {
                        size_t rep_start = arena_.head;
                        size_t rep_count = 0;
                        bool v219_ok = false;
                        Value v219_val = makeNull();
                        if (!at_end()) {
                            unsigned char v219_ch = static_cast<unsigned char>(peek());
                            bool match = false;
                            switch (v219_ch) {
                                case 48:
                                case 49:
                                case 50:
                                case 51:
                                case 52:
                                case 53:
                                case 54:
                                case 55:
                                case 56:
                                case 57:
                                    match = true; break;
                            }
                            if (match) {
                                size_t start_c = cursor_; (void)start_c;
                                advance_char();
                                v219_ok = true;
                                v219_val = makeString(text_at(start_c, cursor_));
                            } else {
                                fail("[0-9]");
                            }
                        } else {
                            fail("[0-9]");
                        }
                        if (v219_ok) {
                            arena_.push_back(v219_val);
                            rep_count++;
                            for (;;) {
                                size_t rc = 0, rl = 0, rco = 0, rar = 0;
                                save(rc, rl, rco, rar);
                                bool v220_ok = false;
                                Value v220_val = makeNull();
                                if (!at_end()) {
                                    unsigned char v220_ch = static_cast<unsigned char>(peek());
                                    bool match = false;
                                    switch (v220_ch) {
                                        case 48:
                                        case 49:
                                        case 50:
                                        case 51:
                                        case 52:
                                        case 53:
                                        case 54:
                                        case 55:
                                        case 56:
                                        case 57:
                                            match = true; break;
                                    }
                                    if (match) {
                                        size_t start_c = cursor_; (void)start_c;
                                        advance_char();
                                        v220_ok = true;
                                        v220_val = makeString(text_at(start_c, cursor_));
                                    } else {
                                        fail("[0-9]");
                                    }
                                } else {
                                    fail("[0-9]");
                                }
                                if (!v220_ok) { restore(rc, rl, rco, rar); break; }
                                if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                                arena_.push_back(v220_val);
                                rep_count++;
                            }
                            v218_ok = true;
                            v218_val.type = ValueType::Array;
                            v218_val.data.arr.arena_start = rep_start;
                            v218_val.data.arr.length = static_cast<uint32_t>(rep_count);
                        }
                    }
                    if (!v218_ok) { v217_ok = false; restore(v217_ss, v217_sls, v217_scs, v217_sars); }
                    else { v217_elems[0] = v218_val; }
                }
                if (v217_ok) {
                    bool v221_ok = false;
                    Value v221_val = makeNull();
                    if (cursor_ + 1 <= input_.size() && input_.substr(cursor_, 1) == std::string_view(".", 1)) {
                        size_t s = cursor_; (void)s;
                        for (size_t i = 0; i < 1; i++) advance_char();
                        v221_ok = true;
                        v221_val = makeString(".");
                    } else {
                        fail("\".\"");
                    }
                    if (!v221_ok) { v217_ok = false; restore(v217_ss, v217_sls, v217_scs, v217_sars); }
                    else { v217_elems[1] = v221_val; }
                }
                if (v217_ok) {
                    bool v222_ok = false;
                    Value v222_val = makeNull();
                    {
                        size_t rep_start = arena_.head;
                        size_t rep_count = 0;
                        bool v223_ok = false;
                        Value v223_val = makeNull();
                        if (!at_end()) {
                            unsigned char v223_ch = static_cast<unsigned char>(peek());
                            bool match = false;
                            switch (v223_ch) {
                                case 48:
                                case 49:
                                case 50:
                                case 51:
                                case 52:
                                case 53:
                                case 54:
                                case 55:
                                case 56:
                                case 57:
                                    match = true; break;
                            }
                            if (match) {
                                size_t start_c = cursor_; (void)start_c;
                                advance_char();
                                v223_ok = true;
                                v223_val = makeString(text_at(start_c, cursor_));
                            } else {
                                fail("[0-9]");
                            }
                        } else {
                            fail("[0-9]");
                        }
                        if (v223_ok) {
                            arena_.push_back(v223_val);
                            rep_count++;
                            for (;;) {
                                size_t rc = 0, rl = 0, rco = 0, rar = 0;
                                save(rc, rl, rco, rar);
                                bool v224_ok = false;
                                Value v224_val = makeNull();
                                if (!at_end()) {
                                    unsigned char v224_ch = static_cast<unsigned char>(peek());
                                    bool match = false;
                                    switch (v224_ch) {
                                        case 48:
                                        case 49:
                                        case 50:
                                        case 51:
                                        case 52:
                                        case 53:
                                        case 54:
                                        case 55:
                                        case 56:
                                        case 57:
                                            match = true; break;
                                    }
                                    if (match) {
                                        size_t start_c = cursor_; (void)start_c;
                                        advance_char();
                                        v224_ok = true;
                                        v224_val = makeString(text_at(start_c, cursor_));
                                    } else {
                                        fail("[0-9]");
                                    }
                                } else {
                                    fail("[0-9]");
                                }
                                if (!v224_ok) { restore(rc, rl, rco, rar); break; }
                                if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                                arena_.push_back(v224_val);
                                rep_count++;
                            }
                            v222_ok = true;
                            v222_val.type = ValueType::Array;
                            v222_val.data.arr.arena_start = rep_start;
                            v222_val.data.arr.length = static_cast<uint32_t>(rep_count);
                        }
                    }
                    if (!v222_ok) { v217_ok = false; restore(v217_ss, v217_sls, v217_scs, v217_sars); }
                    else { v217_elems[2] = v222_val; }
                }
                if (v217_ok) {
                    size_t seq_start = arena_.head;
                    arena_.push_back(v217_elems[0]);
                    arena_.push_back(v217_elems[1]);
                    arena_.push_back(v217_elems[2]);
                    v217_val.type = ValueType::Array;
                    v217_val.data.arr.arena_start = seq_start;
                    v217_val.data.arr.length = static_cast<uint32_t>(3);
                }
                if (v217_ok) {
                    (void)v217_val;
                    v216_ok = true;
                    v216_val = makeString(text_at(ts, cursor_));
                }
            }
            bool v215_ok = v216_ok;
            (void)v216_val;
            Value v215_val = makeNull();
            if (v215_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v215_start, cursor_);
                };
                (void)_text;
                v215_val = [&]() -> Value {
                    return createArray({ makeString("Float"), _text });
                }();
                if (v215_val.line == 0) {
                    v215_val.line = static_cast<uint32_t>(v215_startLine);
                    v215_val.col = static_cast<uint32_t>(v215_startCol);
                    v215_val.length = static_cast<uint32_t>(cursor_ - v215_start);
                }
            }
            if (v215_ok) return {true, v215_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Float");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_IntLiteral() {
        uint64_t memo_key = (static_cast<uint64_t>(32ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 32ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v225_start = cursor_;
            size_t v225_startLine = line_;
            size_t v225_startCol = col_;
            bool v226_ok = false;
            Value v226_val = makeNull();
            {
                size_t ts = cursor_;
                bool v227_ok = false;
                Value v227_val = makeNull();
                {
                    size_t rep_start = arena_.head;
                    size_t rep_count = 0;
                    bool v228_ok = false;
                    Value v228_val = makeNull();
                    if (!at_end()) {
                        unsigned char v228_ch = static_cast<unsigned char>(peek());
                        bool match = false;
                        switch (v228_ch) {
                            case 48:
                            case 49:
                            case 50:
                            case 51:
                            case 52:
                            case 53:
                            case 54:
                            case 55:
                            case 56:
                            case 57:
                                match = true; break;
                        }
                        if (match) {
                            size_t start_c = cursor_; (void)start_c;
                            advance_char();
                            v228_ok = true;
                            v228_val = makeString(text_at(start_c, cursor_));
                        } else {
                            fail("[0-9]");
                        }
                    } else {
                        fail("[0-9]");
                    }
                    if (v228_ok) {
                        arena_.push_back(v228_val);
                        rep_count++;
                        for (;;) {
                            size_t rc = 0, rl = 0, rco = 0, rar = 0;
                            save(rc, rl, rco, rar);
                            bool v229_ok = false;
                            Value v229_val = makeNull();
                            if (!at_end()) {
                                unsigned char v229_ch = static_cast<unsigned char>(peek());
                                bool match = false;
                                switch (v229_ch) {
                                    case 48:
                                    case 49:
                                    case 50:
                                    case 51:
                                    case 52:
                                    case 53:
                                    case 54:
                                    case 55:
                                    case 56:
                                    case 57:
                                        match = true; break;
                                }
                                if (match) {
                                    size_t start_c = cursor_; (void)start_c;
                                    advance_char();
                                    v229_ok = true;
                                    v229_val = makeString(text_at(start_c, cursor_));
                                } else {
                                    fail("[0-9]");
                                }
                            } else {
                                fail("[0-9]");
                            }
                            if (!v229_ok) { restore(rc, rl, rco, rar); break; }
                            if (cursor_ == rc) { restore(rc, rl, rco, rar); break; } // Prevent loop & leak
                            arena_.push_back(v229_val);
                            rep_count++;
                        }
                        v227_ok = true;
                        v227_val.type = ValueType::Array;
                        v227_val.data.arr.arena_start = rep_start;
                        v227_val.data.arr.length = static_cast<uint32_t>(rep_count);
                    }
                }
                if (v227_ok) {
                    (void)v227_val;
                    v226_ok = true;
                    v226_val = makeString(text_at(ts, cursor_));
                }
            }
            bool v225_ok = v226_ok;
            (void)v226_val;
            Value v225_val = makeNull();
            if (v225_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v225_start, cursor_);
                };
                (void)_text;
                v225_val = [&]() -> Value {
                    return createArray({ makeString("Int"), _text });
                }();
                if (v225_val.line == 0) {
                    v225_val.line = static_cast<uint32_t>(v225_startLine);
                    v225_val.col = static_cast<uint32_t>(v225_startCol);
                    v225_val.length = static_cast<uint32_t>(cursor_ - v225_start);
                }
            }
            if (v225_ok) return {true, v225_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Integer");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
    Result parse_BoolLiteral() {
        uint64_t memo_key = (static_cast<uint64_t>(33ULL) << 48) | (static_cast<uint64_t>(cursor_) & 0xFFFFFFFFFFFFULL);
        size_t memo_idx = ((cursor_ * 0x9E3779B9ULL) ^ 33ULL) & MEMO_MASK;
        if (memo_cache_[memo_idx].generation == parse_generation_ && memo_cache_[memo_idx].key == memo_key) {
            if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key) return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            auto& cached = memo_cache_[memo_idx].result;
            if (cached.success) {
                cursor_ = cached.end_cursor; line_ = cached.end_line; col_ = cached.end_col;
                return cached;
            }
            return cached;
        }
        size_t sc = 0, sl = 0, sco = 0, sar = 0;
        save(sc, sl, sco, sar);
        if (memo_cache_[memo_idx].active && memo_cache_[memo_idx].key == memo_key && memo_cache_[memo_idx].generation == parse_generation_) {
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        }
        if (current_depth_++ > MAX_DEPTH) { current_depth_--; fail("Maximum parse depth exceeded"); return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)}; }
        memo_cache_[memo_idx].key = memo_key;
        memo_cache_[memo_idx].generation = parse_generation_;
        memo_cache_[memo_idx].active = true;
        auto eval_body = [&]() -> Result {
            size_t v230_start = cursor_;
            size_t v230_startLine = line_;
            size_t v230_startCol = col_;
            bool v231_ok = false;
            Value v231_val = makeNull();
            {
                size_t cc = 0, cl = 0, cco = 0, car = 0;
                save(cc, cl, cco, car);
                if (!v231_ok) {
                    {
                        bool v232_ok = false;
                        Value v232_val = makeNull();
                        if (cursor_ + 4 <= input_.size() && input_.substr(cursor_, 4) == std::string_view("true", 4)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 4; i++) advance_char();
                            v232_ok = true;
                            v232_val = makeString("true");
                        } else {
                            fail("\"true\"");
                        }
                        if (v232_ok) { v231_ok = true; v231_val = v232_val; }
                    }
                }
                if (!v231_ok) {
                    restore(cc, cl, cco, car);
                    {
                        bool v233_ok = false;
                        Value v233_val = makeNull();
                        if (cursor_ + 5 <= input_.size() && input_.substr(cursor_, 5) == std::string_view("false", 5)) {
                            size_t s = cursor_; (void)s;
                            for (size_t i = 0; i < 5; i++) advance_char();
                            v233_ok = true;
                            v233_val = makeString("false");
                        } else {
                            fail("\"false\"");
                        }
                        if (v233_ok) { v231_ok = true; v231_val = v233_val; }
                    }
                }
            }
            bool v230_ok = v231_ok;
            (void)v231_val;
            Value v230_val = makeNull();
            if (v230_ok) {
                auto _text = [&]() -> std::string_view {
                    (void)0;
                    return text_at(v230_start, cursor_);
                };
                (void)_text;
                v230_val = [&]() -> Value {
                    return createArray({ makeString("Bool"), _text });
                }();
                if (v230_val.line == 0) {
                    v230_val.line = static_cast<uint32_t>(v230_startLine);
                    v230_val.col = static_cast<uint32_t>(v230_startCol);
                    v230_val.length = static_cast<uint32_t>(cursor_ - v230_start);
                }
            }
            if (v230_ok) return {true, v230_val, cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
            return {false, makeNull(), cursor_, static_cast<uint32_t>(line_), static_cast<uint32_t>(col_)};
        };
        Result rule_res = eval_body();
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            for (;;) {
                cursor_ = sc; line_ = sl; col_ = sco;
                Result next_res = eval_body();
                if (!next_res.success || next_res.end_cursor <= rule_res.end_cursor) {
                    cursor_ = rule_res.end_cursor; line_ = rule_res.end_line; col_ = rule_res.end_col;
                    break;
                }
                rule_res = next_res;
                memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
            }
        } else {
            fail("Boolean");
            restore(sc, sl, sco, sar);
        }
        memo_cache_[memo_idx].active = false;
        current_depth_--;
        if (rule_res.success) {
            memo_cache_[memo_idx] = {memo_key, parse_generation_, false, rule_res};
        }
        return rule_res;
    }
    
};

} // namespace EvoParser
