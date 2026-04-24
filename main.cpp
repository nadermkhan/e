#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <filesystem>
#include <unordered_map>
#include <memory>
#include <system_error>
#include <cstdlib>

// === LLVM Headers ===
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/TargetParser/Host.h>
#include <llvm/MC/TargetRegistry.h>
#include <llvm/Target/TargetMachine.h>
#include <llvm/Target/TargetOptions.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/ExecutionEngine/Orc/ExecutionUtils.h>

#include <ElegantParser.hpp>

namespace Elegant {

// FEATURE 1: Strong Typing Foundation
struct TypedValue {
    llvm::Value* val;
    std::string type;
};

struct StructInfo {
    llvm::StructType* type;
    std::unordered_map<std::string, unsigned> fieldIndices;
    std::unordered_map<std::string, std::string> fieldTypesString;
    std::vector<llvm::Type*> fieldTypes;
    bool isReferenceType;

    // FEATURE: Polymorphism — inheritance + Virtual Method Table (V-Table).
    // Reference-type classes carry a hidden VTable pointer at slot 0 of their
    // heap layout; method calls on classes route through the VTable so
    // overrides in subclasses are dispatched dynamically at runtime.
    std::string superclass;
    EvoParser::Value astMembers;
    bool resolved = false;
    llvm::StructType* vtableType = nullptr;
    llvm::GlobalVariable* vtableGlobal = nullptr;
    std::vector<std::string> vtableMethods;                 // vtable slot -> mangled fn name
    std::unordered_map<std::string, unsigned> vtableIndices; // unmangled method name -> slot
};

struct VarInfo {
    llvm::AllocaInst* alloca;
    std::string typeName;
};

// FEATURE 2: Function Symbol Table
struct FuncSig {
    std::string retType;
    std::vector<std::string> argTypes;
    bool isVarArg = false;
};

class LLVMCompiler {
    EvoParser::ParseContext& ctx_;
    std::unique_ptr<llvm::LLVMContext> context_;
    std::unique_ptr<llvm::Module> module_;
    std::unique_ptr<llvm::IRBuilder<>> builder_;

    // FEATURE 3: Lexical Scope Stack
    std::vector<std::unordered_map<std::string, VarInfo>> scopes_;
    std::unordered_map<std::string, StructInfo> structs_;
    std::unordered_map<std::string, FuncSig> functions_;

public:
    LLVMCompiler(EvoParser::ParseContext& ctx, const std::string& moduleName)
        : ctx_(ctx) {
        context_ = std::make_unique<llvm::LLVMContext>();
        module_ = std::make_unique<llvm::Module>(moduleName, *context_);
        builder_ = std::make_unique<llvm::IRBuilder<>>(*context_);
    }

    // --- SCOPE MANAGEMENT ---
    void pushScope() { scopes_.push_back({}); }

    // FEATURE: ARC — release reference-type class variables on scope exit.
    // Note: this releases every class-typed variable in the current scope,
    // including function parameters. Callers are therefore expected to have
    // retained objects they pass in (assignments retain the RHS). Releasing
    // on scope exit balances the initial ref_count = 1 set at allocation
    // and subsequent retains performed by assignments.
    //
    // If the current basic block was already terminated (e.g. the body ended
    // with an explicit `return`), we temporarily re-point the builder just
    // before the terminator so releases run before control leaves the block.
    void popScope() {
        llvm::Function* releaseF = module_->getFunction("elegant_release");
        if (releaseF) {
            // First check whether this scope contains anything we need to
            // release; skip all builder manipulation otherwise so we stay a
            // zero-cost no-op for Int/String/Array-only scopes.
            bool hasRefs = false;
            for (auto& [name, var] : scopes_.back()) {
                auto it = structs_.find(var.typeName);
                if (it != structs_.end() && it->second.isReferenceType) { hasRefs = true; break; }
            }
            if (hasRefs) {
                llvm::BasicBlock* insertBB = builder_->GetInsertBlock();
                if (insertBB) {
                    llvm::Instruction* term = insertBB->getTerminatorOrNull();
                    llvm::BasicBlock*         savedBB = insertBB;
                    llvm::BasicBlock::iterator savedIt = builder_->GetInsertPoint();
                    if (term) builder_->SetInsertPoint(term);

                    llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
                    for (auto& [name, var] : scopes_.back()) {
                        auto it = structs_.find(var.typeName);
                        if (it == structs_.end() || !it->second.isReferenceType) continue;
                        llvm::Value* objPtr = builder_->CreateLoad(ptrTy, var.alloca);
                        builder_->CreateCall(releaseF, {objPtr});
                    }

                    if (term) builder_->SetInsertPoint(savedBB, savedIt);
                }
            }
        }
        scopes_.pop_back();
    }

    VarInfo* lookupVar(const std::string& name) {
        for (auto it = scopes_.rbegin(); it != scopes_.rend(); ++it) {
            auto found = it->find(name);
            if (found != it->end()) return &found->second;
        }
        return nullptr;
    }
    void defineVar(const std::string& name, VarInfo info) {
        scopes_.back()[name] = info;
    }
    // -------------------------

    llvm::Function* getMalloc() {
        if (auto* M = module_->getFunction("malloc")) return M;
        auto* FT = llvm::FunctionType::get(llvm::PointerType::getUnqual(*context_), {llvm::Type::getInt64Ty(*context_)}, false);
        return llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "malloc", module_.get());
    }

    llvm::Function* getFree() {
        if (auto* F = module_->getFunction("free")) return F;
        auto* FT = llvm::FunctionType::get(llvm::Type::getVoidTy(*context_), {llvm::PointerType::getUnqual(*context_)}, false);
        return llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "free", module_.get());
    }

    llvm::Function* getPrintf() {
        if (auto* P = module_->getFunction("printf")) return P;
        auto* FT = llvm::FunctionType::get(llvm::Type::getInt32Ty(*context_), {llvm::PointerType::getUnqual(*context_)}, true);
        return llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "printf", module_.get());
    }

    llvm::Function* getExit() {
        if (auto* E = module_->getFunction("exit")) return E;
        auto* FT = llvm::FunctionType::get(llvm::Type::getVoidTy(*context_), {llvm::Type::getInt32Ty(*context_)}, false);
        return llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "exit", module_.get());
    }

    // FEATURE: The Safe Panic Trigger. Called automatically when a user tries
    // to force-unwrap a `nil` Optional. Instead of a hardware segfault the
    // program halts with a readable diagnostic.
    llvm::Function* getPanic() {
        if (auto* F = module_->getFunction("elegant_panic")) return F;
        auto* FT = llvm::FunctionType::get(llvm::Type::getVoidTy(*context_), false);
        auto* F = llvm::Function::Create(FT, llvm::Function::InternalLinkage, "elegant_panic", module_.get());
        auto* BB = llvm::BasicBlock::Create(*context_, "entry", F);
        llvm::IRBuilder<> b(BB);
        llvm::Value* msg = b.CreateGlobalString(
            "\n\033[31m\xF0\x9F\x9A\xA8 Fatal Error:\033[0m Unexpectedly found nil while unwrapping an Optional value.\n",
            "elegant_panic_msg");
        b.CreateCall(getPrintf(), {msg});
        b.CreateCall(getExit(), {llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), 1)});
        b.CreateUnreachable();
        return F;
    }

    // FEATURE: ARC — emit the native retain/release runtime as LLVM IR.
    // Every reference-type class stores a hidden header at the top of its
    // heap layout: slot 0 is a VTable pointer (for Polymorphism) and slot 1
    // is the ref_count. retain/release GEP into slot 1 to bump/drop the
    // reference counter; release frees the whole allocation when it hits 0.
    void buildARCFunctions() {
        llvm::Type* voidTy = llvm::Type::getVoidTy(*context_);
        llvm::Type* ptrTy  = llvm::PointerType::getUnqual(*context_);
        llvm::Type* i32Ty  = llvm::Type::getInt32Ty(*context_);

        // Canonical header layout shared by every reference-type class.
        // Using a locally-constructed struct keeps the GEPs well-typed even
        // though individual subclass StructTypes append extra fields.
        llvm::StructType* headerTy = llvm::StructType::get(*context_, {ptrTy, i32Ty});

        // --- elegant_retain(ptr) ---
        {
            auto* ft = llvm::FunctionType::get(voidTy, {ptrTy}, false);
            auto* retainF = llvm::Function::Create(ft, llvm::Function::InternalLinkage, "elegant_retain", module_.get());
            auto* bb = llvm::BasicBlock::Create(*context_, "entry", retainF);
            llvm::IRBuilder<> B(bb);

            llvm::Value* objPtr       = retainF->getArg(0);
            llvm::Value* refCountPtr  = B.CreateStructGEP(headerTy, objPtr, 1);
            llvm::Value* count        = B.CreateLoad(i32Ty, refCountPtr);
            llvm::Value* incd         = B.CreateAdd(count, llvm::ConstantInt::get(i32Ty, 1));
            B.CreateStore(incd, refCountPtr);
            B.CreateRetVoid();
        }

        // --- elegant_release(ptr) ---
        {
            auto* ft = llvm::FunctionType::get(voidTy, {ptrTy}, false);
            auto* releaseF = llvm::Function::Create(ft, llvm::Function::InternalLinkage, "elegant_release", module_.get());
            auto* entryBB = llvm::BasicBlock::Create(*context_, "entry",   releaseF);
            auto* freeBB  = llvm::BasicBlock::Create(*context_, "free_it", releaseF);
            auto* contBB  = llvm::BasicBlock::Create(*context_, "cont",    releaseF);
            llvm::IRBuilder<> B(entryBB);

            llvm::Value* objPtr      = releaseF->getArg(0);
            llvm::Value* refCountPtr = B.CreateStructGEP(headerTy, objPtr, 1);
            llvm::Value* count       = B.CreateLoad(i32Ty, refCountPtr);
            llvm::Value* decd        = B.CreateSub(count, llvm::ConstantInt::get(i32Ty, 1));
            B.CreateStore(decd, refCountPtr);
            llvm::Value* isZero = B.CreateICmpSLE(decd, llvm::ConstantInt::get(i32Ty, 0));
            B.CreateCondBr(isZero, freeBB, contBB);

            B.SetInsertPoint(freeBB);
            llvm::Value* fmt = B.CreateGlobalString("\xE2\x99\xBB\xEF\xB8\x8F  ARC: Object Memory Freed!\n", "arc_free_fmt");
            B.CreateCall(getPrintf(), {fmt});
            B.CreateCall(getFree(),   {objPtr});
            B.CreateBr(contBB);

            B.SetInsertPoint(contBB);
            B.CreateRetVoid();
        }
    }

    // FEATURE: Polymorphism — structural subtype test for class hierarchies.
    // `Dog` is-a `Animal` when Dog's superclass chain eventually reaches
    // Animal. We strip trailing Optional markers so `Dog?` is still an
    // `Animal?` for assignment / argument compatibility.
    bool isSubclass(std::string child, std::string parent) {
        if (!child.empty() && (child.back() == '?' || child.back() == '!')) child.pop_back();
        if (!parent.empty() && (parent.back() == '?' || parent.back() == '!')) parent.pop_back();
        if (child == parent) return true;
        auto it = structs_.find(child);
        if (it == structs_.end()) return false;
        const std::string& sup = it->second.superclass;
        if (sup.empty()) return false;
        return isSubclass(sup, parent);
    }

    // FEATURE: Polymorphism — recursive layout resolver.
    // A subclass inherits every field (after the two-slot header) and every
    // V-Table entry from its superclass. Overriding a method rewrites the
    // inherited V-Table slot; new methods append fresh slots. Properties the
    // subclass declares land after the inherited ones.
    void resolveLayout(const std::string& name) {
        auto it = structs_.find(name);
        if (it == structs_.end()) return;
        StructInfo& info = it->second;
        if (info.resolved) return;
        info.resolved = true;

        llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
        llvm::Type* i32Ty = llvm::Type::getInt32Ty(*context_);

        unsigned fieldIdx = 0;
        if (info.isReferenceType) {
            // Slot 0: V-Table pointer. Slot 1: ref_count.
            info.fieldTypes.push_back(ptrTy);
            info.fieldTypesString["__vtable"] = "VTablePtr";
            info.fieldTypes.push_back(i32Ty);
            info.fieldTypesString["__ref_count"] = "Int";
            fieldIdx = 2;
        }

        if (!info.superclass.empty()) {
            auto supIt = structs_.find(info.superclass);
            if (supIt == structs_.end()) {
                ThrowTypeError("Class '" + name + "' inherits from unknown type '" + info.superclass + "'");
            }
            resolveLayout(info.superclass);
            StructInfo& sup = supIt->second;

            // Inherit V-Table layout wholesale (subclass may override slots).
            info.vtableMethods = sup.vtableMethods;
            info.vtableIndices = sup.vtableIndices;

            // Copy parent properties, skipping the two-slot header (already
            // placed above).
            for (size_t i = 2; i < sup.fieldTypes.size(); ++i) {
                info.fieldTypes.push_back(sup.fieldTypes[i]);
            }
            for (const auto& [fName, fIdx] : sup.fieldIndices) {
                if (fIdx >= 2) info.fieldIndices[fName] = fIdx;
            }
            for (const auto& [fName, fType] : sup.fieldTypesString) {
                if (fName != "__vtable" && fName != "__ref_count") {
                    info.fieldTypesString[fName] = fType;
                }
            }
            fieldIdx = static_cast<unsigned>(info.fieldTypes.size());
        }

        auto members = ctx_.getArrayElements(info.astMembers);
        for (const auto& mem : members) {
            auto memArr = ctx_.getArrayElements(mem);
            if (memArr.size == 0) continue;
            std::string_view kind = EvoParser::toString(memArr[0]);

            if (kind == "Property") {
                std::string propName = std::string(EvoParser::toString(memArr[2]));
                std::string propType = EvoParser::isNull(memArr[3]) ? "Int" : std::string(EvoParser::toString(memArr[3]));
                info.fieldIndices[propName] = fieldIdx++;
                info.fieldTypes.push_back(getLLVMType(propType));
                info.fieldTypesString[propName] = propType;
            }
            else if (kind == "Function") {
                // Only reference types carry a V-Table; value-type structs
                // keep static dispatch.
                if (!info.isReferenceType) continue;

                std::string funcName = std::string(EvoParser::toString(memArr[1]));
                std::string mangled  = name + "_" + funcName;

                auto slotIt = info.vtableIndices.find(funcName);
                if (slotIt != info.vtableIndices.end()) {
                    // Override inherited slot.
                    info.vtableMethods[slotIt->second] = mangled;
                } else {
                    info.vtableIndices[funcName] = static_cast<unsigned>(info.vtableMethods.size());
                    info.vtableMethods.push_back(mangled);
                }
            }
        }

        if (info.isReferenceType) {
            std::vector<llvm::Type*> vfuncTypes(info.vtableMethods.size(), ptrTy);
            info.vtableType = llvm::StructType::create(*context_, name + "_VTable");
            info.vtableType->setBody(vfuncTypes);
            info.vtableGlobal = new llvm::GlobalVariable(
                *module_,
                info.vtableType,
                /*isConstant=*/true,
                llvm::GlobalValue::InternalLinkage,
                /*Initializer=*/nullptr,
                name + "_vtable_inst");
        }

        info.type->setBody(info.fieldTypes);
    }

    llvm::StructType* getSwiftArrayType() {
        if (auto* T = llvm::StructType::getTypeByName(*context_, "SwiftArray")) return T;
        auto* T = llvm::StructType::create(*context_, "SwiftArray");
        T->setBody({
            llvm::Type::getInt32Ty(*context_),
            llvm::Type::getInt32Ty(*context_),
            llvm::PointerType::getUnqual(*context_)
        });
        return T;
    }

    // FEATURE: Dynamic Tagged Unions for Optionals. A type ending in `?`
    // lowers to `{ i1 is_valid, T data }` — a standard Swift-style Optional
    // struct. Implicitly-unwrapped `T!` is treated identically at the storage
    // level; the force-unwrap runtime check is what makes them different.
    llvm::Type* getLLVMType(const std::string& typeName) {
        if (!typeName.empty() && (typeName.back() == '?' || typeName.back() == '!')) {
            std::string baseType = typeName.substr(0, typeName.length() - 1);
            llvm::Type* innerTy = getLLVMType(baseType);
            return llvm::StructType::get(*context_, {llvm::Type::getInt1Ty(*context_), innerTy});
        }

        if (typeName == "Int") return llvm::Type::getInt32Ty(*context_);
        if (typeName == "Float") return llvm::Type::getDoubleTy(*context_);
        if (typeName == "String") return llvm::PointerType::getUnqual(*context_);
        if (typeName == "Array") return llvm::PointerType::getUnqual(*context_);
        if (typeName == "Void" || typeName == "") return llvm::Type::getVoidTy(*context_);

        if (structs_.count(typeName)) {
            if (structs_[typeName].isReferenceType) return llvm::PointerType::getUnqual(*context_);
            else return structs_[typeName].type;
        }
        return llvm::Type::getInt32Ty(*context_);
    }

    void compile() {
        // FEATURE: ARC — emit the retain/release runtime into every module
        // before any user code can reference it.
        buildARCFunctions();

        auto declarations = ctx_.getArrayElements(ctx_.root);

        // Pass 1: Type & Signature Registration
        for (const auto& declVal : declarations) {
            auto declArr = ctx_.getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);

            if (nodeType == "Class" || nodeType == "Struct") {
                std::string name = std::string(EvoParser::toString(declArr[1]));
                StructInfo& info = structs_[name];
                info.type = llvm::StructType::create(*context_, name);
                info.isReferenceType = (nodeType == "Class");
                info.astMembers = declArr[3];

                // FEATURE: Polymorphism — capture the inheritance clause.
                // The parser emits superclass as an array of Identifiers so we
                // accept both the array form and the plain StringView form for
                // forward-compat. Only classes participate in inheritance.
                if (nodeType == "Class" && !EvoParser::isNull(declArr[2])) {
                    auto supVal = declArr[2];
                    if (supVal.type == EvoParser::ValueType::StringView) {
                        info.superclass = std::string(EvoParser::toString(supVal));
                    } else if (supVal.type == EvoParser::ValueType::Array) {
                        auto supArr = ctx_.getArrayElements(supVal);
                        if (supArr.size > 0) {
                            info.superclass = std::string(EvoParser::toString(supArr[0]));
                        }
                    }
                }

                // Register method signatures so Pass 3 can typecheck calls.
                for (const auto& mem : ctx_.getArrayElements(info.astMembers)) {
                    auto memArr = ctx_.getArrayElements(mem);
                    if (memArr.size == 0) continue;
                    if (EvoParser::toString(memArr[0]) != "Function") continue;

                    std::string mName = name + "_" + std::string(EvoParser::toString(memArr[1]));
                    FuncSig sig;
                    sig.argTypes.push_back(name); // Implicit 'self'
                    if (!EvoParser::isNull(memArr[2])) {
                        for (const auto& param : ctx_.getArrayElements(memArr[2])) {
                            sig.argTypes.push_back(std::string(EvoParser::toString(ctx_.getArrayElements(param)[2])));
                        }
                    }
                    sig.retType = EvoParser::isNull(memArr[3]) ? "Void" : std::string(EvoParser::toString(memArr[3]));
                    functions_[mName] = sig;
                }
            }
            else if (nodeType == "Extern") {
                std::string extName = std::string(EvoParser::toString(declArr[1]));
                FuncSig sig;
                std::vector<llvm::Type*> argTypes;

                if (!EvoParser::isNull(declArr[2])) {
                    auto paramsArr = ctx_.getArrayElements(declArr[2]);
                    for (const auto& param : paramsArr) {
                        auto p = ctx_.getArrayElements(param);
                        std::string pType = std::string(EvoParser::toString(p[2]));
                        if (pType == "VarArg") sig.isVarArg = true;
                        else {
                            sig.argTypes.push_back(pType);
                            argTypes.push_back(getLLVMType(pType));
                        }
                    }
                }
                sig.retType = EvoParser::isNull(declArr[3]) ? "Void" : std::string(EvoParser::toString(declArr[3]));
                functions_[extName] = sig;

                llvm::FunctionType* ft = llvm::FunctionType::get(getLLVMType(sig.retType), argTypes, sig.isVarArg);
                llvm::Function::Create(ft, llvm::Function::ExternalLinkage, extName, module_.get());
            }
        }

        // Pass 2a: Register top-level function signatures (Pass 1 handled
        // methods, structs, classes and externs already).
        for (const auto& declVal : declarations) {
            auto declArr = ctx_.getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);

            if (nodeType == "Function") {
                std::string name = std::string(EvoParser::toString(declArr[1]));
                FuncSig sig;
                if (!EvoParser::isNull(declArr[2])) {
                    for (const auto& param : ctx_.getArrayElements(declArr[2])) {
                        sig.argTypes.push_back(std::string(EvoParser::toString(ctx_.getArrayElements(param)[2])));
                    }
                }
                sig.retType = EvoParser::isNull(declArr[3]) ? "Void" : std::string(EvoParser::toString(declArr[3]));
                functions_[name] = sig;
            }
        }

        // Pass 2b: Resolve class/struct memory layouts recursively so parent
        // classes are laid out before their children.
        for (const auto& declVal : declarations) {
            auto declArr = ctx_.getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);
            if (nodeType == "Class" || nodeType == "Struct") {
                resolveLayout(std::string(EvoParser::toString(declArr[1])));
            }
        }

        // Pass 3: Code Generation
        pushScope(); // Global scope
        for (const auto& declVal : declarations) {
            auto declArr = ctx_.getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);

            if (nodeType == "Function") {
                compileFunction(declArr, "", nullptr);
            } else if (nodeType == "Class" || nodeType == "Struct") {
                std::string className = std::string(EvoParser::toString(declArr[1]));
                auto members = ctx_.getArrayElements(declArr[3]);
                for (const auto& mem : members) {
                    auto memArr = ctx_.getArrayElements(mem);
                    if (EvoParser::toString(memArr[0]) == "Function") {
                        compileFunction(memArr, className, structs_[className].type);
                    }
                }
            }
        }
        popScope();

        // Pass 4: Emit a concrete V-Table global per reference-type class.
        // Each slot is initialised with a pointer to the final (possibly
        // overridden) method function. Inherited methods that the subclass
        // did not override still resolve to the parent's implementation
        // because the mangled name was copied during resolveLayout.
        for (auto& [name, info] : structs_) {
            if (!info.isReferenceType || info.vtableGlobal == nullptr) continue;

            std::vector<llvm::Constant*> funcs;
            funcs.reserve(info.vtableMethods.size());
            llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
            for (const std::string& mName : info.vtableMethods) {
                llvm::Function* f = module_->getFunction(mName);
                if (f) {
                    funcs.push_back(f);
                } else {
                    funcs.push_back(llvm::ConstantPointerNull::get(llvm::cast<llvm::PointerType>(ptrTy)));
                }
            }
            info.vtableGlobal->setInitializer(llvm::ConstantStruct::get(info.vtableType, funcs));
        }
    }

    void dumpIR() { module_->print(llvm::outs(), nullptr); }

    int executeJIT() {
        llvm::InitializeNativeTarget();
        llvm::InitializeNativeTargetAsmPrinter();
        llvm::InitializeNativeTargetAsmParser();

        auto jitExpected = llvm::orc::LLJITBuilder().create();
        if (!jitExpected) return 1;
        auto jit = std::move(jitExpected.get());

        module_->setDataLayout(jit->getDataLayout());
        auto processSymbols = llvm::orc::DynamicLibrarySearchGenerator::GetForCurrentProcess(jit->getDataLayout().getGlobalPrefix());
        if (processSymbols) jit->getMainJITDylib().addGenerator(std::move(*processSymbols));

        auto tsm = llvm::orc::ThreadSafeModule(std::move(module_), std::move(context_));
        if (auto err = jit->addIRModule(std::move(tsm))) return 1;

        auto mainSym = jit->lookup("main");
        if (!mainSym) return 1;

        int (*mainFn)() = mainSym->toPtr<int (*)()>();

        std::cout << "\n[JIT Execution Started]\n";
        int result = mainFn();
        std::cout << "[JIT Exit Code]: " << result << "\n";
        return result;
    }

    bool emitObjectFile(const std::string& filename) {
        llvm::InitializeNativeTarget();
        llvm::InitializeNativeTargetAsmParser();
        llvm::InitializeNativeTargetAsmPrinter();

        std::string targetTripleStr = llvm::sys::getDefaultTargetTriple();
        llvm::Triple targetTriple(targetTripleStr);
        module_->setTargetTriple(targetTriple);

        std::string error;
        auto target = llvm::TargetRegistry::lookupTarget(targetTripleStr, error);
        if (!target) return false;

        auto targetMachine = target->createTargetMachine(targetTriple, "generic", "", llvm::TargetOptions(), std::optional<llvm::Reloc::Model>(llvm::Reloc::PIC_));
        module_->setDataLayout(targetMachine->createDataLayout());

        std::error_code ec;
        llvm::raw_fd_ostream dest(filename, ec, llvm::sys::fs::OF_None);
        if (ec) return false;

        llvm::legacy::PassManager pass;
        if (targetMachine->addPassesToEmitFile(pass, dest, nullptr, llvm::CodeGenFileType::ObjectFile)) return false;

        pass.run(*module_);
        dest.flush();
        return true;
    }

private:
    [[noreturn]] void ThrowTypeError(const std::string& msg) {
        std::cerr << "\n\xE2\x9D\x8C  Semantic Error: " << msg << "\n";
        std::exit(1);
    }

    llvm::AllocaInst* CreateEntryBlockAlloca(llvm::Function* TheFunction, const std::string& VarName, llvm::Type* type) {
        llvm::IRBuilder<> TmpB(&TheFunction->getEntryBlock(), TheFunction->getEntryBlock().begin());
        return TmpB.CreateAlloca(type, nullptr, VarName);
    }

    llvm::Function* compileFunction(const EvoParser::ArrayView& funcNode, std::string className, llvm::StructType* classType) {
        std::string name = std::string(EvoParser::toString(funcNode[1]));
        if (!className.empty()) name = className + "_" + name;

        std::vector<llvm::Type*> argTypes;
        std::vector<std::string> argNames;

        if (classType) {
            argTypes.push_back(structs_[className].isReferenceType ? llvm::PointerType::getUnqual(*context_) : classType->getPointerTo());
            argNames.push_back("self");
        }

        if (!EvoParser::isNull(funcNode[2])) {
            auto paramsArr = ctx_.getArrayElements(funcNode[2]);
            for (const auto& param : paramsArr) {
                auto p = ctx_.getArrayElements(param);
                argNames.push_back(std::string(EvoParser::toString(p[1])));
                std::string pType = std::string(EvoParser::toString(p[2]));
                argTypes.push_back(getLLVMType(pType));
            }
        }

        std::string retTypeName = EvoParser::isNull(funcNode[3]) ? "Void" : std::string(EvoParser::toString(funcNode[3]));
        llvm::FunctionType* ft = llvm::FunctionType::get(getLLVMType(retTypeName), argTypes, false);
        llvm::Function* f = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, name, module_.get());

        llvm::BasicBlock* bb = llvm::BasicBlock::Create(*context_, "entry", f);
        builder_->SetInsertPoint(bb);

        pushScope(); // Function Body Scope

        unsigned idx = 0;
        for (auto& arg : f->args()) {
            std::string argName = argNames[idx++];
            arg.setName(argName);
            llvm::AllocaInst* Alloca = CreateEntryBlockAlloca(f, argName, arg.getType());
            builder_->CreateStore(&arg, Alloca);
            defineVar(argName, {Alloca, argName == "self" ? className : functions_[name].argTypes[idx-1]});
        }

        auto bodyArr = ctx_.getArrayElements(funcNode[4]);
        for (const auto& stmt : bodyArr) compileStatement(stmt);

        popScope();

        // Implicit return if none found
        if (bb->getTerminatorOrNull() == nullptr) {
            if (retTypeName == "Void") builder_->CreateRetVoid();
            else builder_->CreateRet(llvm::ConstantInt::get(*context_, llvm::APInt(32, 0, true)));
        }

        llvm::verifyFunction(*f);
        return f;
    }

    TypedValue compileLValue(const EvoParser::Value& expr) {
        if (expr.type == EvoParser::ValueType::StringView) {
            std::string varName = std::string(EvoParser::toString(expr));
            auto var = lookupVar(varName);
            if (!var) ThrowTypeError("Unknown variable '" + varName + "'");
            return {var->alloca, var->typeName};
        }

        auto arr = ctx_.getArrayElements(expr);
        if (arr.size > 0) {
            std::string_view nodeType = EvoParser::toString(arr[0]);

            if (nodeType == "Subscript") {
                std::string baseName = std::string(EvoParser::toString(arr[1]));
                TypedValue indexVal = compileExpression(arr[2]);
                if (indexVal.type != "Int") ThrowTypeError("Array subscript must be an Int.");

                auto var = lookupVar(baseName);
                if (!var) ThrowTypeError("Unknown array '" + baseName + "'");
                if (var->typeName != "Array") ThrowTypeError("Cannot subscript non-array type '" + var->typeName + "'");

                llvm::Value* arrObj = builder_->CreateLoad(llvm::PointerType::getUnqual(*context_), var->alloca);
                llvm::Value* bufPtrAddr = builder_->CreateStructGEP(getSwiftArrayType(), arrObj, 2);
                llvm::Value* bufPtr = builder_->CreateLoad(llvm::PointerType::getUnqual(*context_), bufPtrAddr);
                return {builder_->CreateGEP(llvm::Type::getInt32Ty(*context_), bufPtr, indexVal.val), "Int"};
            }
            else if (nodeType == "MemberAccess" || nodeType == "SelfAccess") {
                std::string baseName, propName;
                if (nodeType == "MemberAccess") {
                    baseName = std::string(EvoParser::toString(arr[1]));
                    propName = std::string(EvoParser::toString(arr[2]));
                } else {
                    baseName = "self";
                    propName = std::string(EvoParser::toString(arr[1]));
                }

                auto var = lookupVar(baseName);
                if (!var) ThrowTypeError("Unknown object '" + baseName + "'");
                std::string typeName = var->typeName;
                if (!structs_.count(typeName)) ThrowTypeError("Type '" + typeName + "' is not a struct/class.");

                StructInfo& info = structs_[typeName];
                if (!info.fieldIndices.count(propName)) ThrowTypeError("Type '" + typeName + "' has no property '" + propName + "'");

                unsigned idx = info.fieldIndices[propName];
                std::string pType = info.fieldTypesString[propName];

                llvm::Value* basePtr = var->alloca;
                if (info.isReferenceType || nodeType == "SelfAccess") {
                    basePtr = builder_->CreateLoad(llvm::PointerType::getUnqual(*context_), basePtr);
                }
                return {builder_->CreateStructGEP(info.type, basePtr, idx), pType};
            }
        }
        return {nullptr, ""};
    }

    void compileStatement(const EvoParser::Value& stmtVal) {
        auto stmtArr = ctx_.getArrayElements(stmtVal);
        if (stmtArr.size == 0) return;

        std::string_view nodeType = EvoParser::toString(stmtArr[0]);

        if (nodeType == "Return") {
            if (!EvoParser::isNull(stmtArr[1])) {
                TypedValue retVal = compileExpression(stmtArr[1]);
                builder_->CreateRet(retVal.val);
            } else {
                builder_->CreateRetVoid();
            }
            return;
        }

        if (nodeType == "Property") {
            std::string varName = std::string(EvoParser::toString(stmtArr[2]));
            std::string varType = "";

            if (!EvoParser::isNull(stmtArr[3])) varType = std::string(EvoParser::toString(stmtArr[3]));

            TypedValue initVal = {nullptr, ""};
            std::string rhsConstructorType;  // e.g. "Dog" for `= Dog()`
            if (!EvoParser::isNull(stmtArr[4])) {
                auto rhs = stmtArr[4];
                // Resolve constructors. When the RHS is a bare `Type()` call
                // we skip compileExpression so the allocation/VTable wiring
                // below knows which class to build.
                if (rhs.type == EvoParser::ValueType::Array) {
                    auto rhsArr = ctx_.getArrayElements(rhs);
                    if (EvoParser::toString(rhsArr[0]) == "Call" && rhsArr[1].type == EvoParser::ValueType::StringView) {
                        std::string callee = std::string(EvoParser::toString(rhsArr[1]));
                        if (structs_.count(callee)) {
                            rhsConstructorType = callee;
                            // Infer only when no explicit annotation was given;
                            // leaving a user-provided annotation intact keeps
                            // upcasts (`var a: Animal = Dog()`) honest.
                            if (varType.empty()) varType = callee;
                        }
                    }
                }
                if (rhsConstructorType.empty()) initVal = compileExpression(rhs);
            }

            // TYPE INFERENCE
            if (varType == "") {
                if (initVal.type == "Nil") ThrowTypeError("Cannot infer type from 'nil'. Variable '" + varName + "' requires an explicit Optional type annotation.");
                if (initVal.val == nullptr) ThrowTypeError("Variable '" + varName + "' requires an explicit type or initial value.");
                varType = initVal.type;
            }

            bool isOptional = !varType.empty() && (varType.back() == '?' || varType.back() == '!');

            // FEATURE: Polymorphism — allow implicit upcasts on reference
            // types (e.g. `var a: Animal = Dog()` / `var a: Animal = dog`)
            // as long as the RHS is a subclass of the annotated type.
            if (!isOptional && initVal.val != nullptr && initVal.type != varType
                && !isSubclass(initVal.type, varType)) {
                ThrowTypeError("Cannot assign type '" + initVal.type + "' to variable of type '" + varType + "'");
            }
            if (!rhsConstructorType.empty() && !isSubclass(rhsConstructorType, varType)) {
                ThrowTypeError("Cannot initialize '" + varType + "' from '" + rhsConstructorType + "()'");
            }

            llvm::Type* llvmTy = getLLVMType(varType);
            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::AllocaInst* Alloca = CreateEntryBlockAlloca(TheFunction, varName, llvmTy);
            defineVar(varName, {Alloca, varType});

            // FEATURE: Pack standard values into Optional Tagged Unions.
            // Storage is always { i1 is_valid, T data }; we always store a
            // fully-formed struct so loads are well-defined.
            if (isOptional) {
                llvm::Value* optStruct = llvm::UndefValue::get(llvmTy);
                if (initVal.type == "Nil" || initVal.val == nullptr) {
                    optStruct = builder_->CreateInsertValue(optStruct, builder_->getInt1(false), 0);
                } else if (initVal.type == varType) {
                    optStruct = initVal.val; // Optional-to-Optional copy
                } else {
                    std::string innerType = varType.substr(0, varType.length() - 1);
                    if (initVal.type != innerType) {
                        ThrowTypeError("Cannot assign type '" + initVal.type + "' to variable of type '" + varType + "'");
                    }
                    optStruct = builder_->CreateInsertValue(optStruct, builder_->getInt1(true), 0);
                    optStruct = builder_->CreateInsertValue(optStruct, initVal.val, 1);
                }
                builder_->CreateStore(optStruct, Alloca);
                return;
            }

            if (structs_.count(varType)) {
                StructInfo& info = structs_[varType];
                if (info.isReferenceType) {
                    // FEATURE: Polymorphism — upcasting. When the RHS is an
                    // already-allocated subclass instance we just alias the
                    // pointer and bump its ref_count; no new allocation.
                    if (initVal.val != nullptr && isSubclass(initVal.type, varType)) {
                        builder_->CreateCall(module_->getFunction("elegant_retain"), {initVal.val});
                        builder_->CreateStore(initVal.val, Alloca);
                    } else {
                        // Allocate a fresh instance of the declared concrete
                        // class (rhsConstructorType when present — else the
                        // annotation). This determines the heap size AND the
                        // V-Table that gets wired into slot 0.
                        std::string concrete = !rhsConstructorType.empty() ? rhsConstructorType : varType;
                        StructInfo& cls = structs_[concrete];

                        uint64_t classSize = module_->getDataLayout().getTypeAllocSize(cls.type);
                        llvm::Value* sizeVal = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context_), classSize);
                        llvm::Value* heapPtr = builder_->CreateCall(getMalloc(), {sizeVal});

                        // Slot 0: V-Table pointer (Polymorphism).
                        if (cls.vtableGlobal) {
                            llvm::Value* vtablePtrAddr = builder_->CreateStructGEP(cls.type, heapPtr, 0);
                            builder_->CreateStore(cls.vtableGlobal, vtablePtrAddr);
                        }

                        // Slot 1: ARC ref_count = 1.
                        llvm::Value* refCountPtr = builder_->CreateStructGEP(cls.type, heapPtr, 1);
                        builder_->CreateStore(
                            llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), 1),
                            refCountPtr);

                        builder_->CreateStore(heapPtr, Alloca);
                    }
                } else if (initVal.val) {
                    builder_->CreateStore(initVal.val, Alloca);
                }
            } else if (initVal.val) {
                builder_->CreateStore(initVal.val, Alloca);
            }
            return;
        }

        if (nodeType == "Assign") {
            TypedValue lhs = compileLValue(stmtArr[2]);
            TypedValue rhs = compileExpression(stmtArr[3]);

            bool lhsIsOptional = !lhs.type.empty() && (lhs.type.back() == '?' || lhs.type.back() == '!');

            // FEATURE: Optional assignment — dynamically (re)wrap the RHS
            // into a tagged-union struct (either `nil`, a direct Optional, or
            // an auto-promoted base value).
            if (lhsIsOptional) {
                llvm::Value* optStruct = llvm::UndefValue::get(getLLVMType(lhs.type));
                if (rhs.type == "Nil") {
                    optStruct = builder_->CreateInsertValue(optStruct, builder_->getInt1(false), 0);
                } else if (rhs.type == lhs.type) {
                    optStruct = rhs.val;
                } else {
                    std::string innerType = lhs.type.substr(0, lhs.type.length() - 1);
                    if (rhs.type != innerType) {
                        ThrowTypeError("Cannot assign type '" + rhs.type + "' to variable of type '" + lhs.type + "'");
                    }
                    optStruct = builder_->CreateInsertValue(optStruct, builder_->getInt1(true), 0);
                    optStruct = builder_->CreateInsertValue(optStruct, rhs.val, 1);
                }
                builder_->CreateStore(optStruct, lhs.val);
                return;
            }

            // FEATURE: Polymorphism — allow upcasts on reference-type assigns
            // (`a = dog` where `a: Animal`) as long as `Dog` is-a `Animal`.
            if (lhs.type != rhs.type && !isSubclass(rhs.type, lhs.type)) {
                ThrowTypeError("Cannot assign type '" + rhs.type + "' to '" + lhs.type + "'");
            }

            // FEATURE: ARC — reference-type rebinds release the outgoing
            // object and retain the incoming one before the store lands.
            auto arcIt = structs_.find(rhs.type);
            if (arcIt != structs_.end() && arcIt->second.isReferenceType) {
                llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
                llvm::Value* oldObj = builder_->CreateLoad(ptrTy, lhs.val);
                builder_->CreateCall(module_->getFunction("elegant_release"), {oldObj});
                builder_->CreateCall(module_->getFunction("elegant_retain"),  {rhs.val});
            }

            builder_->CreateStore(rhs.val, lhs.val);
            return;
        }

        if (nodeType == "For") {
            std::string varName = std::string(EvoParser::toString(stmtArr[1]));
            TypedValue startV = compileExpression(stmtArr[2]);
            TypedValue endV = compileExpression(stmtArr[3]);
            if (startV.type != "Int" || endV.type != "Int") ThrowTypeError("Range bounds must be Ints.");

            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            pushScope(); // Loop Scope

            llvm::AllocaInst* Alloca = CreateEntryBlockAlloca(TheFunction, varName, llvm::Type::getInt32Ty(*context_));
            builder_->CreateStore(startV.val, Alloca);
            defineVar(varName, {Alloca, "Int"});

            llvm::BasicBlock* CondBB = llvm::BasicBlock::Create(*context_, "forcond", TheFunction);
            llvm::BasicBlock* LoopBB = llvm::BasicBlock::Create(*context_, "forloop", TheFunction);
            llvm::BasicBlock* AfterBB = llvm::BasicBlock::Create(*context_, "forcont", TheFunction);

            builder_->CreateBr(CondBB);
            builder_->SetInsertPoint(CondBB);

            llvm::Value* currV = builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), Alloca, varName);
            llvm::Value* condV = builder_->CreateICmpSLE(currV, endV.val, "loopcond");
            builder_->CreateCondBr(condV, LoopBB, AfterBB);

            builder_->SetInsertPoint(LoopBB);
            auto bodyArr = ctx_.getArrayElements(stmtArr[4]);
            for (const auto& s : bodyArr) compileStatement(s);

            llvm::Value* stepV = builder_->CreateAdd(builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), Alloca), llvm::ConstantInt::get(*context_, llvm::APInt(32, 1, true)));
            builder_->CreateStore(stepV, Alloca);
            builder_->CreateBr(CondBB);

            builder_->SetInsertPoint(AfterBB);
            popScope();
            return;
        }

        if (nodeType == "If" || nodeType == "While") {
            TypedValue condV = compileExpression(stmtArr[1]);
            if (condV.type != "Bool" && condV.type != "Int") ThrowTypeError("Condition must evaluate to a Bool or Int.");

            llvm::Value* cmpV = builder_->CreateICmpNE(condV.val, llvm::ConstantInt::get(*context_, llvm::APInt(32, 0, true)), "cond");
            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::BasicBlock* ThenBB = llvm::BasicBlock::Create(*context_, "block", TheFunction);
            llvm::BasicBlock* MergeBB = llvm::BasicBlock::Create(*context_, "cont");

            builder_->CreateCondBr(cmpV, ThenBB, MergeBB);
            builder_->SetInsertPoint(ThenBB);

            pushScope(); // Block Scope
            auto arr = ctx_.getArrayElements(stmtArr[2]);
            for (const auto& s : arr) compileStatement(s);
            popScope();

            builder_->CreateBr(MergeBB);
            TheFunction->insert(TheFunction->end(), MergeBB);
            builder_->SetInsertPoint(MergeBB);
            return;
        }

        compileExpression(stmtVal);
    }

    TypedValue compileExpression(const EvoParser::Value& exprVal) {
        if (exprVal.type == EvoParser::ValueType::StringView) {
            std::string varName = std::string(EvoParser::toString(exprVal));
            auto var = lookupVar(varName);
            if (!var) ThrowTypeError("Variable '" + varName + "' used before being declared.");
            return {builder_->CreateLoad(getLLVMType(var->typeName), var->alloca, varName.c_str()), var->typeName};
        }

        auto exprArr = ctx_.getArrayElements(exprVal);
        if (exprArr.size == 0) return {nullptr, ""};
        std::string_view nodeType = EvoParser::toString(exprArr[0]);

        if (nodeType == "String") {
            return {builder_->CreateGlobalString(std::string(EvoParser::toString(exprArr[1])), "str"), "String"};
        }

        // FEATURE: The `nil` literal. Carries the special type "Nil" so the
        // surrounding Property/Assign can wrap it into the correct Optional
        // struct (a bare `nil` has no intrinsic inner type).
        if (nodeType == "Nil") return {nullptr, "Nil"};

        // FEATURE: Forced Unwrapping Runtime Safety Checker. Branches on the
        // Optional's `is_valid` flag and jumps to `elegant_panic` if it's
        // false, otherwise extracts the payload.
        if (nodeType == "ForceUnwrap") {
            TypedValue base = compileExpression(exprArr[1]);
            if (base.type.empty() || (base.type.back() != '?' && base.type.back() != '!')) {
                ThrowTypeError("Cannot force-unwrap non-optional type '" + base.type + "'");
            }

            llvm::Value* isSome = builder_->CreateExtractValue(base.val, 0, "is_some");

            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::BasicBlock* PanicBB = llvm::BasicBlock::Create(*context_, "unwrap_panic", TheFunction);
            llvm::BasicBlock* ContBB  = llvm::BasicBlock::Create(*context_, "unwrap_cont",  TheFunction);

            builder_->CreateCondBr(isSome, ContBB, PanicBB);

            builder_->SetInsertPoint(PanicBB);
            builder_->CreateCall(getPanic());
            builder_->CreateUnreachable();

            builder_->SetInsertPoint(ContBB);
            std::string innerType = base.type.substr(0, base.type.length() - 1);
            llvm::Value* innerVal = builder_->CreateExtractValue(base.val, 1, "unwrapped");
            return {innerVal, innerType};
        }

        if (nodeType == "ArrayLiteral") {
            std::vector<llvm::Value*> elements;
            if (!EvoParser::isNull(exprArr[1])) {
                auto argsArr = ctx_.getArrayElements(exprArr[1]);
                for (const auto& arg : argsArr) {
                    TypedValue ev = compileExpression(arg);
                    if (ev.type != "Int") ThrowTypeError("Arrays currently only support 'Int' elements.");
                    elements.push_back(ev.val);
                }
            }

            llvm::StructType* arrTy = getSwiftArrayType();
            uint64_t structSize = module_->getDataLayout().getTypeAllocSize(arrTy);
            llvm::Value* arrHeapPtr = builder_->CreateCall(getMalloc(), {llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context_), structSize)});

            uint64_t bufSize = elements.size() * 4;
            llvm::Value* bufHeapPtr = builder_->CreateCall(getMalloc(), {llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context_), bufSize)});

            builder_->CreateStore(llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), elements.size()), builder_->CreateStructGEP(arrTy, arrHeapPtr, 0));
            builder_->CreateStore(llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), elements.size()), builder_->CreateStructGEP(arrTy, arrHeapPtr, 1));
            builder_->CreateStore(bufHeapPtr, builder_->CreateStructGEP(arrTy, arrHeapPtr, 2));

            for (size_t i = 0; i < elements.size(); i++) {
                llvm::Value* idxVal = llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), i);
                llvm::Value* elemPtr = builder_->CreateGEP(llvm::Type::getInt32Ty(*context_), bufHeapPtr, idxVal);
                builder_->CreateStore(elements[i], elemPtr);
            }
            return {arrHeapPtr, "Array"};
        }

        if (nodeType == "MemberAccess" || nodeType == "SelfAccess" || nodeType == "Subscript") {
            // Built-in Swift Array `.count` — checked before lvalue path so
            // user-defined structs with the same name still route through it.
            if (nodeType == "MemberAccess") {
                std::string baseName = std::string(EvoParser::toString(exprArr[1]));
                std::string propName = std::string(EvoParser::toString(exprArr[2]));
                auto var = lookupVar(baseName);

                if (var && var->typeName == "Array" && propName == "count") {
                    llvm::Value* arrObj = builder_->CreateLoad(llvm::PointerType::getUnqual(*context_), var->alloca);
                    llvm::Value* countPtr = builder_->CreateStructGEP(getSwiftArrayType(), arrObj, 1);
                    return {builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), countPtr), "Int"};
                }
            }

            TypedValue ptr = compileLValue(exprVal);
            if (!ptr.val) ThrowTypeError("Invalid property access.");
            return {builder_->CreateLoad(getLLVMType(ptr.type), ptr.val), ptr.type};
        }

        if (nodeType == "Int") {
            return {llvm::ConstantInt::get(*context_, llvm::APInt(32, std::stoi(std::string(EvoParser::toString(exprArr[1]))), true)), "Int"};
        }

        if (nodeType == "Call") {
            auto targetNode = exprArr[1];
            if (targetNode.type == EvoParser::ValueType::StringView) {
                std::string callee = std::string(EvoParser::toString(targetNode));
                if (structs_.count(callee)) return {nullptr, ""};

                if (!functions_.count(callee)) ThrowTypeError("Call to undefined function '" + callee + "'");
                FuncSig& sig = functions_[callee];

                std::vector<llvm::Value*> argsV;
                if (!EvoParser::isNull(exprArr[2])) {
                    auto argsArr = ctx_.getArrayElements(exprArr[2]);

                    if (!sig.isVarArg && argsArr.size != sig.argTypes.size()) ThrowTypeError("Function '" + callee + "' expects " + std::to_string(sig.argTypes.size()) + " arguments, but got " + std::to_string(argsArr.size));

                    for (size_t i = 0; i < argsArr.size; ++i) {
                        TypedValue arg = compileExpression(argsArr[i]);
                        // FEATURE: Polymorphism — allow subclass upcasts at
                        // the call boundary so `func f(a: Animal)` accepts a
                        // Dog without an explicit cast.
                        if (i < sig.argTypes.size()
                            && arg.type != sig.argTypes[i]
                            && !isSubclass(arg.type, sig.argTypes[i])) {
                            ThrowTypeError("Argument " + std::to_string(i+1) + " of '" + callee + "' expected '" + sig.argTypes[i] + "', got '" + arg.type + "'");
                        }
                        argsV.push_back(arg.val);
                    }
                }
                llvm::Function* calleeF = module_->getFunction(callee);
                return {builder_->CreateCall(calleeF, argsV), sig.retType};
            }
            else {
                auto targetArr = ctx_.getArrayElements(targetNode);
                if (EvoParser::toString(targetArr[0]) == "MemberAccess") {
                    std::string baseName = std::string(EvoParser::toString(targetArr[1]));
                    std::string methodName = std::string(EvoParser::toString(targetArr[2]));

                    auto var = lookupVar(baseName);
                    if (!var) ThrowTypeError("Unknown variable '" + baseName + "'");

                    auto sIt = structs_.find(var->typeName);
                    if (sIt == structs_.end()) ThrowTypeError("Type '" + var->typeName + "' has no method '" + methodName + "'");
                    StructInfo& info = sIt->second;

                    llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
                    llvm::Value* selfArg = var->alloca;
                    if (info.isReferenceType) {
                        selfArg = builder_->CreateLoad(ptrTy, selfArg);
                        // FEATURE: ARC — callees release their `self` at
                        // scope exit (popScope), so retain before the call
                        // to keep ref counts balanced across the boundary.
                        builder_->CreateCall(module_->getFunction("elegant_retain"), {selfArg});
                    }

                    llvm::Value* funcPtr = nullptr;
                    llvm::FunctionType* fTy = nullptr;
                    FuncSig sig;

                    if (info.isReferenceType) {
                        // FEATURE: Polymorphism — dynamic method dispatch.
                        // Chase the VTable pointer at slot 0 of the object,
                        // then index into it to pull out the final (possibly
                        // overridden) function pointer. The actual callee is
                        // chosen by runtime type, not the declared type.
                        auto vIt = info.vtableIndices.find(methodName);
                        if (vIt == info.vtableIndices.end()) {
                            ThrowTypeError("Type '" + var->typeName + "' has no method '" + methodName + "'");
                        }
                        unsigned vIdx = vIt->second;

                        llvm::Value* vptrAddr = builder_->CreateStructGEP(info.type, selfArg, 0);
                        llvm::Value* vptr     = builder_->CreateLoad(ptrTy, vptrAddr);
                        llvm::Value* funcPtrAddr = builder_->CreateStructGEP(info.vtableType, vptr, vIdx);
                        funcPtr = builder_->CreateLoad(ptrTy, funcPtrAddr);

                        const std::string& mangledName = info.vtableMethods[vIdx];
                        auto fIt = functions_.find(mangledName);
                        if (fIt == functions_.end()) ThrowTypeError("Missing signature for '" + mangledName + "'");
                        sig = fIt->second;
                    } else {
                        // Static dispatch for value-type structs.
                        std::string mangledName = var->typeName + "_" + methodName;
                        auto fIt = functions_.find(mangledName);
                        if (fIt == functions_.end()) ThrowTypeError("Type '" + var->typeName + "' has no method '" + methodName + "'");
                        sig = fIt->second;
                        funcPtr = module_->getFunction(mangledName);
                    }

                    std::vector<llvm::Type*> argTys;
                    argTys.reserve(sig.argTypes.size());
                    for (const auto& t : sig.argTypes) argTys.push_back(getLLVMType(t));
                    fTy = llvm::FunctionType::get(getLLVMType(sig.retType), argTys, sig.isVarArg);

                    std::vector<llvm::Value*> argsV;
                    argsV.push_back(selfArg);

                    if (!EvoParser::isNull(exprArr[2])) {
                        auto argsArr = ctx_.getArrayElements(exprArr[2]);
                        for (size_t i = 0; i < argsArr.size; ++i) {
                            TypedValue arg = compileExpression(argsArr[i]);
                            // i+1 because sig.argTypes[0] is 'self'
                            if (i + 1 < sig.argTypes.size()
                                && arg.type != sig.argTypes[i+1]
                                && !isSubclass(arg.type, sig.argTypes[i+1])) {
                                ThrowTypeError("Method argument type mismatch.");
                            }
                            argsV.push_back(arg.val);
                        }
                    }
                    return {builder_->CreateCall(fTy, funcPtr, argsV), sig.retType};
                }
            }
        }

        if (nodeType == "Binary") {
            std::string op = std::string(EvoParser::toString(exprArr[1]));
            TypedValue L = compileExpression(exprArr[2]);
            TypedValue R = compileExpression(exprArr[3]);

            if (L.type != R.type) ThrowTypeError("Operator '" + op + "' cannot be applied to types '" + L.type + "' and '" + R.type + "'");
            if (L.type != "Int") ThrowTypeError("Mathematical operators only support 'Int' currently.");

            if (op == "+") return {builder_->CreateAdd(L.val, R.val), "Int"};
            if (op == "-") return {builder_->CreateSub(L.val, R.val), "Int"};
            if (op == "*") return {builder_->CreateMul(L.val, R.val), "Int"};
            if (op == "/") return {builder_->CreateSDiv(L.val, R.val), "Int"};

            llvm::Value* cmp = nullptr;
            if (op == "==") cmp = builder_->CreateICmpEQ(L.val, R.val);
            if (op == "!=") cmp = builder_->CreateICmpNE(L.val, R.val);
            if (op == "<")  cmp = builder_->CreateICmpSLT(L.val, R.val);
            if (op == ">")  cmp = builder_->CreateICmpSGT(L.val, R.val);
            if (op == "<=") cmp = builder_->CreateICmpSLE(L.val, R.val);
            if (op == ">=") cmp = builder_->CreateICmpSGE(L.val, R.val);

            if (cmp) return {builder_->CreateZExt(cmp, llvm::Type::getInt32Ty(*context_)), "Bool"};
        }
        return {nullptr, ""};
    }
};
}

#include <stdio.h>
int main(int argc, char** argv) {
    if (argc < 2) return 1;

    bool compileOnly = false;
    std::string input_file = "";

    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "-c") compileOnly = true;
        else input_file = arg;
    }

    std::ifstream ifs(input_file);
    std::ostringstream ss;
    ss << ifs.rdbuf();
    std::string source = ss.str();

    EvoParser::Parser parser;
    EvoParser::ParseContext ctx;
    EvoParser::ParseError err;

    if (!parser.try_parse(source, ctx, err)) {
        std::cerr << "\n\xE2\x9D\x8C  Syntax Error\n" << err.what() << "\n";
        return 1;
    }

    std::string moduleName = std::filesystem::path(input_file).stem().string();
    Elegant::LLVMCompiler compiler(ctx, moduleName);

    compiler.compile();

    if (!compileOnly) {
        compiler.dumpIR();
        return compiler.executeJIT();
    } else {
        std::string obj_file = moduleName + ".obj";
        std::string exe_file = moduleName + ".exe";

        if (compiler.emitObjectFile(obj_file)) {
            std::cout << "\xE2\x9C\x85 Emitted native object: " << obj_file << "\n";
            std::string linkCmd = "lld-link.exe " + obj_file + " /entry:main /subsystem:console /out:" + exe_file + " /defaultlib:msvcrt.lib /defaultlib:ucrt.lib /defaultlib:kernel32.lib";
            std::system(linkCmd.c_str());
        }
    }
    return 0;
}
