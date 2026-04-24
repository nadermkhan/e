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
#include <set>

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
    // FEATURE: Static Dispatch — static methods don't receive an implicit
    // `self` and are not installed into the V-Table.
    bool isStatic = false;
};

class LLVMCompiler {
    // FEATURE: Module Linker — `ctx_` is a mutable pointer so `compileAST`
    // can swap the active parse context when recursing into an imported
    // file. Every AST node carries indices into its own arena, so the
    // visitor must use the context the AST was parsed against.
    EvoParser::ParseContext* ctx_;
    std::unique_ptr<llvm::LLVMContext> context_;
    std::unique_ptr<llvm::Module> module_;
    std::unique_ptr<llvm::IRBuilder<>> builder_;

    // FEATURE 3: Lexical Scope Stack
    std::vector<std::unordered_map<std::string, VarInfo>> scopes_;
    std::unordered_map<std::string, StructInfo> structs_;
    std::unordered_map<std::string, FuncSig> functions_;

    // FEATURE: Module Linker — track already-imported files + keep the
    // imported sources and parse contexts alive for the lifetime of the
    // compiler so string-view AST nodes don't dangle.
    std::set<std::string> imported_modules_;
    std::vector<std::unique_ptr<std::string>> module_sources_;
    std::vector<std::unique_ptr<EvoParser::ParseContext>> module_contexts_;

    // FEATURE: Type Alias Registry — `import MathLib as ML` maps the
    // user-visible name `ML` to the real struct name `MathLib` so
    // type lookups and static method calls route transparently.
    std::unordered_map<std::string, std::string> type_aliases_;

    std::string resolveAlias(const std::string& name) {
        auto it = type_aliases_.find(name);
        return it == type_aliases_.end() ? name : it->second;
    }

public:
    LLVMCompiler(EvoParser::ParseContext& ctx, const std::string& moduleName)
        : ctx_(&ctx) {
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
        llvm::Function* releaseF      = module_->getFunction("elegant_release");
        llvm::Function* arrayReleaseF = module_->getFunction("elegant_array_release");
        if (releaseF || arrayReleaseF) {
            // First check whether this scope contains anything we need to
            // release; skip all builder manipulation otherwise so we stay
            // a zero-cost no-op for scopes with only primitives.
            bool hasRefs = false;
            for (auto& [name, var] : scopes_.back()) {
                auto it = structs_.find(var.typeName);
                if (it != structs_.end() && it->second.isReferenceType) { hasRefs = true; break; }
                // FEATURE: CoW Arrays — every Array-typed local drops
                // its ref-count on scope exit so the shared heap buffer
                // + struct are freed once the last binding dies.
                if (var.typeName == "Array") { hasRefs = true; break; }
            }
            if (hasRefs) {
                llvm::BasicBlock* insertBB = builder_->GetInsertBlock();
                if (insertBB) {
                    // Portable "does this block end in a terminator?" check:
                    // LLVM 23's `getTerminator()` asserts (or in release
                    // just returns `InstList.back()` unchecked) on ill-
                    // formed blocks, and older LLVM installs (the MSYS2
                    // UCRT64 toolchain used by the Windows CI) don't
                    // expose `hasTerminator()` or `getTerminatorOrNull()`
                    // at all. `empty()` + `Instruction::isTerminator()`
                    // are stable across every supported LLVM version.
                    bool hasTerm = !insertBB->empty() && insertBB->back().isTerminator();
                    llvm::Instruction* term = hasTerm ? &insertBB->back() : nullptr;
                    llvm::BasicBlock*         savedBB = insertBB;
                    llvm::BasicBlock::iterator savedIt = builder_->GetInsertPoint();
                    if (term) builder_->SetInsertPoint(term);

                    llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
                    for (auto& [name, var] : scopes_.back()) {
                        auto it = structs_.find(var.typeName);
                        if (it != structs_.end() && it->second.isReferenceType) {
                            llvm::Value* objPtr = builder_->CreateLoad(ptrTy, var.alloca);
                            if (releaseF) builder_->CreateCall(releaseF, {objPtr});
                            continue;
                        }
                        if (var.typeName == "Array" && arrayReleaseF) {
                            llvm::Value* arrPtr = builder_->CreateLoad(ptrTy, var.alloca);
                            builder_->CreateCall(arrayReleaseF, {arrPtr});
                        }
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
        // FEATURE: Strict Symbol Hygiene — reject redeclaration within the
        // same local scope. Parameters count, since `compileFunction`
        // registers them into the function's top scope before the body
        // runs. Shadowing across nested scopes is still allowed.
        if (!scopes_.empty() && scopes_.back().count(name)) {
            ThrowTypeError("Invalid redeclaration of variable '" + name + "' in the same scope.");
        }
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

    // FEATURE: Native Heap String Concatenation — expose libc string helpers
    // so the `+` operator on `String` can allocate a fresh buffer with
    // `malloc` and stitch both operands together via `strcpy`/`strcat`.
    llvm::Function* getStrLen() {
        if (auto* F = module_->getFunction("strlen")) return F;
        return llvm::Function::Create(
            llvm::FunctionType::get(llvm::Type::getInt64Ty(*context_), {llvm::PointerType::getUnqual(*context_)}, false),
            llvm::Function::ExternalLinkage, "strlen", module_.get());
    }
    llvm::Function* getStrCpy() {
        if (auto* F = module_->getFunction("strcpy")) return F;
        return llvm::Function::Create(
            llvm::FunctionType::get(llvm::PointerType::getUnqual(*context_), {llvm::PointerType::getUnqual(*context_), llvm::PointerType::getUnqual(*context_)}, false),
            llvm::Function::ExternalLinkage, "strcpy", module_.get());
    }
    llvm::Function* getStrCat() {
        if (auto* F = module_->getFunction("strcat")) return F;
        return llvm::Function::Create(
            llvm::FunctionType::get(llvm::PointerType::getUnqual(*context_), {llvm::PointerType::getUnqual(*context_), llvm::PointerType::getUnqual(*context_)}, false),
            llvm::Function::ExternalLinkage, "strcat", module_.get());
    }

    // FEATURE: Dynamic Array Resizing — expose libc `realloc` so `append`
    // can grow a Swift-style Array's heap buffer when it runs out of
    // capacity, without copying or manually re-allocating the struct.
    llvm::Function* getRealloc() {
        if (auto* F = module_->getFunction("realloc")) return F;
        return llvm::Function::Create(
            llvm::FunctionType::get(llvm::PointerType::getUnqual(*context_), {llvm::PointerType::getUnqual(*context_), llvm::Type::getInt64Ty(*context_)}, false),
            llvm::Function::ExternalLinkage, "realloc", module_.get());
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
        // Idempotent — the Module Linker's `compileAST` may run multiple
        // times across imported files, and we only want one copy of the
        // retain/release runtime in the LLVM module.
        if (module_->getFunction("elegant_retain")) return;

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

        auto members = ctx_->getArrayElements(info.astMembers);
        for (const auto& mem : members) {
            auto memArr = ctx_->getArrayElements(mem);
            if (memArr.size == 0) continue;
            std::string_view kind = EvoParser::toString(memArr[0]);

            if (kind == "Property") {
                std::string propName = std::string(EvoParser::toString(memArr[2]));
                std::string propType = EvoParser::isNull(memArr[3]) ? "Int" : std::string(EvoParser::toString(memArr[3]));
                info.fieldIndices[propName] = fieldIdx++;
                info.fieldTypes.push_back(getLLVMType(propType));
                info.fieldTypesString[propName] = propType;
            }
            else if (kind == "Function" || kind == "StaticFunction") {
                // FEATURE: Static Dispatch — static methods never occupy a
                // V-Table slot (there is no instance to dispatch through).
                bool isStaticMethod = (kind == "StaticFunction");

                // Only reference types carry a V-Table; value-type structs
                // keep static dispatch.
                if (isStaticMethod || !info.isReferenceType) continue;

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

    // FEATURE: Swift-style Arrays are value types backed by a heap
    // allocation. The layout is { i32 capacity, i32 count, i8* buffer,
    // i32 ref_count } — the trailing ref_count slot was added so
    // assignments can implement Copy-on-Write (CoW) value semantics:
    // multiple live bindings share the same struct + buffer until a
    // mutation forces a private clone. Slot order is preserved to keep
    // subscript/append lowerings unchanged (both read slots 0..2 by
    // positional index).
    llvm::StructType* getSwiftArrayType() {
        if (auto* T = llvm::StructType::getTypeByName(*context_, "SwiftArray")) return T;
        auto* T = llvm::StructType::create(*context_, "SwiftArray");
        T->setBody({
            llvm::Type::getInt32Ty(*context_),
            llvm::Type::getInt32Ty(*context_),
            llvm::PointerType::getUnqual(*context_),
            llvm::Type::getInt32Ty(*context_)
        });
        return T;
    }

    // FEATURE: First-Class Closures — a closure value is a "Thick Pointer"
    // aggregate of { i8* instruction_ptr, i8* context_ptr }. The context
    // pointer addresses a heap-allocated struct containing every variable
    // captured from the surrounding lexical scope. This struct type is
    // reused for every closure so `ClosureType`-tagged values share one
    // ABI and can flow through variables, parameters, and return values.
    llvm::StructType* getThickPointerType() {
        if (auto* T = llvm::StructType::getTypeByName(*context_, "ThickPointer")) return T;
        auto* T = llvm::StructType::create(*context_, "ThickPointer");
        T->setBody({
            llvm::PointerType::getUnqual(*context_),
            llvm::PointerType::getUnqual(*context_)
        });
        return T;
    }

    // FEATURE: Copy-on-Write (CoW) Arrays — expose libc `memcpy` so the
    // CoW clone path can duplicate the backing buffer in one call.
    llvm::Function* getMemcpy() {
        if (auto* F = module_->getFunction("memcpy")) return F;
        llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
        llvm::Type* i64Ty = llvm::Type::getInt64Ty(*context_);
        return llvm::Function::Create(
            llvm::FunctionType::get(ptrTy, {ptrTy, ptrTy, i64Ty}, false),
            llvm::Function::ExternalLinkage, "memcpy", module_.get());
    }

    // FEATURE: CoW Arrays — emit the ref-count helpers for SwiftArray.
    // `elegant_array_retain` increments slot 3 (ref_count); the matching
    // `elegant_array_release` decrements it and, when the count reaches
    // zero, frees both the backing buffer (slot 2) and the struct itself.
    void buildArrayARCFunctions() {
        if (module_->getFunction("elegant_array_retain")) return;

        llvm::Type* voidTy = llvm::Type::getVoidTy(*context_);
        llvm::Type* ptrTy  = llvm::PointerType::getUnqual(*context_);
        llvm::Type* i32Ty  = llvm::Type::getInt32Ty(*context_);
        llvm::StructType* arrTy = getSwiftArrayType();

        {
            auto* ft = llvm::FunctionType::get(voidTy, {ptrTy}, false);
            auto* retainF = llvm::Function::Create(ft, llvm::Function::InternalLinkage, "elegant_array_retain", module_.get());
            auto* bb = llvm::BasicBlock::Create(*context_, "entry", retainF);
            llvm::IRBuilder<> B(bb);

            llvm::Value* arrObj = retainF->getArg(0);
            llvm::Value* isNull = B.CreateICmpEQ(arrObj, llvm::ConstantPointerNull::get(llvm::cast<llvm::PointerType>(ptrTy)));
            llvm::BasicBlock* nullBB = llvm::BasicBlock::Create(*context_, "null", retainF);
            llvm::BasicBlock* bumpBB = llvm::BasicBlock::Create(*context_, "bump", retainF);
            B.CreateCondBr(isNull, nullBB, bumpBB);

            B.SetInsertPoint(nullBB);
            B.CreateRetVoid();

            B.SetInsertPoint(bumpBB);
            llvm::Value* refPtr = B.CreateStructGEP(arrTy, arrObj, 3);
            llvm::Value* count  = B.CreateLoad(i32Ty, refPtr);
            llvm::Value* incd   = B.CreateAdd(count, llvm::ConstantInt::get(i32Ty, 1));
            B.CreateStore(incd, refPtr);
            B.CreateRetVoid();
        }

        {
            auto* ft = llvm::FunctionType::get(voidTy, {ptrTy}, false);
            auto* releaseF = llvm::Function::Create(ft, llvm::Function::InternalLinkage, "elegant_array_release", module_.get());
            auto* entryBB = llvm::BasicBlock::Create(*context_, "entry",   releaseF);
            auto* dropBB  = llvm::BasicBlock::Create(*context_, "drop",    releaseF);
            auto* freeBB  = llvm::BasicBlock::Create(*context_, "free_it", releaseF);
            auto* contBB  = llvm::BasicBlock::Create(*context_, "cont",    releaseF);
            llvm::IRBuilder<> B(entryBB);

            llvm::Value* arrObj = releaseF->getArg(0);
            llvm::Value* isNull = B.CreateICmpEQ(arrObj, llvm::ConstantPointerNull::get(llvm::cast<llvm::PointerType>(ptrTy)));
            B.CreateCondBr(isNull, contBB, dropBB);

            B.SetInsertPoint(dropBB);
            llvm::Value* refPtr = B.CreateStructGEP(arrTy, arrObj, 3);
            llvm::Value* count  = B.CreateLoad(i32Ty, refPtr);
            llvm::Value* decd   = B.CreateSub(count, llvm::ConstantInt::get(i32Ty, 1));
            B.CreateStore(decd, refPtr);
            llvm::Value* isZero = B.CreateICmpSLE(decd, llvm::ConstantInt::get(i32Ty, 0));
            B.CreateCondBr(isZero, freeBB, contBB);

            B.SetInsertPoint(freeBB);
            // Free the backing buffer first, then the struct header itself.
            llvm::Value* bufPtrAddr = B.CreateStructGEP(arrTy, arrObj, 2);
            llvm::Value* buffer     = B.CreateLoad(ptrTy, bufPtrAddr);
            B.CreateCall(getFree(), {buffer});
            B.CreateCall(getFree(), {arrObj});
            B.CreateBr(contBB);

            B.SetInsertPoint(contBB);
            B.CreateRetVoid();
        }
    }

    // FEATURE: Dynamic Tagged Unions for Optionals. A type ending in `?`
    // lowers to `{ i1 is_valid, T data }` — a standard Swift-style Optional
    // struct. Implicitly-unwrapped `T!` is treated identically at the storage
    // level; the force-unwrap runtime check is what makes them different.
    llvm::Type* getLLVMType(const std::string& typeName) {
        // FEATURE: First-Class Closures — a ClosureType value lowers to a
        // Thick Pointer aggregate carrying both the instruction pointer
        // and the heap-allocated capture context. We keep raw function
        // pointers (`(T)->R`) lowered to `i8*` so existing first-class
        // function references and FFI bindings (e.g. `_beginthread`)
        // retain their single-pointer ABI.
        if (typeName == "ClosureType" || typeName == "Closure") {
            return getThickPointerType();
        }
        // FEATURE: First-Class Function Pointers. Any type annotation that
        // contains `->` is a function signature (e.g. `(Int)->Void`). At
        // the LLVM level we lower it to a raw opaque pointer — a CPU
        // instruction pointer — so functions can flow through local
        // variables, parameters, and return values like any other value.
        if (typeName.find("->") != std::string::npos) {
            return llvm::PointerType::getUnqual(*context_);
        }

        if (!typeName.empty() && (typeName.back() == '?' || typeName.back() == '!')) {
            std::string baseType = typeName.substr(0, typeName.length() - 1);
            llvm::Type* innerTy = getLLVMType(baseType);
            return llvm::StructType::get(*context_, {llvm::Type::getInt1Ty(*context_), innerTy});
        }

        // FEATURE: Standard Library Types — `Bool` is lowered to `i32` under
        // the hood so it can flow through the existing Int-shaped code paths
        // (comparisons, conditionals, parameter passing) without special
        // casing. `true` is `1`, `false` is `0`.
        if (typeName == "Int" || typeName == "Bool") return llvm::Type::getInt32Ty(*context_);
        if (typeName == "Float") return llvm::Type::getDoubleTy(*context_);
        if (typeName == "String") return llvm::PointerType::getUnqual(*context_);
        if (typeName == "Array") return llvm::PointerType::getUnqual(*context_);
        if (typeName == "Void" || typeName == "") return llvm::Type::getVoidTy(*context_);

        std::string resolvedType = resolveAlias(typeName);
        if (structs_.count(resolvedType)) {
            if (structs_[resolvedType].isReferenceType) return llvm::PointerType::getUnqual(*context_);
            else return structs_[resolvedType].type;
        }
        return llvm::Type::getInt32Ty(*context_);
    }

    // FEATURE: Module Linker — public entry point. Emits the ARC runtime
    // once, recursively compiles the root file (and anything it imports),
    // then finalises every V-Table global in a single pass at the end so
    // imported classes pick up the fully-populated method tables.
    void compile() {
        buildARCFunctions();
        // FEATURE: CoW Arrays — emit the array-specific retain/release
        // helpers alongside the class-level ARC runtime so assignments
        // and scope exits can bump / drop ref counts on heap-backed
        // SwiftArray value types.
        buildArrayARCFunctions();
        compileAST(*ctx_, ctx_->root);

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

    void compileAST(EvoParser::ParseContext& currentCtx, const EvoParser::Value& astRoot) {
        // FEATURE: Module Linker — swap the active parse context for the
        // duration of this call. Recursive `compileAST` invocations for
        // imported files each set `ctx_` to their own context on entry
        // and restore it on exit, so AST traversals in nested passes
        // always see the arena the AST was actually parsed against.
        EvoParser::ParseContext* savedCtx = ctx_;
        ctx_ = &currentCtx;

        auto declarations = ctx_->getArrayElements(astRoot);

        // Pass 1: Type & Signature Registration (plus Module Imports).
        for (const auto& declVal : declarations) {
            auto declArr = ctx_->getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);

            // FEATURE: Module Linker — the `import Foo` statement loads
            // `Foo.ele` from disk, parses it, and recursively runs the full
            // compile pipeline on the sub-AST. Classes, static functions,
            // and globals from the imported file are merged into the
            // active `structs_` / `functions_` tables before this file's
            // own Pass 2/3 runs, so forward references Just Work.
            if (nodeType == "Import") {
                std::string pkgName = std::string(EvoParser::toString(declArr[1]));

                // FEATURE: `as` alias keyword — `import MathLib as ML`
                // routes lookups of `ML` to the real struct name `MathLib`.
                if (declArr.size > 2 && !EvoParser::isNull(declArr[2])) {
                    auto aliasArr = ctx_->getArrayElements(declArr[2]);
                    if (aliasArr.size > 0) {
                        // The sub-group captures `("as" _ Identifier)`;
                        // we only care about the Identifier in slot 2.
                        std::string alias = std::string(EvoParser::toString(aliasArr[aliasArr.size - 1]));
                        if (type_aliases_.count(alias) || structs_.count(alias)) {
                            ThrowTypeError("Alias collision: The name '" + alias + "' is already in use.");
                        }
                        type_aliases_[alias] = pkgName; // Map ML -> MathLib
                    }
                }

                // Prevent infinite import cycles.
                if (imported_modules_.count(pkgName)) continue;
                imported_modules_.insert(pkgName);

                std::string filename = pkgName + ".ele";
                std::ifstream ifs(filename);
                if (!ifs) ThrowTypeError("Module Linker Error: Cannot find file '" + filename + "'");

                auto sourceStr = std::make_unique<std::string>(std::string(std::istreambuf_iterator<char>(ifs), {}));
                module_sources_.push_back(std::move(sourceStr));

                auto subCtx = std::make_unique<EvoParser::ParseContext>();
                EvoParser::Parser parser;
                EvoParser::ParseError importErr;

                if (!parser.try_parse(*module_sources_.back(), *subCtx, importErr)) {
                    ThrowTypeError("Syntax error in imported module '" + pkgName + "':\n" + importErr.what());
                }

                // Recursion: suspend current file, compile the import,
                // then resume. compileAST saves/restores `ctx_` on its own.
                compileAST(*subCtx, subCtx->root);

                module_contexts_.push_back(std::move(subCtx));
                continue;
            }

            if (nodeType == "Class" || nodeType == "Struct") {
                std::string name = std::string(EvoParser::toString(declArr[1]));

                // FEATURE: Strict Symbol Hygiene — reject duplicate global
                // type declarations across the whole module (including
                // imported files).
                if (structs_.count(name)) ThrowTypeError("Invalid redeclaration of Type '" + name + "'.");
                if (type_aliases_.count(name)) ThrowTypeError("Type '" + name + "' collides with an existing import alias.");

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
                        auto supArr = ctx_->getArrayElements(supVal);
                        if (supArr.size > 0) {
                            info.superclass = std::string(EvoParser::toString(supArr[0]));
                        }
                    }
                }

                // Register method signatures so Pass 3 can typecheck calls.
                for (const auto& mem : ctx_->getArrayElements(info.astMembers)) {
                    auto memArr = ctx_->getArrayElements(mem);
                    if (memArr.size == 0) continue;
                    std::string_view kind = EvoParser::toString(memArr[0]);
                    if (kind != "Function" && kind != "StaticFunction") continue;

                    bool isStaticMethod = (kind == "StaticFunction");
                    std::string mName = name + "_" + std::string(EvoParser::toString(memArr[1]));
                    FuncSig sig;
                    sig.isStatic = isStaticMethod;
                    // Only instance methods get the implicit `self`.
                    if (!isStaticMethod) sig.argTypes.push_back(name);
                    if (!EvoParser::isNull(memArr[2])) {
                        for (const auto& param : ctx_->getArrayElements(memArr[2])) {
                            sig.argTypes.push_back(std::string(EvoParser::toString(ctx_->getArrayElements(param)[2])));
                        }
                    }
                    sig.retType = EvoParser::isNull(memArr[3]) ? "Void" : std::string(EvoParser::toString(memArr[3]));
                    functions_[mName] = sig;
                }
            }
            else if (nodeType == "Extern") {
                std::string extName = std::string(EvoParser::toString(declArr[1]));

                // The Prelude declares a handful of externs (printf, exit,
                // sqrt, ...) that user scripts are still free to declare
                // themselves. Swallow duplicate registrations so `extern
                // func printf` in user code doesn't collide with the
                // prelude-injected declaration (or with a previously
                // emitted intrinsic like `getPrintf`'s shim).
                if (functions_.count(extName)) continue;

                FuncSig sig;
                std::vector<llvm::Type*> argTypes;

                if (!EvoParser::isNull(declArr[2])) {
                    auto paramsArr = ctx_->getArrayElements(declArr[2]);
                    for (const auto& param : paramsArr) {
                        auto p = ctx_->getArrayElements(param);
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

                if (!module_->getFunction(extName)) {
                    llvm::FunctionType* ft = llvm::FunctionType::get(getLLVMType(sig.retType), argTypes, sig.isVarArg);
                    llvm::Function::Create(ft, llvm::Function::ExternalLinkage, extName, module_.get());
                }
            }
        }

        // Pass 2a: Register top-level function signatures (Pass 1 handled
        // methods, structs, classes and externs already).
        for (const auto& declVal : declarations) {
            auto declArr = ctx_->getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);

            if (nodeType == "Function") {
                std::string name = std::string(EvoParser::toString(declArr[1]));

                // FEATURE: Strict Symbol Hygiene — global function
                // collision check spanning every imported file.
                if (functions_.count(name)) ThrowTypeError("Invalid redeclaration of Global Function '" + name + "'.");

                FuncSig sig;
                if (!EvoParser::isNull(declArr[2])) {
                    for (const auto& param : ctx_->getArrayElements(declArr[2])) {
                        sig.argTypes.push_back(std::string(EvoParser::toString(ctx_->getArrayElements(param)[2])));
                    }
                }
                sig.retType = EvoParser::isNull(declArr[3]) ? "Void" : std::string(EvoParser::toString(declArr[3]));
                functions_[name] = sig;
            }
        }

        // Pass 2b: Resolve class/struct memory layouts recursively so parent
        // classes are laid out before their children.
        for (const auto& declVal : declarations) {
            auto declArr = ctx_->getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);
            if (nodeType == "Class" || nodeType == "Struct") {
                resolveLayout(std::string(EvoParser::toString(declArr[1])));
            }
        }

        // Pass 3: Code Generation
        pushScope(); // Global scope
        for (const auto& declVal : declarations) {
            auto declArr = ctx_->getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);

            if (nodeType == "Function") {
                compileFunction(declArr, "", nullptr);
            } else if (nodeType == "Class" || nodeType == "Struct") {
                std::string className = std::string(EvoParser::toString(declArr[1]));
                auto members = ctx_->getArrayElements(declArr[3]);
                for (const auto& mem : members) {
                    auto memArr = ctx_->getArrayElements(mem);
                    std::string_view memKind = EvoParser::toString(memArr[0]);
                    if (memKind == "Function" || memKind == "StaticFunction") {
                        compileFunction(memArr, className, structs_[className].type);
                    }
                }
            }
        }
        popScope();

        // Restore the caller's active parse context. V-Table globals are
        // finalised in the outer `compile()` wrapper after every module
        // has been merged into `structs_`.
        ctx_ = savedCtx;
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

    // FEATURE: First-Class Closures — walk a closure body AST and collect
    // the names of every outer-scope variable it references. `params` is
    // the set of identifiers bound by the closure's parameter list; any
    // identifier in the body that matches a binding in an enclosing scope
    // AND isn't a parameter gets recorded for capture. Locals declared
    // inside the closure body (via `var`/`let`) shadow the outer binding
    // and are also excluded.
    void collectClosureCaptures(const EvoParser::Value& node,
                                std::set<std::string>& params,
                                std::set<std::string>& localDecls,
                                std::vector<std::string>& captures,
                                std::set<std::string>& seen) {
        if (node.type == EvoParser::ValueType::StringView) {
            std::string name = std::string(EvoParser::toString(node));
            if (name.empty()) return;
            if (params.count(name) || localDecls.count(name)) return;
            if (lookupVar(name) == nullptr) return;
            if (seen.insert(name).second) captures.push_back(name);
            return;
        }
        if (node.type != EvoParser::ValueType::Array) return;

        auto arr = ctx_->getArrayElements(node);
        if (arr.size == 0) return;

        // When the head is a tag we recognise, dispatch by shape so we
        // skip positions that aren't variable references (e.g. the `op`
        // field on a Binary node, the method name on a MemberAccess, a
        // string literal payload). Everything we don't explicitly carve
        // out falls through to a generic recursion over all children.
        if (arr[0].type == EvoParser::ValueType::StringView) {
            std::string_view head = EvoParser::toString(arr[0]);

            if (head == "String" || head == "Int" || head == "Float" ||
                head == "Bool"   || head == "Nil") {
                return;
            }
            if (head == "Property") {
                // Property declaration inside the closure body:
                // stmtArr = [ "Property", mutability, name, type, init ]
                if (arr.size >= 3 && arr[2].type == EvoParser::ValueType::StringView) {
                    localDecls.insert(std::string(EvoParser::toString(arr[2])));
                }
                if (arr.size >= 5) {
                    collectClosureCaptures(arr[4], params, localDecls, captures, seen);
                }
                return;
            }
            if (head == "For") {
                // For loop: [ "For", varName, start, end, body ]
                if (arr.size >= 5) {
                    collectClosureCaptures(arr[2], params, localDecls, captures, seen);
                    collectClosureCaptures(arr[3], params, localDecls, captures, seen);
                    std::set<std::string> innerDecls = localDecls;
                    if (arr[1].type == EvoParser::ValueType::StringView) {
                        innerDecls.insert(std::string(EvoParser::toString(arr[1])));
                    }
                    collectClosureCaptures(arr[4], params, innerDecls, captures, seen);
                }
                return;
            }
            if (head == "MemberAccess") {
                // [ "MemberAccess", base, prop ] — prop isn't a variable.
                if (arr.size >= 2) {
                    collectClosureCaptures(arr[1], params, localDecls, captures, seen);
                }
                return;
            }
            if (head == "SelfAccess") {
                return;
            }
            if (head == "Binary") {
                // [ "Binary", op, left, right ] — op is a string, not a var.
                if (arr.size >= 4) {
                    collectClosureCaptures(arr[2], params, localDecls, captures, seen);
                    collectClosureCaptures(arr[3], params, localDecls, captures, seen);
                }
                return;
            }
            if (head == "Unary") {
                // [ "Unary", op, expr ] — op is a string.
                if (arr.size >= 3) {
                    collectClosureCaptures(arr[2], params, localDecls, captures, seen);
                }
                return;
            }
            if (head == "Assign") {
                // [ "Assign", op, target, val ] — op is a string.
                if (arr.size >= 4) {
                    collectClosureCaptures(arr[2], params, localDecls, captures, seen);
                    collectClosureCaptures(arr[3], params, localDecls, captures, seen);
                }
                return;
            }
            if (head == "Call") {
                // [ "Call", target, args ] — if target is a bare identifier
                // naming a top-level function, it's not a variable capture.
                if (arr.size >= 2) {
                    if (arr[1].type == EvoParser::ValueType::StringView) {
                        std::string tgt = std::string(EvoParser::toString(arr[1]));
                        if (!functions_.count(tgt) && !structs_.count(tgt)) {
                            collectClosureCaptures(arr[1], params, localDecls, captures, seen);
                        }
                    } else {
                        collectClosureCaptures(arr[1], params, localDecls, captures, seen);
                    }
                }
                if (arr.size >= 3) {
                    collectClosureCaptures(arr[2], params, localDecls, captures, seen);
                }
                return;
            }
        }

        for (size_t i = 0; i < arr.size; ++i) {
            collectClosureCaptures(arr[i], params, localDecls, captures, seen);
        }
    }

    // FEATURE: First-Class Closures — lower a `{ x, y in body }` AST to a
    // Thick Pointer value. The generated LLVM function takes an implicit
    // leading `i8*` context parameter (the heap-allocated capture struct)
    // plus the user's declared parameters. Inside the body the captured
    // variables are unpacked into local allocas so the rest of the
    // compiler's lowering machinery treats them exactly like ordinary
    // locals. The returned TypedValue carries the `{fn, ctx}` aggregate
    // along with a `"Closure"` type tag that downstream call sites use to
    // pick the thick-pointer calling convention.
    TypedValue compileClosure(const EvoParser::ArrayView& closureAst) {
        llvm::BasicBlock* savedBB      = builder_->GetInsertBlock();
        llvm::BasicBlock::iterator savedIt = builder_->GetInsertPoint();

        // Collect explicit parameter names. The grammar emits either Null
        // (no params) or an Array<Identifier>.
        std::vector<std::string> paramNames;
        if (closureAst.size > 1 && !EvoParser::isNull(closureAst[1])) {
            auto paramsView = ctx_->getArrayElements(closureAst[1]);
            for (size_t i = 0; i < paramsView.size; ++i) {
                paramNames.push_back(std::string(EvoParser::toString(paramsView[i])));
            }
        }

        // Walk the body and collect names referenced in the body that
        // resolve to an enclosing-scope local (and aren't closure params
        // or inside-the-closure `var` declarations).
        std::vector<std::string> captureNames;
        {
            std::set<std::string> paramSet(paramNames.begin(), paramNames.end());
            std::set<std::string> localDecls;
            std::set<std::string> seen;
            if (closureAst.size > 2 && !EvoParser::isNull(closureAst[2])) {
                auto bodyView = ctx_->getArrayElements(closureAst[2]);
                for (size_t i = 0; i < bodyView.size; ++i) {
                    collectClosureCaptures(bodyView[i], paramSet, localDecls, captureNames, seen);
                }
            }
        }

        // Build the context struct type from the captured variables'
        // current LLVM types.
        llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
        llvm::Type* i64Ty = llvm::Type::getInt64Ty(*context_);
        std::vector<llvm::Type*> ctxTypes;
        std::vector<std::string> ctxTypeNames;
        ctxTypes.reserve(captureNames.size());
        ctxTypeNames.reserve(captureNames.size());
        for (const auto& name : captureNames) {
            VarInfo* var = lookupVar(name);
            ctxTypeNames.push_back(var->typeName);
            ctxTypes.push_back(getLLVMType(var->typeName));
        }

        llvm::StructType* ctxType = llvm::StructType::get(*context_, ctxTypes);

        // Allocate the context struct on the heap so it outlives the
        // current lexical scope. An empty capture set still gets a
        // 1-byte malloc so the thick pointer's context slot is always a
        // valid heap pointer (or null for truly no-capture closures).
        llvm::Value* ctxHeapPtr;
        if (captureNames.empty()) {
            ctxHeapPtr = llvm::ConstantPointerNull::get(llvm::cast<llvm::PointerType>(ptrTy));
        } else {
            uint64_t ctxSize = module_->getDataLayout().getTypeAllocSize(ctxType);
            ctxHeapPtr = builder_->CreateCall(
                getMalloc(),
                {llvm::ConstantInt::get(i64Ty, ctxSize)});

            // Populate the context by loading each captured variable out
            // of its alloca and storing it into the matching struct slot.
            for (size_t i = 0; i < captureNames.size(); ++i) {
                VarInfo* var = lookupVar(captureNames[i]);
                llvm::Value* loaded = builder_->CreateLoad(ctxTypes[i], var->alloca);
                llvm::Value* slotPtr = builder_->CreateStructGEP(ctxType, ctxHeapPtr, i);
                builder_->CreateStore(loaded, slotPtr);
            }
        }

        // Build the closure's function type: leading i8* context + one i32
        // Int per explicit parameter (for the initial release we restrict
        // closure parameters to `Int` — the same restriction the rest of
        // the array/loop code applies to user-defined first-class values).
        std::vector<llvm::Type*> closureArgTypes;
        closureArgTypes.push_back(ptrTy);
        for (size_t i = 0; i < paramNames.size(); ++i) {
            closureArgTypes.push_back(llvm::Type::getInt32Ty(*context_));
        }

        llvm::FunctionType* ft = llvm::FunctionType::get(
            llvm::Type::getVoidTy(*context_),
            closureArgTypes,
            false);

        static unsigned closureSeq = 0;
        std::string closureName = "elegant_closure_" + std::to_string(closureSeq++);
        llvm::Function* closureFunc = llvm::Function::Create(
            ft,
            llvm::Function::InternalLinkage,
            closureName,
            module_.get());

        // Emit the closure body against a fresh scope. We stash away the
        // outer scopes on the side so the closure's body can't
        // accidentally reach into its caller's locals through
        // `lookupVar` — every capture has to go through the explicit
        // context struct above.
        std::vector<std::unordered_map<std::string, VarInfo>> savedScopes;
        savedScopes.swap(scopes_);

        llvm::BasicBlock* bodyBB = llvm::BasicBlock::Create(*context_, "entry", closureFunc);
        builder_->SetInsertPoint(bodyBB);
        pushScope();

        // Unpack captures: for each captured variable create a local
        // alloca and populate it from the context struct slot. The rest
        // of compileExpression/compileStatement then treats them as
        // ordinary locals with the captured value snapshot at closure
        // creation time (Swift's default `let`-style capture semantics).
        llvm::Value* contextArg = closureFunc->getArg(0);
        if (!captureNames.empty()) {
            for (size_t i = 0; i < captureNames.size(); ++i) {
                llvm::Value* slotPtr = builder_->CreateStructGEP(ctxType, contextArg, i);
                llvm::Value* loaded  = builder_->CreateLoad(ctxTypes[i], slotPtr);
                llvm::AllocaInst* a  = CreateEntryBlockAlloca(closureFunc, captureNames[i], ctxTypes[i]);
                builder_->CreateStore(loaded, a);
                defineVar(captureNames[i], {a, ctxTypeNames[i]});
            }
        }

        // Parameter allocas. Each declared closure parameter lands in a
        // fresh `Int` alloca so the body can read/write it like any
        // other local.
        for (size_t i = 0; i < paramNames.size(); ++i) {
            llvm::Value* argVal = closureFunc->getArg(1 + i);
            llvm::AllocaInst* a  = CreateEntryBlockAlloca(closureFunc, paramNames[i], llvm::Type::getInt32Ty(*context_));
            builder_->CreateStore(argVal, a);
            defineVar(paramNames[i], {a, "Int"});
        }

        if (closureAst.size > 2 && !EvoParser::isNull(closureAst[2])) {
            auto bodyView = ctx_->getArrayElements(closureAst[2]);
            for (size_t i = 0; i < bodyView.size; ++i) {
                compileStatement(bodyView[i]);
            }
        }

        // Append an implicit `ret void` if the body didn't provide one.
        {
            llvm::BasicBlock* tailBB = builder_->GetInsertBlock();
            bool tailHasTerm = tailBB && !tailBB->empty() && tailBB->back().isTerminator();
            if (tailBB && !tailHasTerm) builder_->CreateRetVoid();
        }

        popScope();
        savedScopes.swap(scopes_);

        builder_->SetInsertPoint(savedBB, savedIt);

        // Assemble the Thick Pointer aggregate `{fn, ctx}` and hand it
        // back tagged with the special `Closure` type.
        llvm::StructType* thickTy = getThickPointerType();
        llvm::Value* thickPtr = llvm::UndefValue::get(thickTy);
        thickPtr = builder_->CreateInsertValue(thickPtr, closureFunc, 0);
        thickPtr = builder_->CreateInsertValue(thickPtr, ctxHeapPtr, 1);
        return {thickPtr, "Closure"};
    }

    llvm::Function* compileFunction(const EvoParser::ArrayView& funcNode, std::string className, llvm::StructType* classType) {
        std::string name = std::string(EvoParser::toString(funcNode[1]));
        if (!className.empty()) name = className + "_" + name;

        // FEATURE: Static Dispatch — a `static func` declared inside a
        // class does not receive the implicit `self` first argument, and
        // therefore isn't routed through the V-Table.
        bool isStatic = (EvoParser::toString(funcNode[0]) == "StaticFunction");

        std::vector<llvm::Type*> argTypes;
        std::vector<std::string> argNames;

        if (classType && !isStatic) {
            argTypes.push_back(structs_[className].isReferenceType ? llvm::PointerType::getUnqual(*context_) : classType->getPointerTo());
            argNames.push_back("self");
        }

        if (!EvoParser::isNull(funcNode[2])) {
            auto paramsArr = ctx_->getArrayElements(funcNode[2]);
            for (const auto& param : paramsArr) {
                auto p = ctx_->getArrayElements(param);
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

        auto bodyArr = ctx_->getArrayElements(funcNode[4]);
        for (const auto& stmt : bodyArr) compileStatement(stmt);

        popScope();

        // Implicit return if none found. We must check the *current* insert
        // block rather than the entry block so functions whose last statement
        // lowered to a merge block (e.g. a trailing `if`) still get a
        // terminator and pass the IR verifier.
        // Decide whether this function already ends in a terminator. We
        // have to do the check by hand because the LLVM surface area for
        // "does this block have a terminator?" isn't portable across
        // versions: LLVM 23's `getTerminator()` returns `InstList.back()`
        // unchecked in release, and the older MSYS2 LLVM used by the
        // Windows CI lacks both `hasTerminator()` and
        // `getTerminatorOrNull()`. `empty()` + `Instruction::isTerminator()`
        // have been stable since forever, so use those.
        llvm::BasicBlock* tailBB = builder_->GetInsertBlock();
        bool tailHasTerm = tailBB && !tailBB->empty() && tailBB->back().isTerminator();
        if (tailBB && !tailHasTerm) {
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

        auto arr = ctx_->getArrayElements(expr);
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

                // FEATURE: Runtime array bounds checking. Reads the count from
                // the Fat Pointer array header and traps before any GEP that
                // could walk off the buffer. Replaces the C-style silent UB
                // with a clean diagnostic + exit(1).
                llvm::Value* countPtr = builder_->CreateStructGEP(getSwiftArrayType(), arrObj, 1);
                llvm::Value* countVal = builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), countPtr);

                llvm::Value* isNeg = builder_->CreateICmpSLT(indexVal.val, llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), 0));
                llvm::Value* isOut = builder_->CreateICmpSGE(indexVal.val, countVal);
                llvm::Value* isOutOfBounds = builder_->CreateOr(isNeg, isOut);

                llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
                llvm::BasicBlock* PanicBB = llvm::BasicBlock::Create(*context_, "bounds_panic", TheFunction);
                llvm::BasicBlock* ContBB = llvm::BasicBlock::Create(*context_, "bounds_cont", TheFunction);

                builder_->CreateCondBr(isOutOfBounds, PanicBB, ContBB);

                builder_->SetInsertPoint(PanicBB);
                llvm::Value* panicMsg = builder_->CreateGlobalString(
                    "\n\033[31m\xF0\x9F\x9A\xA8 Fatal Error:\033[0m Array index out of bounds!\n",
                    "bounds_panic_msg");
                builder_->CreateCall(getPrintf(), {panicMsg});
                builder_->CreateCall(getExit(), {llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), 1)});
                builder_->CreateUnreachable();

                builder_->SetInsertPoint(ContBB);

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
        auto stmtArr = ctx_->getArrayElements(stmtVal);
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
                    auto rhsArr = ctx_->getArrayElements(rhs);
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
                // FEATURE: CoW Arrays — when a new binding aliases an
                // existing Array value (e.g. `var b = a`), retain the
                // shared struct so the backing buffer + header outlive
                // whichever binding dies first. A fresh array literal
                // already seeds ref_count = 1, so the retain here rides
                // it up to 2 while both locals are live.
                if (varType == "Array") {
                    if (auto* arRetain = module_->getFunction("elegant_array_retain")) {
                        builder_->CreateCall(arRetain, {initVal.val});
                    }
                }
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
            // FEATURE: CoW Arrays — the same retain/release dance for
            // Array rebinds. The outgoing binding drops its share of the
            // shared struct, the incoming binding bumps the ref_count so
            // the two never race on the underlying heap buffer.
            if (lhs.type == "Array" && rhs.type == "Array") {
                llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
                llvm::Value* oldArr = builder_->CreateLoad(ptrTy, lhs.val);
                if (auto* arRel = module_->getFunction("elegant_array_release")) {
                    builder_->CreateCall(arRel, {oldArr});
                }
                if (auto* arRet = module_->getFunction("elegant_array_retain")) {
                    builder_->CreateCall(arRet, {rhs.val});
                }
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
            auto bodyArr = ctx_->getArrayElements(stmtArr[4]);
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
            auto arr = ctx_->getArrayElements(stmtArr[2]);
            for (const auto& s : arr) compileStatement(s);
            popScope();

            builder_->CreateBr(MergeBB);
            TheFunction->insert(TheFunction->end(), MergeBB);
            builder_->SetInsertPoint(MergeBB);
            return;
        }

        compileExpression(stmtVal);
    }

    // FEATURE: First-Class Functions — build the canonical signature
    // string for a named function. This is the textual type that flows
    // through the rest of the type checker whenever a function is used
    // as a value: `(Int,String)->Int`, `()->Void`, etc. Kept space-free
    // so it compares cleanly against parameter annotations captured by
    // the grammar.
    std::string buildFuncSigType(const FuncSig& sig) const {
        std::string s = "(";
        for (size_t i = 0; i < sig.argTypes.size(); ++i) {
            s += sig.argTypes[i];
            if (i + 1 < sig.argTypes.size()) s += ",";
        }
        s += ")->" + sig.retType;
        return s;
    }

    // FEATURE: First-Class Functions — strip ASCII whitespace from a
    // captured function-type annotation so `(Int) -> Void` and
    // `(Int)->Void` compare equal to the synthesised canonical form.
    static std::string canonicalizeFuncType(std::string s) {
        std::string out;
        out.reserve(s.size());
        for (char c : s) if (c != ' ' && c != '\t') out.push_back(c);
        return out;
    }

    TypedValue compileExpression(const EvoParser::Value& exprVal) {
        if (exprVal.type == EvoParser::ValueType::StringView) {
            std::string varName = std::string(EvoParser::toString(exprVal));

            // FEATURE: First-Class Functions — resolve a global function
            // name used as a value expression. `var cb = square` pulls the
            // function's address out of the module and tags it with the
            // synthesised `(Int)->Void` signature so the rest of the
            // compiler can type-check and dispatch it indirectly.
            if (functions_.count(varName) && module_->getFunction(varName)) {
                llvm::Function* F = module_->getFunction(varName);
                return {F, buildFuncSigType(functions_[varName])};
            }

            auto var = lookupVar(varName);
            if (!var) ThrowTypeError("Variable '" + varName + "' used before being declared.");
            return {builder_->CreateLoad(getLLVMType(var->typeName), var->alloca, varName.c_str()), var->typeName};
        }

        auto exprArr = ctx_->getArrayElements(exprVal);
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

        // FEATURE: First-Class Closures — `{ x in body }` expressions lower
        // to a thick-pointer aggregate captured from the surrounding
        // scope. See `compileClosure` for the full lowering.
        if (nodeType == "Closure") {
            return compileClosure(exprArr);
        }

        if (nodeType == "ArrayLiteral") {
            std::vector<llvm::Value*> elements;
            if (!EvoParser::isNull(exprArr[1])) {
                auto argsArr = ctx_->getArrayElements(exprArr[1]);
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
            // Guarantee at least a 4-byte scratch allocation so empty
            // literals can still round-trip through `free` without
            // tripping platform-specific "free(nullptr) isn't always
            // nullptr" quirks (MSVCRT in particular).
            uint64_t allocBufSize = bufSize == 0 ? 4 : bufSize;
            llvm::Value* bufHeapPtr = builder_->CreateCall(getMalloc(), {llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context_), allocBufSize)});

            builder_->CreateStore(llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), elements.size()), builder_->CreateStructGEP(arrTy, arrHeapPtr, 0));
            builder_->CreateStore(llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), elements.size()), builder_->CreateStructGEP(arrTy, arrHeapPtr, 1));
            builder_->CreateStore(bufHeapPtr, builder_->CreateStructGEP(arrTy, arrHeapPtr, 2));
            // FEATURE: CoW Arrays — a freshly-minted array literal is the
            // sole owner of its struct + buffer, so seed ref_count = 1.
            // Assignments and parameter passing bump this via
            // `elegant_array_retain`, and scope exit releases it.
            builder_->CreateStore(
                llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), 1),
                builder_->CreateStructGEP(arrTy, arrHeapPtr, 3));

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

        // FEATURE: Standard Library Booleans — `true`/`false` keywords
        // compile down to constant `i32` values tagged with the `Bool` type
        // so the type system can reject non-boolean conditions even though
        // the underlying storage is shared with `Int`.
        if (nodeType == "Bool") {
            int val = (std::string(EvoParser::toString(exprArr[1])) == "true") ? 1 : 0;
            return {llvm::ConstantInt::get(*context_, llvm::APInt(32, val, true)), "Bool"};
        }

        if (nodeType == "Call") {
            auto targetNode = exprArr[1];

            // FEATURE: First-Class Functions — indirect dispatch. When the
            // callee name is neither a registered static function nor a
            // class/struct constructor it must be a local variable holding
            // a function pointer. Load the pointer, rebuild the LLVM
            // function type from the variable's signature string, and
            // emit a CreateCall against the loaded address.
            if (targetNode.type == EvoParser::ValueType::StringView) {
                std::string targetName = std::string(EvoParser::toString(targetNode));
                if (!functions_.count(targetName) && !structs_.count(targetName)) {
                    TypedValue funcVar = compileExpression(targetNode);
                    bool isClosure = (funcVar.type == "Closure" || funcVar.type == "ClosureType");
                    if (!isClosure && funcVar.type.find("->") == std::string::npos) {
                        ThrowTypeError("Attempted to call '" + targetName + "' which is not a function.");
                    }

                    // FEATURE: First-Class Closures — thick-pointer call
                    // convention. Extract the instruction pointer + the
                    // heap context pointer from the aggregate and invoke
                    // the closure with the context slot prepended as an
                    // implicit first argument. Return type is always
                    // Void at the moment (the closure grammar doesn't
                    // carry an explicit return type yet).
                    if (isClosure) {
                        llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
                        llvm::Value* instructionPtr = builder_->CreateExtractValue(funcVar.val, 0, "closure_fn");
                        llvm::Value* contextPtr     = builder_->CreateExtractValue(funcVar.val, 1, "closure_ctx");

                        std::vector<llvm::Value*> argsV;
                        std::vector<llvm::Type*>  argLLTypes;
                        argsV.push_back(contextPtr);
                        argLLTypes.push_back(ptrTy);

                        if (!EvoParser::isNull(exprArr[2])) {
                            auto argsArr = ctx_->getArrayElements(exprArr[2]);
                            for (size_t i = 0; i < argsArr.size; ++i) {
                                TypedValue argVal = compileExpression(argsArr[i]);
                                argsV.push_back(argVal.val);
                                argLLTypes.push_back(getLLVMType(argVal.type));
                            }
                        }

                        llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getVoidTy(*context_), argLLTypes, false);
                        builder_->CreateCall(ft, instructionPtr, argsV);
                        return {nullptr, "Void"};
                    }

                    // Parse return type out of `(T1,T2,...)->TR`. Canonical
                    // form is space-free so we can slice directly.
                    std::string sigStr = canonicalizeFuncType(funcVar.type);
                    size_t arrowPos = sigStr.find("->");
                    std::string retType = sigStr.substr(arrowPos + 2);

                    std::vector<llvm::Value*> argsV;
                    std::vector<llvm::Type*>  argLLTypes;
                    if (!EvoParser::isNull(exprArr[2])) {
                        auto argsArr = ctx_->getArrayElements(exprArr[2]);
                        for (size_t i = 0; i < argsArr.size; ++i) {
                            TypedValue argVal = compileExpression(argsArr[i]);
                            argsV.push_back(argVal.val);
                            argLLTypes.push_back(getLLVMType(argVal.type));
                        }
                    }

                    llvm::FunctionType* dynFT = llvm::FunctionType::get(getLLVMType(retType), argLLTypes, false);
                    return {builder_->CreateCall(dynFT, funcVar.val, argsV), retType};
                }
            }

            if (targetNode.type == EvoParser::ValueType::StringView) {
                std::string callee = std::string(EvoParser::toString(targetNode));
                if (structs_.count(callee)) return {nullptr, ""};

                if (!functions_.count(callee)) ThrowTypeError("Call to undefined function '" + callee + "'");
                FuncSig& sig = functions_[callee];

                std::vector<llvm::Value*> argsV;
                if (!EvoParser::isNull(exprArr[2])) {
                    auto argsArr = ctx_->getArrayElements(exprArr[2]);

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
                auto targetArr = ctx_->getArrayElements(targetNode);
                if (EvoParser::toString(targetArr[0]) == "MemberAccess") {
                    std::string baseName = std::string(EvoParser::toString(targetArr[1]));
                    std::string methodName = std::string(EvoParser::toString(targetArr[2]));

                    // FEATURE: Static method calls + `as` alias routing.
                    // `Number.parseInt(...)` or `ML.square(...)` never
                    // require an instance. Resolve the alias first so the
                    // user-visible name maps onto the real struct, then
                    // dispatch directly to `<Type>_<method>` when the
                    // signature is marked `isStatic`. Falling through here
                    // preserves normal instance-method dispatch for any
                    // regular `func` that happens to share a base name
                    // with a registered type.
                    {
                        std::string resolvedBase = resolveAlias(baseName);
                        if (structs_.count(resolvedBase)) {
                            std::string mangledName = resolvedBase + "_" + methodName;
                            auto fit = functions_.find(mangledName);
                            if (fit != functions_.end() && fit->second.isStatic) {
                                FuncSig& sig = fit->second;

                                std::vector<llvm::Value*> argsV;
                                if (!EvoParser::isNull(exprArr[2])) {
                                    auto argsArr = ctx_->getArrayElements(exprArr[2]);
                                    for (size_t i = 0; i < argsArr.size; ++i) {
                                        argsV.push_back(compileExpression(argsArr[i]).val);
                                    }
                                }

                                llvm::Function* calleeF = module_->getFunction(mangledName);
                                return {builder_->CreateCall(calleeF, argsV), sig.retType};
                            }
                            if (fit != functions_.end() && !fit->second.isStatic) {
                                ThrowTypeError("'" + methodName + "' on '" + resolvedBase + "' is an instance method; call it on an instance (e.g. `var x = " + resolvedBase + "(); x." + methodName + "(...)`).");
                            }
                        }
                    }

                    auto var = lookupVar(baseName);
                    if (!var) ThrowTypeError("Unknown variable '" + baseName + "'");

                    // FEATURE: Dynamic Array Resizing + Copy-on-Write via
                    // `Array.append`. Arrays live on the heap as
                    // `{ i32 capacity, i32 count, i8* buffer, i32 ref_count }`.
                    //
                    // Swift arrays are value types with shared backing
                    // storage: two live bindings share the heap buffer
                    // until one of them mutates, at which point the
                    // mutator gets a private clone. Append is the canonical
                    // mutation entry point, so we insert an
                    // `isKnownUniquelyReferenced` fast-path check here:
                    //   * ref_count == 1  → mutate in place (the common
                    //     case; zero overhead beyond one load/compare).
                    //   * ref_count  > 1  → fork off a `cow_clone` block
                    //     that allocates a fresh struct + buffer, memcpys
                    //     the data across, drops the original ref (so the
                    //     other sharers still see the old data), and
                    //     stores the new struct into this variable's
                    //     alloca so subsequent loads see the private copy.
                    //
                    // All branches rejoin at a single `mutate_array` block
                    // which does the familiar capacity check + realloc,
                    // then stores the new element at `buffer[count]` and
                    // bumps the count. All branches rejoin at a single
                    // append block so the rest of the function sees a
                    // well-formed CFG.
                    if (var->typeName == "Array" && methodName == "append") {
                        if (EvoParser::isNull(exprArr[2])) ThrowTypeError("Array.append requires exactly one argument.");
                        auto argsArr = ctx_->getArrayElements(exprArr[2]);
                        if (argsArr.size != 1) ThrowTypeError("Array.append requires exactly one argument.");
                        TypedValue element = compileExpression(argsArr[0]);
                        if (element.type != "Int") ThrowTypeError("Array.append currently only supports 'Int' elements.");

                        llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
                        llvm::Type* i32Ty = llvm::Type::getInt32Ty(*context_);
                        llvm::Type* i64Ty = llvm::Type::getInt64Ty(*context_);
                        llvm::StructType* arrTy = getSwiftArrayType();

                        // --- Copy-on-Write fast-path check ---
                        // Load the current struct pointer + its ref_count.
                        // If the count is > 1 we fall into CoWCloneBB and
                        // replace this variable's alloca with a private
                        // copy; otherwise we go straight to MutateBB and
                        // rewrite the shared struct in place.
                        llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
                        llvm::Value* sharedArr    = builder_->CreateLoad(ptrTy, var->alloca);
                        llvm::Value* sharedRefPtr = builder_->CreateStructGEP(arrTy, sharedArr, 3);
                        llvm::Value* sharedRef    = builder_->CreateLoad(i32Ty, sharedRefPtr);
                        llvm::Value* isUnique     = builder_->CreateICmpEQ(sharedRef, llvm::ConstantInt::get(i32Ty, 1));

                        llvm::BasicBlock* CoWCloneBB = llvm::BasicBlock::Create(*context_, "cow_clone",   TheFunction);
                        llvm::BasicBlock* MutateBB   = llvm::BasicBlock::Create(*context_, "mutate_array", TheFunction);
                        builder_->CreateCondBr(isUnique, MutateBB, CoWCloneBB);

                        // --- Copy-on-Write clone path ---
                        builder_->SetInsertPoint(CoWCloneBB);
                        llvm::Value* oldCapPtr    = builder_->CreateStructGEP(arrTy, sharedArr, 0);
                        llvm::Value* oldCountPtr  = builder_->CreateStructGEP(arrTy, sharedArr, 1);
                        llvm::Value* oldBufPtr    = builder_->CreateStructGEP(arrTy, sharedArr, 2);
                        llvm::Value* oldCap   = builder_->CreateLoad(i32Ty, oldCapPtr);
                        llvm::Value* oldCount = builder_->CreateLoad(i32Ty, oldCountPtr);
                        llvm::Value* oldBuf   = builder_->CreateLoad(ptrTy, oldBufPtr);

                        // Allocate the new buffer. `max(capacity, 1)` keeps
                        // us from sitting on a zero-byte malloc that some
                        // libcs refuse to service.
                        llvm::Value* capIsZero   = builder_->CreateICmpEQ(oldCap, llvm::ConstantInt::get(i32Ty, 0));
                        llvm::Value* allocCap    = builder_->CreateSelect(capIsZero, llvm::ConstantInt::get(i32Ty, 1), oldCap);
                        llvm::Value* bytesToCopy = builder_->CreateMul(oldCount, llvm::ConstantInt::get(i32Ty, 4));
                        llvm::Value* bytesToAlloc= builder_->CreateMul(allocCap, llvm::ConstantInt::get(i32Ty, 4));
                        llvm::Value* newBuf      = builder_->CreateCall(
                            getMalloc(),
                            {builder_->CreateZExt(bytesToAlloc, i64Ty)});
                        builder_->CreateCall(getMemcpy(), {
                            newBuf,
                            oldBuf,
                            builder_->CreateZExt(bytesToCopy, i64Ty)
                        });

                        // Allocate the new SwiftArray struct, seed it with
                        // the same capacity/count and a freshly-owned
                        // ref_count of 1.
                        uint64_t structSize = module_->getDataLayout().getTypeAllocSize(arrTy);
                        llvm::Value* newArr = builder_->CreateCall(
                            getMalloc(),
                            {llvm::ConstantInt::get(i64Ty, structSize)});
                        builder_->CreateStore(oldCap,   builder_->CreateStructGEP(arrTy, newArr, 0));
                        builder_->CreateStore(oldCount, builder_->CreateStructGEP(arrTy, newArr, 1));
                        builder_->CreateStore(newBuf,   builder_->CreateStructGEP(arrTy, newArr, 2));
                        builder_->CreateStore(
                            llvm::ConstantInt::get(i32Ty, 1),
                            builder_->CreateStructGEP(arrTy, newArr, 3));

                        // Drop this variable's share of the original
                        // struct and rebind the local to the private copy.
                        if (auto* arRel = module_->getFunction("elegant_array_release")) {
                            builder_->CreateCall(arRel, {sharedArr});
                        }
                        builder_->CreateStore(newArr, var->alloca);
                        builder_->CreateBr(MutateBB);

                        builder_->SetInsertPoint(MutateBB);

                        // Re-load via the alloca so we see the clone on
                        // the CoW path and the original struct on the
                        // unique-ref path.
                        llvm::Value* arrObj = builder_->CreateLoad(ptrTy, var->alloca);
                        llvm::Value* capPtr     = builder_->CreateStructGEP(arrTy, arrObj, 0);
                        llvm::Value* countPtr   = builder_->CreateStructGEP(arrTy, arrObj, 1);
                        llvm::Value* bufPtrAddr = builder_->CreateStructGEP(arrTy, arrObj, 2);

                        llvm::Value* capacity = builder_->CreateLoad(i32Ty, capPtr);
                        llvm::Value* count    = builder_->CreateLoad(i32Ty, countPtr);
                        llvm::Value* buffer   = builder_->CreateLoad(ptrTy, bufPtrAddr);

                        llvm::Value* isFull = builder_->CreateICmpEQ(count, capacity);

                        llvm::BasicBlock* ReallocBB = llvm::BasicBlock::Create(*context_, "realloc_buf", TheFunction);
                        llvm::BasicBlock* AppendBB  = llvm::BasicBlock::Create(*context_, "append_item", TheFunction);

                        builder_->CreateCondBr(isFull, ReallocBB, AppendBB);

                        builder_->SetInsertPoint(ReallocBB);
                        // Grow by doubling; bootstrap empty arrays to a
                        // minimum capacity of 1 so `0 * 2` doesn't leave
                        // us stuck with a zero-byte buffer forever.
                        llvm::Value* doubled = builder_->CreateMul(capacity, llvm::ConstantInt::get(i32Ty, 2));
                        llvm::Value* isEmpty = builder_->CreateICmpEQ(capacity, llvm::ConstantInt::get(i32Ty, 0));
                        llvm::Value* newCapacity = builder_->CreateSelect(isEmpty, llvm::ConstantInt::get(i32Ty, 1), doubled);
                        builder_->CreateStore(newCapacity, capPtr);

                        llvm::Value* newSizeBytes = builder_->CreateMul(newCapacity, llvm::ConstantInt::get(i32Ty, 4));
                        llvm::Value* newSizeBytes64 = builder_->CreateZExt(newSizeBytes, i64Ty);

                        llvm::Value* newBuffer = builder_->CreateCall(getRealloc(), {buffer, newSizeBytes64});
                        builder_->CreateStore(newBuffer, bufPtrAddr);
                        builder_->CreateBr(AppendBB);

                        builder_->SetInsertPoint(AppendBB);
                        // Reload the buffer — realloc may have moved it.
                        llvm::Value* currentBuffer = builder_->CreateLoad(ptrTy, bufPtrAddr);
                        llvm::Value* targetPtr = builder_->CreateGEP(i32Ty, currentBuffer, count);
                        builder_->CreateStore(element.val, targetPtr);

                        llvm::Value* newCount = builder_->CreateAdd(count, llvm::ConstantInt::get(i32Ty, 1));
                        builder_->CreateStore(newCount, countPtr);

                        return {nullptr, "Void"};
                    }

                    // =====================================================
                    // FEATURE: Raw Memory Intrinsics on `Memory`.
                    //
                    // Four methods on the stdlib `Memory` class are lowered
                    // directly to LLVM instructions instead of going through
                    // normal method dispatch: `ptrToInt` / `intToPtr` let
                    // users round-trip between an `i8*` and an integer
                    // address, and `peek` / `poke` dereference arbitrary
                    // integer addresses as `i32` cells. The `Memory` stubs
                    // in the Prelude exist only to pacify the semantic
                    // checker — their bodies are never reached because we
                    // short-circuit here.
                    // =====================================================
                    if (var->typeName == "Memory") {
                        llvm::Type* i32Ty = llvm::Type::getInt32Ty(*context_);
                        llvm::Type* i64Ty = llvm::Type::getInt64Ty(*context_);
                        llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);

                        auto requireArgs = [&](size_t n) {
                            if (EvoParser::isNull(exprArr[2])) {
                                ThrowTypeError("Memory." + methodName + " requires " + std::to_string(n) + " argument(s).");
                            }
                            auto argsArr = ctx_->getArrayElements(exprArr[2]);
                            if (argsArr.size != n) {
                                ThrowTypeError("Memory." + methodName + " requires " + std::to_string(n) + " argument(s).");
                            }
                            return argsArr;
                        };

                        // `alloc` routes through getMalloc() — see prelude note.
                        // We zero-extend the i32 `Int` arg to i64 to match
                        // the internal shim's `size_t` prototype.
                        if (methodName == "alloc") {
                            auto argsArr = requireArgs(1);
                            TypedValue bytes = compileExpression(argsArr[0]);
                            if (bytes.type != "Int") ThrowTypeError("Memory.alloc expects an Int size.");
                            llvm::Value* bytes64 = builder_->CreateZExt(bytes.val, i64Ty);
                            return {builder_->CreateCall(getMalloc(), {bytes64}), "String"};
                        }
                        if (methodName == "ptrToInt") {
                            auto argsArr = requireArgs(1);
                            TypedValue ptr = compileExpression(argsArr[0]);
                            return {builder_->CreatePtrToInt(ptr.val, i32Ty), "Int"};
                        }
                        if (methodName == "intToPtr") {
                            auto argsArr = requireArgs(1);
                            TypedValue addr = compileExpression(argsArr[0]);
                            return {builder_->CreateIntToPtr(addr.val, ptrTy), "String"};
                        }
                        if (methodName == "peek") {
                            auto argsArr = requireArgs(1);
                            TypedValue addr = compileExpression(argsArr[0]);
                            llvm::Value* rawPtr = builder_->CreateIntToPtr(addr.val, ptrTy);
                            return {builder_->CreateLoad(i32Ty, rawPtr), "Int"};
                        }
                        if (methodName == "poke") {
                            auto argsArr = requireArgs(2);
                            TypedValue addr = compileExpression(argsArr[0]);
                            TypedValue val  = compileExpression(argsArr[1]);
                            llvm::Value* rawPtr = builder_->CreateIntToPtr(addr.val, ptrTy);
                            builder_->CreateStore(val.val, rawPtr);
                            return {nullptr, "Void"};
                        }
                    }

                    // =====================================================
                    // FEATURE: `Files.write` interceptor.
                    //
                    // Computes the payload length via the internal i64 strlen
                    // shim (which would clash with a prelude-level i32 extern)
                    // and emits a `fwrite(data, 1, len, self.handle)` call
                    // against the i32-shaped FFI fwrite. The shim's wider
                    // return type is truncated to `Int` on the Elegant side.
                    // =====================================================
                    if (var->typeName == "Files" && methodName == "write") {
                        if (EvoParser::isNull(exprArr[2])) ThrowTypeError("Files.write requires one argument.");
                        auto argsArr = ctx_->getArrayElements(exprArr[2]);
                        if (argsArr.size != 1) ThrowTypeError("Files.write requires one argument.");

                        TypedValue data = compileExpression(argsArr[0]);
                        if (data.type != "String") ThrowTypeError("Files.write expects a String.");

                        llvm::Type* i32Ty = llvm::Type::getInt32Ty(*context_);
                        llvm::Type* ptrTy = llvm::PointerType::getUnqual(*context_);
                        llvm::StructType* filesTy = structs_["Files"].type;

                        llvm::Value* selfObj    = builder_->CreateLoad(ptrTy, var->alloca);
                        llvm::Value* handleAddr = builder_->CreateStructGEP(filesTy, selfObj, structs_["Files"].fieldIndices["handle"]);
                        llvm::Value* handle     = builder_->CreateLoad(ptrTy, handleAddr);

                        llvm::Value* lenI64 = builder_->CreateCall(getStrLen(), {data.val});
                        llvm::Value* lenI32 = builder_->CreateTrunc(lenI64, i32Ty);

                        llvm::Function* fwrite = module_->getFunction("fwrite");
                        if (!fwrite) ThrowTypeError("Missing fwrite declaration in prelude.");
                        builder_->CreateCall(fwrite, {
                            data.val,
                            llvm::ConstantInt::get(i32Ty, 1),
                            lenI32,
                            handle
                        });
                        return {nullptr, "Void"};
                    }

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
                        auto argsArr = ctx_->getArrayElements(exprArr[2]);
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

        // FEATURE: Unary operators. Currently just '-' for Int/Float
        // negation, lowered to LLVM's `neg` / `fneg` so call sites can
        // write `-1` directly instead of faking it with `0 - 1`.
        if (nodeType == "Unary") {
            std::string op = std::string(EvoParser::toString(exprArr[1]));
            TypedValue expr = compileExpression(exprArr[2]);

            if (op == "-") {
                if (expr.type == "Int") return {builder_->CreateNeg(expr.val), "Int"};
                if (expr.type == "Float") return {builder_->CreateFNeg(expr.val), "Float"};
                ThrowTypeError("Unary operator '-' cannot be applied to type '" + expr.type + "'.");
            }
            ThrowTypeError("Unknown unary operator '" + op + "'.");
        }

        if (nodeType == "Binary") {
            std::string op = std::string(EvoParser::toString(exprArr[1]));
            TypedValue L = compileExpression(exprArr[2]);
            TypedValue R = compileExpression(exprArr[3]);

            if (L.type != R.type) ThrowTypeError("Operator '" + op + "' cannot be applied to types '" + L.type + "' and '" + R.type + "'");

            if (op == "+") {
                if (L.type == "Int") return {builder_->CreateAdd(L.val, R.val), "Int"};

                // FEATURE: Native Heap String Concatenation. When the type
                // checker sees `String + String` it lowers to a sequence of
                // libc calls: size the result via `strlen`, grab a fresh
                // heap buffer with `malloc` (+1 for the null terminator),
                // then `strcpy` / `strcat` the operands into place. The
                // resulting pointer is tagged `String` so subsequent ops
                // flow through the normal C-string path.
                if (L.type == "String") {
                    llvm::Value* lenL = builder_->CreateCall(getStrLen(), {L.val});
                    llvm::Value* lenR = builder_->CreateCall(getStrLen(), {R.val});

                    llvm::Value* totalLen = builder_->CreateAdd(lenL, lenR);
                    totalLen = builder_->CreateAdd(totalLen, llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context_), 1));

                    llvm::Value* newStr = builder_->CreateCall(getMalloc(), {totalLen});

                    builder_->CreateCall(getStrCpy(), {newStr, L.val});
                    builder_->CreateCall(getStrCat(), {newStr, R.val});

                    return {newStr, "String"};
                }
                ThrowTypeError("Operator '+' is not supported for type '" + L.type + "'");
            }

            // Arithmetic minus/multiply/divide still require Int operands.
            // Comparisons below happily accept Bool since Bool shares the
            // i32 representation with Int.
            if (op == "-" || op == "*" || op == "/") {
                if (L.type != "Int") ThrowTypeError("Mathematical operators only support 'Int' currently.");
            }

            if (op == "-") return {builder_->CreateSub(L.val, R.val), "Int"};
            if (op == "*") return {builder_->CreateMul(L.val, R.val), "Int"};
            if (op == "/") {
                // FEATURE: Runtime zero-division protection. Traps before the
                // SDiv can raise SIGFPE, giving a clean diagnostic + exit(1).
                llvm::Value* isZero = builder_->CreateICmpEQ(R.val, llvm::ConstantInt::get(*context_, llvm::APInt(32, 0, true)));
                llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
                llvm::BasicBlock* PanicBB = llvm::BasicBlock::Create(*context_, "div_panic", TheFunction);
                llvm::BasicBlock* ContBB = llvm::BasicBlock::Create(*context_, "div_cont", TheFunction);

                builder_->CreateCondBr(isZero, PanicBB, ContBB);

                builder_->SetInsertPoint(PanicBB);
                llvm::Value* panicMsg = builder_->CreateGlobalString(
                    "\n\033[31m\xF0\x9F\x9A\xA8 Fatal Error:\033[0m Division by zero.\n",
                    "div_panic_msg");
                builder_->CreateCall(getPrintf(), {panicMsg});
                builder_->CreateCall(getExit(), {llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), 1)});
                builder_->CreateUnreachable();

                builder_->SetInsertPoint(ContBB);
                return {builder_->CreateSDiv(L.val, R.val), "Int"};
            }

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
#include <cstring>

// FEATURE: Cross-platform Thread shims.
// The Prelude's `Thread` class targets the Windows C runtime + kernel32
// APIs (`_beginthread`, `Sleep`, `WaitForSingleObject`). When the JIT
// runs on a non-Windows host those symbols don't exist in any loaded
// library, and LLJIT refuses to materialise the module even if no user
// code actually calls Thread. We expose weak C-linkage stubs here so
// `DynamicLibrarySearchGenerator::GetForCurrentProcess` resolves them
// against this executable's symbol table on POSIX. On Windows the
// matching msvcrt/kernel32 symbols already exist and will be preferred
// by the linker, so these stubs only kick in for JIT-on-Linux / macOS.
#if !defined(_WIN32)
#include <pthread.h>
#include <time.h>
#include <mutex>
#include <unordered_map>
namespace {
    // Bridge Win32-style `int` handles onto `pthread_t`. We hand the
    // script a small integer id and track the real pthread here so
    // WaitForSingleObject can `pthread_join` on the corresponding
    // thread without exposing pthread_t (which is opaque on POSIX).
    std::mutex g_threadMutex;
    std::unordered_map<int, pthread_t> g_threadHandles;
    int g_nextHandle = 1;
}
extern "C" {
    __attribute__((weak)) int _beginthread(void (*start)(void), unsigned stack_size, void* arglist) {
        (void)stack_size; (void)arglist;
        pthread_t th;
        struct Adapter {
            static void* run(void* p) {
                auto fn = reinterpret_cast<void (*)(void)>(p);
                if (fn) fn();
                return nullptr;
            }
        };
        if (pthread_create(&th, nullptr, &Adapter::run, reinterpret_cast<void*>(start)) != 0) return 0;
        std::lock_guard<std::mutex> g(g_threadMutex);
        int handle = g_nextHandle++;
        g_threadHandles[handle] = th;
        return handle;
    }
    __attribute__((weak)) void Sleep(unsigned ms) {
        struct timespec ts;
        ts.tv_sec  = static_cast<time_t>(ms / 1000);
        ts.tv_nsec = static_cast<long>((ms % 1000) * 1000000L);
        nanosleep(&ts, nullptr);
    }
    __attribute__((weak)) int WaitForSingleObject(int handle, int ms) {
        (void)ms;
        pthread_t th;
        {
            std::lock_guard<std::mutex> g(g_threadMutex);
            auto it = g_threadHandles.find(handle);
            if (it == g_threadHandles.end()) return 0;
            th = it->second;
            g_threadHandles.erase(it);
        }
        pthread_join(th, nullptr);
        return 0;
    }
}
#endif

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

    // =========================================================================
    // FEATURE: The Elegant Standard Library (Prelude).
    //
    // Just like Swift silently imports its Stdlib module into every file,
    // we prepend a small set of declarations to every script so users can
    // call `print`, `printInt`, `fatalError`, and a handful of math helpers
    // without ever writing an `extern func printf`. The extern declarations
    // are idempotent: duplicate registrations (for scripts that still bring
    // their own `extern func printf`) are swallowed by the Extern pass.
    // =========================================================================
    std::string stdlib = R"ELEGANT(
// --- 1. CORE OS FFI BINDINGS ---
// These resolve against libc / msvcrt at runtime via the JIT's dynamic
// symbol lookup. No special linking required on the user's end.
extern func printf(format: String, ...) -> Void
extern func exit(status: Int) -> Void
extern func system(cmd: String) -> Int
extern func getenv(name: String) -> String
extern func getchar() -> Int

// --- 2. MEMORY & FILE FFI BINDINGS ---
// `String` is a raw `i8*` in LLVM IR, so it doubles as `void*` / `FILE*`
// across the C ABI boundary — the type system just sees an opaque pointer.
//
// Notably absent: `malloc` and `strlen`. Those names clash with internal
// shims (`getMalloc` / `getStrLen`) that use the correct 64-bit `size_t`
// prototypes. Exposing an i32-shaped version here poisons the shim cache
// and makes callers emit malformed `add i32, i64` IR. `Memory.alloc` and
// `Files.write` route through compileExpression interceptors below and
// call the internal shims directly with proper zero-extension.
extern func free(ptr: String) -> Void
extern func memset(ptr: String, val: Int, num: Int) -> String
extern func fopen(filename: String, mode: String) -> String
extern func fclose(stream: String) -> Int
extern func fwrite(ptr: String, size: Int, count: Int, stream: String) -> Int
extern func fread(ptr: String, size: Int, count: Int, stream: String) -> Int

// --- 3. NUMBER UTILITY FFI BINDINGS ---
// `sprintf` is declared with a fixed 3-arg shape because the compiler's
// varargs support is reserved for stdlib-owned variadics like printf. A
// fixed signature is enough for the integer formatting we actually need.
extern func rand() -> Int
extern func atoi(str: String) -> Int
extern func sprintf(buffer: String, format: String, val: Int) -> Int

// Math Library bindings — the OS math lib is linked in via the JIT's
// dynamic symbol lookup, so `sqrt` and friends resolve against libm at
// runtime with no additional setup on the user's part.
extern func sqrt(x: Float) -> Float
extern func pow(base: Float, exp: Float) -> Float
extern func abs(x: Int) -> Int

// --- 4. MULTITHREADING FFI BINDINGS ---
// `_beginthread` / `Sleep` / `WaitForSingleObject` are the Windows C
// runtime + Win32 kernel APIs used by the `Thread` class below. On the
// Windows JIT target they resolve against msvcrt + kernel32 via the
// dynamic symbol lookup. On non-Windows hosts the symbols obviously
// don't exist, so scripts that actually *invoke* Thread will fail at
// JIT symbol resolution rather than at parse time — which is what we
// want, so the Prelude keeps compiling cleanly on every platform.
extern func _beginthread(start: ()->Void, stack_size: Int, arglist: Int) -> Int
extern func Sleep(ms: Int) -> Void
extern func WaitForSingleObject(handle: Int, milliseconds: Int) -> Int

// --- CORE GLOBALS ---
func print(text: String) {
    printf(format: "%s\n", text)
}

func printInt(val: Int) {
    printf(format: "%d\n", val)
}

func fatalError(msg: String) {
    printf(format: "\nFatal Error: %s\n", msg)
    exit(status: 1)
}

// ==========================================
// ELEGANT STANDARD LIBRARY CLASSES
// ==========================================

// FEATURE: Static Dispatch — the Prelude's utility classes act as
// static namespaces now that the language supports `static func`. No
// instantiation required: call `Elegant.info()`, `Number.parseInt(...)`,
// `Memory.alloc(...)` etc. directly on the type.
class Elegant {
    static func info() {
        printf(format: "Elegant Compiler v1.0.0 | Target: Native\n")
    }
}

// Thin veneer over `system` / `getenv` so scripts can spawn subprocesses
// and query the environment without touching the raw FFI by hand.
class OS {
    static func execute(command: String) -> Int {
        return system(cmd: command)
    }

    static func getEnv(name: String) -> String {
        return getenv(name: name)
    }
}

class IO {
    func readChar() -> Int {
        return getchar()
    }
}

// Manual heap management that completely sidesteps ARC. Useful for scratch
// buffers, FFI handoff, and the raw-memory intrinsics below. The
// ptrToInt/intToPtr/peek/poke stubs exist so the semantic checker accepts
// the call sites — the LLVM backend intercepts those four methods and
// emits raw inttoptr/ptrtoint/load/store instead of dispatching here.
class Memory {
    // `alloc` is a compileExpression interceptor: the dummy body exists
    // only to satisfy the type checker. At lowering time we emit a direct
    // call to the internal `getMalloc()` shim with an i64-zero-extended
    // size argument so we don't collide with the prelude-level extern.
    func alloc(bytes: Int) -> String { return "" }

    static func free(ptr: String) {
        free(ptr: ptr)
    }

    static func clear(ptr: String, bytes: Int) {
        memset(ptr: ptr, val: 0, num: bytes)
    }

    // DANGER: UNRESTRICTED MEMORY INTRINSICS — backed by LLVM, not by
    // these dummy bodies. The stubs are only here to satisfy the type
    // checker; the real lowering happens in compileExpression.
    //
    // Known limitation: `Int` is i32 in Elegant, so `ptrToInt` truncates
    // pointers on 64-bit targets and `peek` / `poke` can only address the
    // low 4 GiB. Lifting this requires a language-level `Int64` type.
    func ptrToInt(ptr: String) -> Int { return 0 }
    func intToPtr(address: Int) -> String { return "" }
    func peek(address: Int) -> Int { return 0 }
    func poke(address: Int, value: Int) {}
}

// `handle` is treated as a C `FILE*` — we hand it straight to fwrite/
// fclose without ever dereferencing it on the Elegant side.
class Files {
    var handle: String

    func open(path: String, mode: String) {
        self.handle = fopen(filename: path, mode: mode)
    }

    // `write` is a compileExpression interceptor so we can use the
    // internal `getStrLen()` shim (returning i64) without colliding with
    // a prelude-level `extern func strlen`. The dummy body is unreachable.
    func write(data: String) {}

    func close() {
        fclose(stream: self.handle)
    }
}

// Lightweight HTTP client that shells out to the OS-native `curl` binary
// (ships with Windows 10+/macOS/most Linux distros). Keeps us out of the
// raw-sockets business until we need a real networking story.
class HTTP {
    static func download(url: String, outputFile: String) {
        var cmd = "curl -s -L " + url + " -o " + outputFile
        printf(format: "Downloading: %s\n", url)
        system(cmd: cmd)
    }
}

// Small utility belt for the common string <-> int conversions that our
// minimal built-in operators can't express on their own.
class Number {
    static func parseInt(str: String) -> Int {
        return atoi(str: str)
    }

    // Int -> dynamically heap-allocated String. 32 bytes is enough for
    // any 32-bit integer's decimal representation plus a null terminator
    // with room to spare.
    static func toString(val: Int) -> String {
        var mem = Memory()
        var buffer = mem.alloc(bytes: 32)
        sprintf(buffer: buffer, format: "%d", val: val)
        return buffer
    }

    // We don't parse the `%` operator yet, so we simulate modulo using
    // integer division truncation: r - range * (r / range).
    static func random(min: Int, max: Int) -> Int {
        var r = rand()
        var range = (max - min) + 1
        var remainder = r - (range * (r / range))
        return min + remainder
    }
}

// FEATURE: OS-Level Multithreading.
// `Thread.spawn` hands a first-class function pointer to `_beginthread`
// and returns an OS thread handle. `Thread.join` safely blocks the
// calling thread until the worker signals completion via
// `WaitForSingleObject` with the `INFINITE` sentinel (-1 / 0xFFFFFFFF).
class Thread {
    static func spawn(task: ()->Void) -> Int {
        return _beginthread(start: task, stack_size: 0, arglist: 0)
    }

    static func sleep(ms: Int) {
        Sleep(ms: ms)
    }

    static func join(handle: Int) {
        // INFINITE = 0xFFFFFFFF, which is -1 interpreted as a signed 32-bit
        // integer. Lowered via the unary-minus operator to a CreateNeg on
        // the i32 `1`, matching WaitForSingleObject's signed-milliseconds ABI.
        WaitForSingleObject(handle: handle, milliseconds: -1)
    }
}
)ELEGANT";

    // Stitch the Prelude ahead of the user's source. Line numbers in
    // diagnostics will be offset by the prelude's length — acceptable
    // tradeoff for getting a Swift-like zero-import experience.
    std::string source = stdlib + "\n" + ss.str();

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
