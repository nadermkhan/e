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

// === LLVM ORC JIT Headers ===
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/ExecutionEngine/Orc/ExecutionUtils.h>

#include <ElegantParser.hpp>

namespace Elegant {

// FEATURE: The Semantic Analyzer Type Registry.
// Tracks whether a user-defined nominal type is a Value Type (Struct, stack)
// or a Reference Type (Class, heap via malloc + pointer copy semantics).
struct StructInfo {
    llvm::StructType* type = nullptr;
    std::unordered_map<std::string, unsigned> fieldIndices;
    std::vector<llvm::Type*> fieldTypes;
    bool isReferenceType = false; // true => class (heap), false => struct (stack)
};

struct VarInfo {
    llvm::AllocaInst* alloca;
    std::string typeName;
};

class LLVMCompiler {
    EvoParser::ParseContext& ctx_;
    std::unique_ptr<llvm::LLVMContext> context_;
    std::unique_ptr<llvm::Module> module_;
    std::unique_ptr<llvm::IRBuilder<>> builder_;

    std::unordered_map<std::string, VarInfo> named_values_;
    std::unordered_map<std::string, StructInfo> structs_;

public:
    LLVMCompiler(EvoParser::ParseContext& ctx, const std::string& moduleName)
        : ctx_(ctx) {
        context_ = std::make_unique<llvm::LLVMContext>();
        module_ = std::make_unique<llvm::Module>(moduleName, *context_);
        builder_ = std::make_unique<llvm::IRBuilder<>>(*context_);
    }

    // Dynamic FFI linker to the OS 'malloc' function for heap allocation.
    llvm::Function* getMalloc() {
        if (auto* M = module_->getFunction("malloc")) return M;
        auto* FT = llvm::FunctionType::get(
            llvm::PointerType::getUnqual(*context_),
            {llvm::Type::getInt64Ty(*context_)},
            false);
        return llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "malloc", module_.get());
    }

    // MAP AST TYPES TO LLVM RAM TYPES
    llvm::Type* getLLVMType(const std::string& typeName) {
        if (typeName == "Int") return llvm::Type::getInt32Ty(*context_);
        if (typeName == "Float") return llvm::Type::getDoubleTy(*context_);
        if (typeName == "String") return llvm::PointerType::getUnqual(*context_);
        if (typeName == "Void" || typeName == "") return llvm::Type::getVoidTy(*context_);

        if (structs_.count(typeName)) {
            // Swift semantics: classes are pointers, structs are values.
            if (structs_[typeName].isReferenceType) return llvm::PointerType::getUnqual(*context_);
            return structs_[typeName].type;
        }
        return llvm::Type::getInt32Ty(*context_); // fallback
    }

    void compile() {
        auto declarations = ctx_.getArrayElements(ctx_.root);

        // PASS 1: Semantic Type Registration (structs vs classes) + externs
        for (const auto& declVal : declarations) {
            auto declArr = ctx_.getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);

            if (nodeType == "Class" || nodeType == "Struct") {
                std::string name = std::string(EvoParser::toString(declArr[1]));
                structs_[name].type = llvm::StructType::create(*context_, name);
                structs_[name].isReferenceType = (nodeType == "Class");
            }
            else if (nodeType == "Extern") {
                std::string extName = std::string(EvoParser::toString(declArr[1]));
                std::vector<llvm::Type*> argTypes;
                bool isVarArg = false;

                if (!EvoParser::isNull(declArr[2])) {
                    auto paramsArr = ctx_.getArrayElements(declArr[2]);
                    for (const auto& param : paramsArr) {
                        auto p = ctx_.getArrayElements(param);
                        std::string pType = std::string(EvoParser::toString(p[2]));
                        if (pType == "VarArg") isVarArg = true;
                        else argTypes.push_back(getLLVMType(pType));
                    }
                }

                std::string retTypeName = EvoParser::isNull(declArr[3])
                    ? "Void" : std::string(EvoParser::toString(declArr[3]));
                llvm::FunctionType* ft = llvm::FunctionType::get(
                    getLLVMType(retTypeName), argTypes, isVarArg);
                llvm::Function::Create(ft, llvm::Function::ExternalLinkage, extName, module_.get());
            }
        }

        // PASS 2: Memory blueprint mapping (fill in struct bodies).
        for (const auto& declVal : declarations) {
            auto declArr = ctx_.getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);

            if (nodeType == "Class" || nodeType == "Struct") {
                std::string name = std::string(EvoParser::toString(declArr[1]));
                StructInfo& info = structs_[name];
                auto members = ctx_.getArrayElements(declArr[3]);

                unsigned idx = 0;
                for (const auto& mem : members) {
                    auto memArr = ctx_.getArrayElements(mem);
                    if (EvoParser::toString(memArr[0]) == "Property") {
                        std::string propName = std::string(EvoParser::toString(memArr[2]));
                        std::string propType = EvoParser::isNull(memArr[3])
                            ? "Int" : std::string(EvoParser::toString(memArr[3]));
                        info.fieldIndices[propName] = idx++;
                        info.fieldTypes.push_back(getLLVMType(propType));
                    }
                }
                info.type->setBody(info.fieldTypes);
            }
        }

        // PASS 3: Generate Executable Code
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

        auto processSymbols = llvm::orc::DynamicLibrarySearchGenerator::GetForCurrentProcess(
            jit->getDataLayout().getGlobalPrefix());
        if (processSymbols) jit->getMainJITDylib().addGenerator(std::move(*processSymbols));

        auto tsm = llvm::orc::ThreadSafeModule(std::move(module_), std::move(context_));
        if (auto err = jit->addIRModule(std::move(tsm))) return 1;

        auto mainSym = jit->lookup("main");
        if (!mainSym) {
            llvm::errs() << "\n❌ Execution Error: Could not find 'func main()' to execute.\n";
            return 1;
        }

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

        auto targetMachine = target->createTargetMachine(
            targetTriple, "generic", "", llvm::TargetOptions(),
            std::optional<llvm::Reloc::Model>(llvm::Reloc::PIC_));
        module_->setDataLayout(targetMachine->createDataLayout());

        std::error_code ec;
        llvm::raw_fd_ostream dest(filename, ec, llvm::sys::fs::OF_None);
        if (ec) return false;

        llvm::legacy::PassManager pass;
        if (targetMachine->addPassesToEmitFile(pass, dest, nullptr, llvm::CodeGenFileType::ObjectFile))
            return false;

        pass.run(*module_);
        dest.flush();
        return true;
    }

private:
    llvm::AllocaInst* CreateEntryBlockAlloca(llvm::Function* TheFunction,
                                             const std::string& VarName,
                                             llvm::Type* type) {
        llvm::IRBuilder<> TmpB(&TheFunction->getEntryBlock(), TheFunction->getEntryBlock().begin());
        return TmpB.CreateAlloca(type, nullptr, VarName);
    }

    llvm::Function* compileFunction(const EvoParser::ArrayView& funcNode,
                                    std::string className,
                                    llvm::StructType* classType) {
        std::string name = std::string(EvoParser::toString(funcNode[1]));
        if (!className.empty()) name = className + "_" + name;

        std::vector<llvm::Type*> argTypes;
        std::vector<std::string> argNames;

        if (classType) {
            // 'self' is a pointer either way (opaque pointers).
            // For classes: heap pointer. For structs: pointer-to-stack-struct.
            argTypes.push_back(llvm::PointerType::getUnqual(*context_));
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

        std::string retTypeName = EvoParser::isNull(funcNode[3])
            ? "Void" : std::string(EvoParser::toString(funcNode[3]));
        llvm::FunctionType* ft = llvm::FunctionType::get(getLLVMType(retTypeName), argTypes, false);
        llvm::Function* f = llvm::Function::Create(
            ft, llvm::Function::ExternalLinkage, name, module_.get());

        llvm::BasicBlock* bb = llvm::BasicBlock::Create(*context_, "entry", f);
        builder_->SetInsertPoint(bb);
        named_values_.clear();

        unsigned idx = 0;
        for (auto& arg : f->args()) {
            std::string argName = argNames[idx++];
            arg.setName(argName);
            llvm::AllocaInst* Alloca = CreateEntryBlockAlloca(f, argName, arg.getType());
            builder_->CreateStore(&arg, Alloca);
            named_values_[argName] = {Alloca, argName == "self" ? className : "Int"};
        }

        auto bodyArr = ctx_.getArrayElements(funcNode[4]);
        for (const auto& stmt : bodyArr) compileStatement(stmt);

        // Ensure every basic block has a terminator. `getTerminator()` is
        // unreliable on some LLVM builds, so check the last instruction directly.
        for (auto& block : *f) {
            bool hasTerm = !block.empty() && block.back().isTerminator();
            if (!hasTerm) {
                builder_->SetInsertPoint(&block);
                if (f->getReturnType()->isVoidTy()) {
                    builder_->CreateRetVoid();
                } else {
                    builder_->CreateRet(llvm::ConstantInt::get(*context_, llvm::APInt(32, 0, true)));
                }
            }
        }

        llvm::verifyFunction(*f);
        return f;
    }

    // Resolves memory addresses, handling both heap (class) and stack (struct) base pointers.
    llvm::Value* compileLValue(const EvoParser::Value& expr, std::string& outTypeName) {
        if (expr.type == EvoParser::ValueType::StringView) {
            std::string varName = std::string(EvoParser::toString(expr));
            auto it = named_values_.find(varName);
            if (it == named_values_.end()) { llvm::errs() << "Unknown var: " << varName << "\n"; return nullptr; }
            outTypeName = it->second.typeName;
            return it->second.alloca;
        }

        auto arr = ctx_.getArrayElements(expr);
        if (arr.size > 0) {
            std::string_view nodeType = EvoParser::toString(arr[0]);
            if (nodeType == "MemberAccess" || nodeType == "SelfAccess") {
                std::string baseName, propName;
                if (nodeType == "MemberAccess") {
                    baseName = std::string(EvoParser::toString(arr[1]));
                    propName = std::string(EvoParser::toString(arr[2]));
                } else {
                    baseName = "self";
                    propName = std::string(EvoParser::toString(arr[1]));
                }

                auto it = named_values_.find(baseName);
                if (it == named_values_.end()) return nullptr;
                std::string typeName = it->second.typeName;
                if (!structs_.count(typeName)) return nullptr;

                StructInfo& info = structs_[typeName];
                unsigned idx = info.fieldIndices[propName];
                outTypeName = "Int";

                llvm::Value* basePtr = it->second.alloca;
                // If it's a class, the local variable is a pointer into the heap;
                // we MUST dereference it before calculating GEP offsets.
                // 'self' is always a pointer stored in its alloca, so load it too.
                if (info.isReferenceType || nodeType == "SelfAccess") {
                    basePtr = builder_->CreateLoad(
                        llvm::PointerType::getUnqual(*context_),
                        basePtr, "heap_deref");
                }

                return builder_->CreateStructGEP(info.type, basePtr, idx, propName + "_ptr");
            }
        }
        return nullptr;
    }

    llvm::Value* compileStatement(const EvoParser::Value& stmtVal) {
        auto stmtArr = ctx_.getArrayElements(stmtVal);
        if (stmtArr.size == 0) return nullptr;

        std::string_view nodeType = EvoParser::toString(stmtArr[0]);

        if (nodeType == "Return") {
            llvm::Value* retVal = nullptr;
            if (!EvoParser::isNull(stmtArr[1])) retVal = compileExpression(stmtArr[1]);
            if (retVal) return builder_->CreateRet(retVal);
            return builder_->CreateRetVoid();
        }

        if (nodeType == "Property") {
            std::string varName = std::string(EvoParser::toString(stmtArr[2]));
            std::string varType = "Int";
            bool typeExplicit = !EvoParser::isNull(stmtArr[3]);
            if (typeExplicit) varType = std::string(EvoParser::toString(stmtArr[3]));

            // Classify the RHS: constructor call, alias of a typed variable,
            // or a generic expression. This lets us choose the right storage.
            bool isConstructorCall = false;
            bool isAliasCopy = false; // var b = a  — 'a' is a known struct/class local

            llvm::Value* initVal = nullptr;

            if (!EvoParser::isNull(stmtArr[4])) {
                auto rhs = stmtArr[4];

                if (rhs.type == EvoParser::ValueType::Array) {
                    auto rhsArr = ctx_.getArrayElements(rhs);
                    std::string_view rhsKind = EvoParser::toString(rhsArr[0]);
                    if (rhsKind == "Call" && rhsArr[1].type == EvoParser::ValueType::StringView) {
                        std::string callee = std::string(EvoParser::toString(rhsArr[1]));
                        if (structs_.count(callee)) {
                            varType = callee;
                            isConstructorCall = true;
                        }
                    } else if (!typeExplicit) {
                        if (rhsKind == "String") varType = "String";
                        else if (rhsKind == "Float") varType = "Float";
                        else if (rhsKind == "Bool") varType = "Int";
                    }
                } else if (rhs.type == EvoParser::ValueType::StringView) {
                    // var b = a — infer type from existing variable.
                    std::string refName = std::string(EvoParser::toString(rhs));
                    auto refIt = named_values_.find(refName);
                    if (refIt != named_values_.end() && structs_.count(refIt->second.typeName)) {
                        varType = refIt->second.typeName;
                        isAliasCopy = true;
                    }
                }

                if (!isConstructorCall) initVal = compileExpression(rhs);
            }

            // Determine storage type for the local.
            llvm::Type* llvmTy;
            if (structs_.count(varType)) {
                // Class local stores a heap pointer; struct local stores the value inline.
                if (structs_[varType].isReferenceType)
                    llvmTy = llvm::PointerType::getUnqual(*context_);
                else
                    llvmTy = structs_[varType].type;
            } else {
                llvmTy = getLLVMType(varType);
            }

            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::AllocaInst* Alloca = CreateEntryBlockAlloca(TheFunction, varName, llvmTy);
            named_values_[varName] = {Alloca, varType};

            if (isConstructorCall && structs_.count(varType)) {
                if (structs_[varType].isReferenceType) {
                    // Heap allocation: malloc(sizeof(T)) and stash the pointer.
                    uint64_t classSize = module_->getDataLayout().getTypeAllocSize(structs_[varType].type);
                    llvm::Value* sizeVal = llvm::ConstantInt::get(
                        llvm::Type::getInt64Ty(*context_), classSize);
                    llvm::Value* heapPtr = builder_->CreateCall(
                        getMalloc(), {sizeVal}, "new_class_alloc");
                    builder_->CreateStore(heapPtr, Alloca);
                }
                // Structs: leave the stack slot uninitialized; user assigns fields.
                (void)isAliasCopy;
            } else if (initVal) {
                // Pure value store — LLVM emits a struct-copy for struct types,
                // a pointer-copy for classes, and a scalar store for primitives.
                builder_->CreateStore(initVal, Alloca);
            }
            return nullptr;
        }

        if (nodeType == "Assign") {
            std::string dummyType;
            llvm::Value* lhsPtr = compileLValue(stmtArr[2], dummyType);
            if (!lhsPtr) return nullptr;

            llvm::Value* rhsVal = compileExpression(stmtArr[3]);
            if (!rhsVal) return nullptr;
            builder_->CreateStore(rhsVal, lhsPtr);
            return rhsVal;
        }

        if (nodeType == "If") {
            llvm::Value* condV = compileExpression(stmtArr[1]);
            condV = builder_->CreateICmpNE(
                condV, llvm::ConstantInt::get(*context_, llvm::APInt(32, 0, true)), "ifcond");

            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::BasicBlock* ThenBB = llvm::BasicBlock::Create(*context_, "then", TheFunction);
            llvm::BasicBlock* ElseBB = llvm::BasicBlock::Create(*context_, "else");
            llvm::BasicBlock* MergeBB = llvm::BasicBlock::Create(*context_, "ifcont");

            bool hasElse = !EvoParser::isNull(stmtArr[3]);
            builder_->CreateCondBr(condV, ThenBB, hasElse ? ElseBB : MergeBB);

            builder_->SetInsertPoint(ThenBB);
            auto thenArr = ctx_.getArrayElements(stmtArr[2]);
            for (const auto& s : thenArr) compileStatement(s);
            {
                auto* curBB = builder_->GetInsertBlock();
                if (curBB->empty() || !curBB->back().isTerminator()) builder_->CreateBr(MergeBB);
            }

            if (hasElse) {
                TheFunction->insert(TheFunction->end(), ElseBB);
                builder_->SetInsertPoint(ElseBB);
                auto elseArr = ctx_.getArrayElements(stmtArr[3]);
                for (const auto& s : elseArr) compileStatement(s);
                auto* curBB = builder_->GetInsertBlock();
                if (curBB->empty() || !curBB->back().isTerminator()) builder_->CreateBr(MergeBB);
            } else { delete ElseBB; }

            TheFunction->insert(TheFunction->end(), MergeBB);
            builder_->SetInsertPoint(MergeBB);
            return nullptr;
        }

        if (nodeType == "While") {
            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::BasicBlock* CondBB = llvm::BasicBlock::Create(*context_, "whilecond", TheFunction);
            llvm::BasicBlock* LoopBB = llvm::BasicBlock::Create(*context_, "whileloop", TheFunction);
            llvm::BasicBlock* AfterBB = llvm::BasicBlock::Create(*context_, "whilecont", TheFunction);

            builder_->CreateBr(CondBB);
            builder_->SetInsertPoint(CondBB);

            llvm::Value* condV = compileExpression(stmtArr[1]);
            condV = builder_->CreateICmpNE(
                condV, llvm::ConstantInt::get(*context_, llvm::APInt(32, 0, true)), "loopcond");
            builder_->CreateCondBr(condV, LoopBB, AfterBB);

            builder_->SetInsertPoint(LoopBB);
            auto bodyArr = ctx_.getArrayElements(stmtArr[2]);
            for (const auto& s : bodyArr) compileStatement(s);
            {
                auto* curBB = builder_->GetInsertBlock();
                if (curBB->empty() || !curBB->back().isTerminator()) builder_->CreateBr(CondBB);
            }

            builder_->SetInsertPoint(AfterBB);
            return nullptr;
        }

        return compileExpression(stmtVal);
    }

    llvm::Value* compileExpression(const EvoParser::Value& exprVal) {
        if (exprVal.type == EvoParser::ValueType::StringView) {
            std::string varName = std::string(EvoParser::toString(exprVal));
            auto it = named_values_.find(varName);
            if (it == named_values_.end()) {
                llvm::errs() << "Unknown var: " << varName << "\n";
                return nullptr;
            }

            llvm::Type* ty = getLLVMType(it->second.typeName);
            // For structs, this loads the whole value (auto-memcpy on store => deep copy).
            // For classes, this loads the heap pointer (pointer-copy on store => shared ref).
            return builder_->CreateLoad(ty, it->second.alloca, varName.c_str());
        }

        auto exprArr = ctx_.getArrayElements(exprVal);
        if (exprArr.size == 0) return nullptr;

        std::string_view nodeType = EvoParser::toString(exprArr[0]);

        // Lower strings to global constant memory, honoring common escapes.
        if (nodeType == "String") {
            std::string raw = std::string(EvoParser::toString(exprArr[1]));
            std::string val;
            val.reserve(raw.size());
            for (size_t i = 0; i < raw.size(); ++i) {
                char c = raw[i];
                if (c == '\\' && i + 1 < raw.size()) {
                    char nxt = raw[++i];
                    switch (nxt) {
                        case 'n': val.push_back('\n'); break;
                        case 't': val.push_back('\t'); break;
                        case 'r': val.push_back('\r'); break;
                        case '0': val.push_back('\0'); break;
                        case '\\': val.push_back('\\'); break;
                        case '"': val.push_back('"'); break;
                        case '\'': val.push_back('\''); break;
                        default: val.push_back('\\'); val.push_back(nxt); break;
                    }
                } else {
                    val.push_back(c);
                }
            }
            return builder_->CreateGlobalString(val, "str");
        }

        if (nodeType == "MemberAccess" || nodeType == "SelfAccess") {
            std::string dummyType;
            llvm::Value* ptr = compileLValue(exprVal, dummyType);
            if (!ptr) return nullptr;
            return builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), ptr, "loadtmp");
        }

        if (nodeType == "Int") {
            int val = std::stoi(std::string(EvoParser::toString(exprArr[1])));
            return llvm::ConstantInt::get(*context_, llvm::APInt(32, val, true));
        }

        if (nodeType == "Call") {
            auto targetNode = exprArr[1];

            if (targetNode.type == EvoParser::ValueType::StringView) {
                std::string callee = std::string(EvoParser::toString(targetNode));
                if (structs_.count(callee)) return nullptr; // constructor handled in Property

                llvm::Function* calleeF = module_->getFunction(callee);
                if (!calleeF) { llvm::errs() << "Unknown function: " << callee << "\n"; return nullptr; }

                std::vector<llvm::Value*> argsV;
                if (!EvoParser::isNull(exprArr[2])) {
                    auto argsArr = ctx_.getArrayElements(exprArr[2]);
                    for (const auto& arg : argsArr) argsV.push_back(compileExpression(arg));
                }
                // LLVM forbids naming results of void-returning calls.
                const char* callName = calleeF->getReturnType()->isVoidTy() ? "" : "calltmp";
                return builder_->CreateCall(calleeF, argsV, callName);
            }
            else {
                auto targetArr = ctx_.getArrayElements(targetNode);
                if (EvoParser::toString(targetArr[0]) == "MemberAccess") {
                    std::string baseName = std::string(EvoParser::toString(targetArr[1]));
                    std::string methodName = std::string(EvoParser::toString(targetArr[2]));

                    auto it = named_values_.find(baseName);
                    if (it == named_values_.end()) {
                        llvm::errs() << "Unknown var: " << baseName << "\n";
                        return nullptr;
                    }
                    std::string typeName = it->second.typeName;

                    llvm::Function* calleeF = module_->getFunction(typeName + "_" + methodName);
                    if (!calleeF) { llvm::errs() << "Unknown method: " << methodName << "\n"; return nullptr; }

                    std::vector<llvm::Value*> argsV;
                    // Inject 'self'. For classes pass the heap pointer; for structs pass
                    // the pointer to the stack-allocated struct.
                    llvm::Value* selfArg = it->second.alloca;
                    if (structs_.count(typeName) && structs_[typeName].isReferenceType) {
                        selfArg = builder_->CreateLoad(
                            llvm::PointerType::getUnqual(*context_), selfArg, "self_heap");
                    }
                    argsV.push_back(selfArg);

                    if (!EvoParser::isNull(exprArr[2])) {
                        auto argsArr = ctx_.getArrayElements(exprArr[2]);
                        for (const auto& arg : argsArr) argsV.push_back(compileExpression(arg));
                    }
                    const char* callName = calleeF->getReturnType()->isVoidTy() ? "" : "methodtmp";
                    return builder_->CreateCall(calleeF, argsV, callName);
                }
            }
        }

        if (nodeType == "Binary") {
            std::string op = std::string(EvoParser::toString(exprArr[1]));
            llvm::Value* L = compileExpression(exprArr[2]);
            llvm::Value* R = compileExpression(exprArr[3]);
            if (!L || !R) return nullptr;

            if (op == "+") return builder_->CreateAdd(L, R, "addtmp");
            if (op == "-") return builder_->CreateSub(L, R, "subtmp");
            if (op == "*") return builder_->CreateMul(L, R, "multmp");
            if (op == "/") return builder_->CreateSDiv(L, R, "divtmp");

            llvm::Value* cmp = nullptr;
            if (op == "==") cmp = builder_->CreateICmpEQ(L, R, "eqtmp");
            if (op == "!=") cmp = builder_->CreateICmpNE(L, R, "netmp");
            if (op == "<")  cmp = builder_->CreateICmpSLT(L, R, "lttmp");
            if (op == ">")  cmp = builder_->CreateICmpSGT(L, R, "gttmp");
            if (op == "<=") cmp = builder_->CreateICmpSLE(L, R, "sletmp");
            if (op == ">=") cmp = builder_->CreateICmpSGE(L, R, "sgetmp");

            if (cmp) return builder_->CreateZExt(cmp, llvm::Type::getInt32Ty(*context_), "booltmp");
        }

        return nullptr;
    }
};

} // namespace Elegant

// Ensure standard C runtime symbols are available to the JIT via host linkage.
#include <stdio.h>

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cout << "Elegant Compiler Toolchain\n";
        return 1;
    }

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
        std::cerr << "\n❌ Syntax Error\n" << err.what() << "\n";
        return 1;
    }

    std::string moduleName = std::filesystem::path(input_file).stem().string();
    Elegant::LLVMCompiler compiler(ctx, moduleName);

    compiler.compile();

    if (!compileOnly) {
        std::cout << "\n--- Generated LLVM IR ---\n";
        compiler.dumpIR();
        return compiler.executeJIT();
    } else {
        std::string obj_file = moduleName + ".obj";
        std::string exe_file = moduleName + ".exe";

        if (compiler.emitObjectFile(obj_file)) {
            std::cout << "✅ Emitted native object: " << obj_file << "\n";
            std::cout << "🚀 Linking standalone executable...\n";
            std::string linkCmd = "lld-link.exe " + obj_file + " /entry:main /subsystem:console /out:"
                + exe_file + " /defaultlib:msvcrt.lib /defaultlib:ucrt.lib /defaultlib:kernel32.lib";
            std::system(linkCmd.c_str());
            std::cout << "✅ Built executable: " << exe_file << "\n";
        }
    }
    return 0;
}
