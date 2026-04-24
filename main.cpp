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

struct StructInfo {
    llvm::StructType* type;
    std::unordered_map<std::string, unsigned> fieldIndices;
    std::vector<llvm::Type*> fieldTypes;
    bool isReferenceType;
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

    llvm::Function* getMalloc() {
        if (auto* M = module_->getFunction("malloc")) return M;
        auto* FT = llvm::FunctionType::get(llvm::PointerType::getUnqual(*context_), {llvm::Type::getInt64Ty(*context_)}, false);
        return llvm::Function::Create(FT, llvm::Function::ExternalLinkage, "malloc", module_.get());
    }

    // FEATURE: Swift "Fat Pointer" Array Definition
    // Memory Layout: { i32 capacity, i32 count, i32* buffer_ptr }
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

    llvm::Type* getLLVMType(const std::string& typeName) {
        if (typeName == "Int") return llvm::Type::getInt32Ty(*context_);
        if (typeName == "Float") return llvm::Type::getDoubleTy(*context_);
        if (typeName == "String" || typeName == "Array") return llvm::PointerType::getUnqual(*context_); 
        if (typeName == "Void" || typeName == "") return llvm::Type::getVoidTy(*context_);
        
        if (structs_.count(typeName)) {
            if (structs_[typeName].isReferenceType) return llvm::PointerType::getUnqual(*context_);
            else return structs_[typeName].type;
        }
        return llvm::Type::getInt32Ty(*context_); 
    }

    void compile() {
        auto declarations = ctx_.getArrayElements(ctx_.root);
        
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
                std::string retTypeName = EvoParser::isNull(declArr[3]) ? "Void" : std::string(EvoParser::toString(declArr[3]));
                llvm::FunctionType* ft = llvm::FunctionType::get(getLLVMType(retTypeName), argTypes, isVarArg);
                llvm::Function::Create(ft, llvm::Function::ExternalLinkage, extName, module_.get());
            }
        }
        
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
                        std::string propType = EvoParser::isNull(memArr[3]) ? "Int" : std::string(EvoParser::toString(memArr[3]));
                        info.fieldIndices[propName] = idx++;
                        info.fieldTypes.push_back(getLLVMType(propType)); 
                    }
                }
                info.type->setBody(info.fieldTypes);
            }
        }
        
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

        auto processSymbols = llvm::orc::DynamicLibrarySearchGenerator::GetForCurrentProcess(jit->getDataLayout().getGlobalPrefix());
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

        // Ensure every basic block has a terminator.
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

    llvm::Value* compileLValue(const EvoParser::Value& expr, std::string& outTypeName) {
        if (expr.type == EvoParser::ValueType::StringView) {
            std::string varName = std::string(EvoParser::toString(expr));
            auto it = named_values_.find(varName);
            if (it == named_values_.end()) return nullptr;
            outTypeName = it->second.typeName;
            return it->second.alloca;
        }

        auto arr = ctx_.getArrayElements(expr);
        if (arr.size > 0) {
            std::string_view nodeType = EvoParser::toString(arr[0]);
            
            // FEATURE: Swift Array Subscript — Fat Pointer dereferencing
            if (nodeType == "Subscript") {
                std::string baseName = std::string(EvoParser::toString(arr[1]));
                llvm::Value* indexVal = compileExpression(arr[2]);

                auto it = named_values_.find(baseName);
                if (it == named_values_.end()) return nullptr;

                outTypeName = "Int";

                // 1. Load the SwiftArray struct pointer from the variable slot.
                llvm::Value* arrObj = builder_->CreateLoad(llvm::PointerType::getUnqual(*context_), it->second.alloca, "arr_obj");

                // 2. GEP into the struct (field 2) to reach the buffer pointer slot, then load it.
                llvm::Value* bufPtrAddr = builder_->CreateStructGEP(getSwiftArrayType(), arrObj, 2, "buf_ptr_addr");
                llvm::Value* bufPtr = builder_->CreateLoad(llvm::PointerType::getUnqual(*context_), bufPtrAddr, "buf_ptr");

                // 3. GEP into the contiguous data buffer using the user's index.
                return builder_->CreateGEP(llvm::Type::getInt32Ty(*context_), bufPtr, indexVal, "subscript_ptr");
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

                auto it = named_values_.find(baseName);
                if (it == named_values_.end()) return nullptr;
                std::string typeName = it->second.typeName;
                if (!structs_.count(typeName)) return nullptr;
                
                StructInfo& info = structs_[typeName];
                unsigned idx = info.fieldIndices[propName];
                outTypeName = "Int"; 
                
                llvm::Value* basePtr = it->second.alloca;
                if (info.isReferenceType || nodeType == "SelfAccess") {
                    basePtr = builder_->CreateLoad(llvm::PointerType::getUnqual(*context_), basePtr, "heap_deref");
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

            bool isConstructorCall = false;
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
                    } else if (rhsKind == "ArrayLiteral") {
                        varType = "Array"; // Type Inference for Arrays
                    } else if (!typeExplicit) {
                        if (rhsKind == "String") varType = "String";
                        else if (rhsKind == "Float") varType = "Float";
                        else if (rhsKind == "Bool") varType = "Int";
                    }
                } else if (rhs.type == EvoParser::ValueType::StringView) {
                    // var b = a — infer struct/class type from existing variable.
                    std::string refName = std::string(EvoParser::toString(rhs));
                    auto refIt = named_values_.find(refName);
                    if (refIt != named_values_.end() && structs_.count(refIt->second.typeName)) {
                        varType = refIt->second.typeName;
                    }
                }
                if (!isConstructorCall) initVal = compileExpression(rhs);
            }

            llvm::Type* llvmTy = getLLVMType(varType);
            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::AllocaInst* Alloca = CreateEntryBlockAlloca(TheFunction, varName, llvmTy);
            named_values_[varName] = {Alloca, varType};

            if (isConstructorCall && structs_.count(varType)) {
                if (structs_[varType].isReferenceType) {
                    uint64_t classSize = module_->getDataLayout().getTypeAllocSize(structs_[varType].type);
                    llvm::Value* sizeVal = llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context_), classSize);
                    llvm::Value* heapPtr = builder_->CreateCall(getMalloc(), {sizeVal}, "new_class_alloc");
                    builder_->CreateStore(heapPtr, Alloca);
                }
                // Value-type structs: leave slot uninitialized; user assigns fields.
            } else if (initVal) {
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

        // FEATURE: Swift For-In Range Iterator Loop
        if (nodeType == "For") {
            std::string varName = std::string(EvoParser::toString(stmtArr[1]));
            llvm::Value* startV = compileExpression(stmtArr[2]);
            llvm::Value* endV = compileExpression(stmtArr[3]);
            
            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::AllocaInst* Alloca = CreateEntryBlockAlloca(TheFunction, varName, llvm::Type::getInt32Ty(*context_));
            builder_->CreateStore(startV, Alloca);
            
            auto oldVal = named_values_[varName];
            named_values_[varName] = {Alloca, "Int"};
            
            llvm::BasicBlock* CondBB = llvm::BasicBlock::Create(*context_, "forcond", TheFunction);
            llvm::BasicBlock* LoopBB = llvm::BasicBlock::Create(*context_, "forloop", TheFunction);
            llvm::BasicBlock* AfterBB = llvm::BasicBlock::Create(*context_, "forcont", TheFunction);
            
            builder_->CreateBr(CondBB);
            builder_->SetInsertPoint(CondBB);
            
            llvm::Value* currV = builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), Alloca, varName);
            llvm::Value* condV = builder_->CreateICmpSLE(currV, endV, "loopcond");
            builder_->CreateCondBr(condV, LoopBB, AfterBB);
            
            builder_->SetInsertPoint(LoopBB);
            auto bodyArr = ctx_.getArrayElements(stmtArr[4]);
            for (const auto& s : bodyArr) compileStatement(s);
            
            llvm::Value* stepV = builder_->CreateAdd(builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), Alloca), llvm::ConstantInt::get(*context_, llvm::APInt(32, 1, true)), "nextval");
            builder_->CreateStore(stepV, Alloca);
            builder_->CreateBr(CondBB);
            
            builder_->SetInsertPoint(AfterBB);
            named_values_[varName] = oldVal; // Shadow scope safety
            return nullptr;
        }

        if (nodeType == "If" || nodeType == "While") {
            llvm::Value* condV = compileExpression(stmtArr[1]);
            condV = builder_->CreateICmpNE(condV, llvm::ConstantInt::get(*context_, llvm::APInt(32, 0, true)), "cond");
            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::BasicBlock* ThenBB = llvm::BasicBlock::Create(*context_, "block", TheFunction);
            llvm::BasicBlock* MergeBB = llvm::BasicBlock::Create(*context_, "cont");
            builder_->CreateCondBr(condV, ThenBB, MergeBB);
            builder_->SetInsertPoint(ThenBB);
            auto arr = ctx_.getArrayElements(stmtArr[2]);
            for (const auto& s : arr) compileStatement(s);
            builder_->CreateBr(MergeBB);
            TheFunction->insert(TheFunction->end(), MergeBB);
            builder_->SetInsertPoint(MergeBB);
            return nullptr;
        }

        return compileExpression(stmtVal);
    }

    llvm::Value* compileExpression(const EvoParser::Value& exprVal) {
        if (exprVal.type == EvoParser::ValueType::StringView) {
            std::string varName = std::string(EvoParser::toString(exprVal));
            auto it = named_values_.find(varName);
            if (it == named_values_.end()) return nullptr; 
            return builder_->CreateLoad(getLLVMType(it->second.typeName), it->second.alloca, varName.c_str());
        }

        auto exprArr = ctx_.getArrayElements(exprVal);
        if (exprArr.size == 0) return nullptr;
        std::string_view nodeType = EvoParser::toString(exprArr[0]);

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

        // FEATURE: Swift Array Allocation — build the Fat Pointer
        // Layout: { i32 capacity, i32 count, i32* buffer_ptr }
        if (nodeType == "ArrayLiteral") {
            std::vector<llvm::Value*> elements;
            if (!EvoParser::isNull(exprArr[1])) {
                auto argsArr = ctx_.getArrayElements(exprArr[1]);
                for (const auto& arg : argsArr) elements.push_back(compileExpression(arg));
            }

            llvm::StructType* arrTy = getSwiftArrayType();
            uint64_t structSize = module_->getDataLayout().getTypeAllocSize(arrTy);

            // 1. Malloc the SwiftArray struct (the "fat pointer" object).
            llvm::Value* arrHeapPtr = builder_->CreateCall(
                getMalloc(),
                {llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context_), structSize)},
                "arr_obj");

            // 2. Malloc the contiguous data buffer (32-bit ints).
            uint64_t bufSize = elements.size() * 4;
            llvm::Value* bufHeapPtr = builder_->CreateCall(
                getMalloc(),
                {llvm::ConstantInt::get(llvm::Type::getInt64Ty(*context_), bufSize)},
                "arr_buf");

            // 3. Store Capacity, Count, and Buffer Pointer into the struct.
            llvm::Value* countConst = llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), elements.size());
            builder_->CreateStore(countConst, builder_->CreateStructGEP(arrTy, arrHeapPtr, 0, "cap_ptr"));
            builder_->CreateStore(countConst, builder_->CreateStructGEP(arrTy, arrHeapPtr, 1, "count_ptr"));
            builder_->CreateStore(bufHeapPtr, builder_->CreateStructGEP(arrTy, arrHeapPtr, 2, "buf_slot"));

            // 4. Populate the data buffer.
            for (size_t i = 0; i < elements.size(); i++) {
                llvm::Value* idxVal = llvm::ConstantInt::get(llvm::Type::getInt32Ty(*context_), i);
                llvm::Value* elemPtr = builder_->CreateGEP(llvm::Type::getInt32Ty(*context_), bufHeapPtr, idxVal, "elem_ptr");
                builder_->CreateStore(elements[i], elemPtr);
            }
            return arrHeapPtr;
        }

        if (nodeType == "MemberAccess" || nodeType == "SelfAccess" || nodeType == "Subscript") {
            // FEATURE: Built-in Swift Array `.count` property.
            // Checked first so user-defined structs named "Array" still work via the lvalue path.
            if (nodeType == "MemberAccess") {
                std::string baseName = std::string(EvoParser::toString(exprArr[1]));
                std::string propName = std::string(EvoParser::toString(exprArr[2]));
                auto it = named_values_.find(baseName);
                if (it != named_values_.end() && it->second.typeName == "Array" && propName == "count") {
                    llvm::Value* arrObj = builder_->CreateLoad(llvm::PointerType::getUnqual(*context_), it->second.alloca, "arr_obj");
                    llvm::Value* countPtr = builder_->CreateStructGEP(getSwiftArrayType(), arrObj, 1, "count_ptr");
                    return builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), countPtr, "count_val");
                }
            }

            std::string dummyType;
            llvm::Value* ptr = compileLValue(exprVal, dummyType);
            if (!ptr) return nullptr;
            return builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), ptr, "loadtmp");
        }

        if (nodeType == "Int") {
            return llvm::ConstantInt::get(*context_, llvm::APInt(32, std::stoi(std::string(EvoParser::toString(exprArr[1]))), true));
        }

        if (nodeType == "Call") {
            auto targetNode = exprArr[1];
            if (targetNode.type == EvoParser::ValueType::StringView) {
                std::string callee = std::string(EvoParser::toString(targetNode));
                if (structs_.count(callee)) return nullptr; 
                llvm::Function* calleeF = module_->getFunction(callee);
                
                std::vector<llvm::Value*> argsV;
                if (!EvoParser::isNull(exprArr[2])) {
                    auto argsArr = ctx_.getArrayElements(exprArr[2]);
                    for (const auto& arg : argsArr) argsV.push_back(compileExpression(arg));
                }
                return builder_->CreateCall(calleeF, argsV, "calltmp");
            } 
            else {
                auto targetArr = ctx_.getArrayElements(targetNode);
                if (EvoParser::toString(targetArr[0]) == "MemberAccess") {
                    std::string baseName = std::string(EvoParser::toString(targetArr[1]));
                    std::string methodName = std::string(EvoParser::toString(targetArr[2]));
                    
                    auto it = named_values_.find(baseName);
                    std::string typeName = it->second.typeName;
                    
                    llvm::Function* calleeF = module_->getFunction(typeName + "_" + methodName);
                    std::vector<llvm::Value*> argsV;
                    
                    llvm::Value* selfArg = it->second.alloca;
                    if (structs_[typeName].isReferenceType) {
                        selfArg = builder_->CreateLoad(llvm::PointerType::getUnqual(*context_), selfArg, "self_heap");
                    }
                    argsV.push_back(selfArg); 
                    
                    if (!EvoParser::isNull(exprArr[2])) {
                        auto argsArr = ctx_.getArrayElements(exprArr[2]);
                        for (const auto& arg : argsArr) argsV.push_back(compileExpression(arg));
                    }
                    return builder_->CreateCall(calleeF, argsV, "methodtmp");
                }
            }
        }

        if (nodeType == "Binary") {
            std::string op = std::string(EvoParser::toString(exprArr[1]));
            llvm::Value* L = compileExpression(exprArr[2]);
            llvm::Value* R = compileExpression(exprArr[3]);
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
            std::string linkCmd = "lld-link.exe " + obj_file + " /entry:main /subsystem:console /out:" + exe_file + " /defaultlib:msvcrt.lib /defaultlib:ucrt.lib /defaultlib:kernel32.lib";
            std::system(linkCmd.c_str());
        }
    }
    return 0;
}
