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

#include <ElegantParser.hpp> 

namespace Elegant {

struct StructInfo {
    llvm::StructType* type;
    std::unordered_map<std::string, unsigned> fieldIndices;
    std::vector<llvm::Type*> fieldTypes;
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

    void compile() {
        auto declarations = ctx_.getArrayElements(ctx_.root);
        
        // PASS 1: Struct / Class Blueprint Registration
        for (const auto& declVal : declarations) {
            auto declArr = ctx_.getArrayElements(declVal);
            if (declArr.size == 0) continue;
            std::string_view nodeType = EvoParser::toString(declArr[0]);
            
            if (nodeType == "Class" || nodeType == "Struct") {
                std::string name = std::string(EvoParser::toString(declArr[1]));
                structs_[name].type = llvm::StructType::create(*context_, name);
            }
        }
        
        // PASS 2: Memory Layout Mapping (Assigning Memory Offsets to Properties)
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
                        info.fieldIndices[propName] = idx++;
                        info.fieldTypes.push_back(llvm::Type::getInt32Ty(*context_)); // Simplifying to i32 properties
                    }
                }
                info.type->setBody(info.fieldTypes);
            }
        }
        
        // PASS 3: Generate Executable Code (Functions & Methods)
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
                        // Methods get compiled with an implicit 'self' pointer!
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

        auto tsm = llvm::orc::ThreadSafeModule(std::move(module_), std::move(context_));
        if (auto err = jit->addIRModule(std::move(tsm))) return 1;

        auto mainSym = jit->lookup("main");
        if (!mainSym) {
            llvm::errs() << "\n\xE2\x9D\x8C Execution Error: Could not find 'func main()' to execute.\n";
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
        if (!className.empty()) name = className + "_" + name; // e.g. "Point_move"
        
        std::vector<llvm::Type*> argTypes;
        std::vector<std::string> argNames;
        
        // INJECT HIDDEN "self" POINTER FOR OOP METHODS
        if (classType) {
            argTypes.push_back(classType->getPointerTo());
            argNames.push_back("self");
        }

        if (!EvoParser::isNull(funcNode[2])) {
            auto paramsArr = ctx_.getArrayElements(funcNode[2]);
            for (const auto& param : paramsArr) {
                auto p = ctx_.getArrayElements(param);
                argNames.push_back(std::string(EvoParser::toString(p[1])));
                argTypes.push_back(llvm::Type::getInt32Ty(*context_));
            }
        }

        llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getInt32Ty(*context_), argTypes, false);
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

        llvm::verifyFunction(*f);
        return f;
    }

    // Helper: Calculates the exact memory address in RAM for a variable or struct property
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
            
            // External struct access: p.x
            if (nodeType == "MemberAccess") {
                std::string baseName = std::string(EvoParser::toString(arr[1]));
                std::string propName = std::string(EvoParser::toString(arr[2]));

                auto it = named_values_.find(baseName);
                if (it == named_values_.end()) return nullptr;
                std::string typeName = it->second.typeName;
                
                if (!structs_.count(typeName)) return nullptr;
                StructInfo& info = structs_[typeName];
                unsigned idx = info.fieldIndices[propName];

                outTypeName = "Int";
                return builder_->CreateStructGEP(info.type, it->second.alloca, idx, propName + "_ptr");
            }
            // Internal method access: self.x
            else if (nodeType == "SelfAccess") {
                std::string propName = std::string(EvoParser::toString(arr[1]));
                auto it = named_values_.find("self");
                if (it == named_values_.end()) return nullptr;
                
                std::string typeName = it->second.typeName;
                StructInfo& info = structs_[typeName];
                unsigned idx = info.fieldIndices[propName];

                outTypeName = "Int";
                llvm::Value* selfPtr = builder_->CreateLoad(info.type->getPointerTo(), it->second.alloca, "self_load");
                return builder_->CreateStructGEP(info.type, selfPtr, idx, propName + "_ptr");
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
            
            // Allow explicit typing (var x: Point)
            if (!EvoParser::isNull(stmtArr[3])) varType = std::string(EvoParser::toString(stmtArr[3]));
            
            llvm::Value* initVal = nullptr;
            if (!EvoParser::isNull(stmtArr[4])) {
                auto rhs = stmtArr[4];
                // Type Inference for Constructors (var p = Point())
                if (rhs.type == EvoParser::ValueType::Array) {
                    auto rhsArr = ctx_.getArrayElements(rhs);
                    if (EvoParser::toString(rhsArr[0]) == "Call" && rhsArr[1].type == EvoParser::ValueType::StringView) {
                        std::string callee = std::string(EvoParser::toString(rhsArr[1]));
                        if (structs_.count(callee)) varType = callee; 
                    }
                }
                
                // Standard expressions
                if (!structs_.count(varType)) initVal = compileExpression(rhs);
            }

            llvm::Type* llvmTy = llvm::Type::getInt32Ty(*context_);
            if (structs_.count(varType)) llvmTy = structs_[varType].type;

            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::AllocaInst* Alloca = CreateEntryBlockAlloca(TheFunction, varName, llvmTy);
            named_values_[varName] = {Alloca, varType};

            if (initVal && !structs_.count(varType)) builder_->CreateStore(initVal, Alloca);
            return nullptr;
        }

        if (nodeType == "Assign") {
            std::string dummyType;
            llvm::Value* lhsPtr = compileLValue(stmtArr[2], dummyType);
            if (!lhsPtr) return nullptr;

            llvm::Value* rhsVal = compileExpression(stmtArr[3]);
            builder_->CreateStore(rhsVal, lhsPtr);
            return rhsVal;
        }

        // Control Flow: If/While remain unchanged
        if (nodeType == "If") {
            llvm::Value* condV = compileExpression(stmtArr[1]);
            condV = builder_->CreateICmpNE(condV, llvm::ConstantInt::get(*context_, llvm::APInt(32, 0, true)), "ifcond");
            
            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::BasicBlock* ThenBB = llvm::BasicBlock::Create(*context_, "then", TheFunction);
            llvm::BasicBlock* ElseBB = llvm::BasicBlock::Create(*context_, "else");
            llvm::BasicBlock* MergeBB = llvm::BasicBlock::Create(*context_, "ifcont");
            
            bool hasElse = !EvoParser::isNull(stmtArr[3]);
            builder_->CreateCondBr(condV, ThenBB, hasElse ? ElseBB : MergeBB);
            
            builder_->SetInsertPoint(ThenBB);
            auto thenArr = ctx_.getArrayElements(stmtArr[2]);
            for (const auto& s : thenArr) compileStatement(s);
            builder_->CreateBr(MergeBB);
            
            if (hasElse) {
                TheFunction->insert(TheFunction->end(), ElseBB);
                builder_->SetInsertPoint(ElseBB);
                auto elseArr = ctx_.getArrayElements(stmtArr[3]);
                for (const auto& s : elseArr) compileStatement(s);
                builder_->CreateBr(MergeBB);
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
            condV = builder_->CreateICmpNE(condV, llvm::ConstantInt::get(*context_, llvm::APInt(32, 0, true)), "loopcond");
            builder_->CreateCondBr(condV, LoopBB, AfterBB);

            builder_->SetInsertPoint(LoopBB);
            auto bodyArr = ctx_.getArrayElements(stmtArr[2]);
            for (const auto& s : bodyArr) compileStatement(s);
            builder_->CreateBr(CondBB);

            builder_->SetInsertPoint(AfterBB);
            return nullptr;
        }

        return compileExpression(stmtVal);
    }

    llvm::Value* compileExpression(const EvoParser::Value& exprVal) {
        if (exprVal.type == EvoParser::ValueType::StringView) {
            std::string varName = std::string(EvoParser::toString(exprVal));
            auto it = named_values_.find(varName);
            if (it == named_values_.end()) { llvm::errs() << "Unknown var: " << varName << "\n"; return nullptr; }
            return builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), it->second.alloca, varName.c_str());
        }

        auto exprArr = ctx_.getArrayElements(exprVal);
        if (exprArr.size == 0) return nullptr;

        std::string_view nodeType = EvoParser::toString(exprArr[0]);

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
            
            // Standard Function Call: calculate()
            if (targetNode.type == EvoParser::ValueType::StringView) {
                std::string callee = std::string(EvoParser::toString(targetNode));
                if (structs_.count(callee)) return nullptr; // It's a constructor init, handled in Property

                llvm::Function* calleeF = module_->getFunction(callee);
                if (!calleeF) { llvm::errs() << "Unknown function: " << callee << "\n"; return nullptr; }
                
                std::vector<llvm::Value*> argsV;
                if (!EvoParser::isNull(exprArr[2])) {
                    auto argsArr = ctx_.getArrayElements(exprArr[2]);
                    for (const auto& arg : argsArr) argsV.push_back(compileExpression(arg));
                }
                return builder_->CreateCall(calleeF, argsV, "calltmp");
            } 
            // OOP Method Call: p.move()
            else {
                auto targetArr = ctx_.getArrayElements(targetNode);
                if (EvoParser::toString(targetArr[0]) == "MemberAccess") {
                    std::string baseName = std::string(EvoParser::toString(targetArr[1]));
                    std::string methodName = std::string(EvoParser::toString(targetArr[2]));
                    
                    auto it = named_values_.find(baseName);
                    std::string typeName = it->second.typeName;
                    
                    // Route to the mangled static method
                    llvm::Function* calleeF = module_->getFunction(typeName + "_" + methodName);
                    if (!calleeF) { llvm::errs() << "Unknown method: " << methodName << "\n"; return nullptr; }
                    
                    std::vector<llvm::Value*> argsV;
                    argsV.push_back(it->second.alloca); // Inject implicit 'self'
                    
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
        std::cerr << "\n\xE2\x9D\x8C Syntax Error\n" << err.what() << "\n";
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
            std::string linkCmd = "lld-link.exe " + obj_file + " /entry:main /subsystem:console /nodefaultlib /out:" + exe_file;
            std::system(linkCmd.c_str());
        }
    }
    return 0;
}
