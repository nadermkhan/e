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

class LLVMCompiler {
    EvoParser::ParseContext& ctx_;
    std::unique_ptr<llvm::LLVMContext> context_;
    std::unique_ptr<llvm::Module> module_;
    std::unique_ptr<llvm::IRBuilder<>> builder_;

    // Map names to memory allocations (AllocaInst), not raw values. Variables
    // are stack slots that we load from / store to.
    std::unordered_map<std::string, llvm::AllocaInst*> named_values_;

    // OOP registry: class/struct name -> LLVM StructType layout.
    std::unordered_map<std::string, llvm::StructType*> class_types_;

public:
    LLVMCompiler(EvoParser::ParseContext& ctx, const std::string& moduleName)
        : ctx_(ctx) {
        context_ = std::make_unique<llvm::LLVMContext>();
        module_ = std::make_unique<llvm::Module>(moduleName, *context_);
        builder_ = std::make_unique<llvm::IRBuilder<>>(*context_);
    }

    void compile() {
        auto declarations = ctx_.getArrayElements(ctx_.root);
        for (const auto& declVal : declarations) {
            auto declArr = ctx_.getArrayElements(declVal);
            if (declArr.size == 0) continue;

            std::string_view nodeType = EvoParser::toString(declArr[0]);

            if (nodeType == "Function") {
                compileFunction(declArr);
            } else if (nodeType == "Class" || nodeType == "Struct") {
                // Scaffolding for OOP: map AST Class/Struct to an LLVM StructType.
                // Full member layout + method lowering lands in a follow-up.
            }
        }
    }

    void dumpIR() {
        module_->print(llvm::outs(), nullptr);
    }

    int executeJIT() {
        llvm::InitializeNativeTarget();
        llvm::InitializeNativeTargetAsmPrinter();
        llvm::InitializeNativeTargetAsmParser();

        auto jitExpected = llvm::orc::LLJITBuilder().create();
        if (!jitExpected) {
            llvm::errs() << "Failed to create JIT engine.\n";
            return 1;
        }
        auto jit = std::move(jitExpected.get());

        module_->setDataLayout(jit->getDataLayout());

        // Rename the user's `main` to an internal name before handing the module
        // to the JIT. On Windows/MinGW the x86 backend injects an implicit call
        // to `__main` (the MinGW CRT static-init helper) at the entry of any
        // function literally named `main`. That symbol is not available inside
        // the JIT and causes "Symbols not found: [ __main ]". Renaming avoids
        // the injection entirely. AOT object emission keeps the original `main`.
        constexpr const char* kJitEntryName = "__elegant_jit_entry";
        if (auto* userMain = module_->getFunction("main")) {
            userMain->setName(kJitEntryName);
        } else {
            llvm::errs() << "Execution Error: Could not find a 'func main()' to execute.\n";
            return 1;
        }

        auto tsm = llvm::orc::ThreadSafeModule(std::move(module_), std::move(context_));
        if (auto err = jit->addIRModule(std::move(tsm))) {
            llvm::errs() << "Failed to add IR module to JIT.\n";
            return 1;
        }

        auto mainSym = jit->lookup(kJitEntryName);
        if (!mainSym) {
            llvm::errs() << "Execution Error: Could not find a 'func main()' to execute.\n";
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
        if (!target) {
            llvm::errs() << error;
            return false;
        }

        auto cpu = "generic";
        auto features = "";
        llvm::TargetOptions opt;
        auto rm = std::optional<llvm::Reloc::Model>(llvm::Reloc::PIC_);
        auto targetMachine = target->createTargetMachine(targetTriple, cpu, features, opt, rm);

        module_->setDataLayout(targetMachine->createDataLayout());

        std::error_code ec;
        llvm::raw_fd_ostream dest(filename, ec, llvm::sys::fs::OF_None);
        if (ec) {
            llvm::errs() << "Could not open file: " << ec.message();
            return false;
        }

        llvm::legacy::PassManager pass;
        if (targetMachine->addPassesToEmitFile(pass, dest, nullptr, llvm::CodeGenFileType::ObjectFile)) {
            llvm::errs() << "TargetMachine can't emit a file of this type";
            return false;
        }

        pass.run(*module_);
        dest.flush();
        return true;
    }

private:
    // Allocates stack memory for a variable at the start of a function.
    llvm::AllocaInst* CreateEntryBlockAlloca(llvm::Function* TheFunction, const std::string& VarName) {
        llvm::IRBuilder<> TmpB(&TheFunction->getEntryBlock(), TheFunction->getEntryBlock().begin());
        return TmpB.CreateAlloca(llvm::Type::getInt32Ty(*context_), nullptr, VarName);
    }

    llvm::Function* compileFunction(const EvoParser::ArrayView& funcNode) {
        std::string name = std::string(EvoParser::toString(funcNode[1]));

        // 1. Process parameters.
        std::vector<llvm::Type*> argTypes;
        std::vector<std::string> argNames;
        if (!EvoParser::isNull(funcNode[2])) {
            auto paramsArr = ctx_.getArrayElements(funcNode[2]);
            for (const auto& param : paramsArr) {
                auto p = ctx_.getArrayElements(param);
                argNames.push_back(std::string(EvoParser::toString(p[1])));
                argTypes.push_back(llvm::Type::getInt32Ty(*context_));
            }
        }

        // 2. Create the function.
        llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getInt32Ty(*context_), argTypes, false);
        llvm::Function* f = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, name, module_.get());

        // 3. Create the entry block.
        llvm::BasicBlock* bb = llvm::BasicBlock::Create(*context_, "entry", f);
        builder_->SetInsertPoint(bb);
        named_values_.clear();

        // 4. Map arguments to stack slots.
        unsigned idx = 0;
        for (auto& arg : f->args()) {
            std::string argName = argNames[idx++];
            arg.setName(argName);
            llvm::AllocaInst* Alloca = CreateEntryBlockAlloca(f, argName);
            builder_->CreateStore(&arg, Alloca);
            named_values_[argName] = Alloca;
        }

        // 5. Compile the body.
        auto bodyArr = ctx_.getArrayElements(funcNode[4]);
        for (const auto& stmt : bodyArr) compileStatement(stmt);

        llvm::verifyFunction(*f);
        return f;
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
            // Variable declaration: var x = 5
            std::string varName = std::string(EvoParser::toString(stmtArr[2]));
            llvm::Value* initVal = EvoParser::isNull(stmtArr[4])
                ? llvm::ConstantInt::get(*context_, llvm::APInt(32, 0, true))
                : compileExpression(stmtArr[4]);

            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::AllocaInst* Alloca = CreateEntryBlockAlloca(TheFunction, varName);
            builder_->CreateStore(initVal, Alloca);
            named_values_[varName] = Alloca;
            return initVal;
        }

        if (nodeType == "Assign") {
            // Variable mutation: x = 10
            std::string varName = std::string(EvoParser::toString(stmtArr[2]));
            llvm::Value* val = compileExpression(stmtArr[3]);
            auto it = named_values_.find(varName);
            if (it == named_values_.end()) {
                llvm::errs() << "Unknown variable: " << varName << "\n";
                return nullptr;
            }
            builder_->CreateStore(val, it->second);
            return val;
        }

        if (nodeType == "If") {
            // if (cond) { ... } else { ... }
            llvm::Value* condV = compileExpression(stmtArr[1]);
            if (!condV) return nullptr;
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
            } else {
                delete ElseBB;
            }

            TheFunction->insert(TheFunction->end(), MergeBB);
            builder_->SetInsertPoint(MergeBB);
            return nullptr;
        }

        if (nodeType == "While") {
            // while (cond) { ... }
            llvm::Function* TheFunction = builder_->GetInsertBlock()->getParent();
            llvm::BasicBlock* CondBB = llvm::BasicBlock::Create(*context_, "whilecond", TheFunction);
            llvm::BasicBlock* LoopBB = llvm::BasicBlock::Create(*context_, "whileloop", TheFunction);
            llvm::BasicBlock* AfterBB = llvm::BasicBlock::Create(*context_, "whilecont", TheFunction);

            builder_->CreateBr(CondBB);
            builder_->SetInsertPoint(CondBB);

            llvm::Value* condV = compileExpression(stmtArr[1]);
            if (!condV) return nullptr;
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
        // Raw string => variable lookup.
        if (exprVal.type == EvoParser::ValueType::StringView) {
            std::string varName = std::string(EvoParser::toString(exprVal));
            auto it = named_values_.find(varName);
            if (it == named_values_.end()) {
                llvm::errs() << "Unknown var: " << varName << "\n";
                return nullptr;
            }
            return builder_->CreateLoad(llvm::Type::getInt32Ty(*context_), it->second, varName.c_str());
        }

        auto exprArr = ctx_.getArrayElements(exprVal);
        if (exprArr.size == 0) return nullptr;

        std::string_view nodeType = EvoParser::toString(exprArr[0]);

        if (nodeType == "Int") {
            int val = std::stoi(std::string(EvoParser::toString(exprArr[1])));
            return llvm::ConstantInt::get(*context_, llvm::APInt(32, val, true));
        }

        if (nodeType == "Call") {
            std::string callee = std::string(EvoParser::toString(exprArr[1]));
            llvm::Function* calleeF = module_->getFunction(callee);
            if (!calleeF) {
                llvm::errs() << "Unknown function: " << callee << "\n";
                return nullptr;
            }

            std::vector<llvm::Value*> argsV;
            if (!EvoParser::isNull(exprArr[2])) {
                auto argsArr = ctx_.getArrayElements(exprArr[2]);
                for (const auto& arg : argsArr) argsV.push_back(compileExpression(arg));
            }
            return builder_->CreateCall(calleeF, argsV, "calltmp");
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

            // Widen i1 booleans to i32 so they flow through variable slots.
            if (cmp) return builder_->CreateZExt(cmp, llvm::Type::getInt32Ty(*context_), "booltmp");
        }

        return nullptr;
    }
};

} // namespace Elegant

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cout << "Elegant Compiler Toolchain\n";
        std::cout << "Usage (JIT): elegantc <file.ele>\n";
        std::cout << "Usage (AOT): elegantc -c <file.ele>\n";
        return 1;
    }

    bool compileOnly = false;
    std::string input_file = "";

    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        if (arg == "-c") compileOnly = true;
        else input_file = arg;
    }

    if (input_file.empty()) {
        std::cerr << "Error: No input file specified.\n";
        return 1;
    }

    std::ifstream ifs(input_file);
    if (!ifs) {
        std::cerr << "Error: Cannot open '" << input_file << "'\n";
        return 1;
    }

    std::ostringstream ss;
    ss << ifs.rdbuf();
    std::string source = ss.str();

    EvoParser::Parser parser;
    EvoParser::ParseContext ctx;
    EvoParser::ParseError err;

    if (!parser.try_parse(source, ctx, err)) {
        std::cerr << "\nSyntax Error in " << input_file << "\n";
        std::cerr << err.what() << "\n";
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
