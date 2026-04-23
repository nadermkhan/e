#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <filesystem>
#include <unordered_map>
#include <memory>
#include <system_error>

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

// === Evo Parser Header ===
#include <ElegantParser.hpp>

namespace Elegant {

class LLVMCompiler {
    EvoParser::ParseContext& ctx_;
    std::unique_ptr<llvm::LLVMContext> context_;
    std::unique_ptr<llvm::Module> module_;
    std::unique_ptr<llvm::IRBuilder<>> builder_;
    std::unordered_map<std::string, llvm::Value*> named_values_;

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
            }
        }
    }

    void dumpIR() {
        module_->print(llvm::outs(), nullptr);
    }

    bool emitObjectFile(const std::string& filename) {
        llvm::InitializeAllTargetInfos();
        llvm::InitializeAllTargets();
        llvm::InitializeAllTargetMCs();
        llvm::InitializeAllAsmParsers();
        llvm::InitializeAllAsmPrinters();

        // LLVM 18 Fix: Explicit llvm::Triple 
        std::string targetTripleStr = llvm::sys::getDefaultTargetTriple();
        llvm::Triple targetTriple(targetTripleStr);
        
        // Pass the object directly, NOT a string
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
        
        // Pass the object directly here too
        auto targetMachine = target->createTargetMachine(targetTriple, cpu, features, opt, rm);

        module_->setDataLayout(targetMachine->createDataLayout());

        std::error_code ec;
        llvm::raw_fd_ostream dest(filename, ec, llvm::sys::fs::OF_None);
        if (ec) {
            llvm::errs() << "Could not open file: " << ec.message();
            return false;
        }

        llvm::legacy::PassManager pass;
        auto fileType = llvm::CodeGenFileType::ObjectFile; 

        if (targetMachine->addPassesToEmitFile(pass, dest, nullptr, fileType)) {
            llvm::errs() << "TargetMachine can't emit a file of this type";
            return false;
        }

        pass.run(*module_);
        dest.flush();
        return true;
    }

private:
    llvm::Function* compileFunction(const EvoParser::ArrayView& funcNode) {
        std::string name = std::string(EvoParser::toString(funcNode[1]));
        
        llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getInt32Ty(*context_), false);
        llvm::Function* f = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, name, module_.get());

        llvm::BasicBlock* bb = llvm::BasicBlock::Create(*context_, "entry", f);
        builder_->SetInsertPoint(bb);
        named_values_.clear();

        auto bodyArr = ctx_.getArrayElements(funcNode[4]);
        for (const auto& stmt : bodyArr) {
            compileStatement(stmt);
        }

        llvm::verifyFunction(*f);
        return f;
    }

    llvm::Value* compileStatement(const EvoParser::Value& stmtVal) {
        auto stmtArr = ctx_.getArrayElements(stmtVal);
        if (stmtArr.size == 0) return nullptr;

        std::string_view nodeType = EvoParser::toString(stmtArr[0]);

        if (nodeType == "Return") {
            llvm::Value* retVal = nullptr;
            if (!EvoParser::isNull(stmtArr[1])) {
                retVal = compileExpression(stmtArr[1]);
            }
            if (retVal) return builder_->CreateRet(retVal);
            return builder_->CreateRetVoid();
        }
        
        return compileExpression(stmtVal);
    }

    llvm::Value* compileExpression(const EvoParser::Value& exprVal) {
        auto exprArr = ctx_.getArrayElements(exprVal);
        if (exprArr.size == 0) return nullptr;

        std::string_view nodeType = EvoParser::toString(exprArr[0]);

        if (nodeType == "Int") {
            int val = std::stoi(std::string(EvoParser::toString(exprArr[1])));
            return llvm::ConstantInt::get(*context_, llvm::APInt(32, val, true));
        }
        if (nodeType == "Float") {
            double val = std::stod(std::string(EvoParser::toString(exprArr[1])));
            return llvm::ConstantFP::get(*context_, llvm::APFloat(val));
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
        }

        return nullptr;
    }
};

} // namespace Elegant

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: elegantc <input.ele>\n";
        return 1;
    }

    std::string input_file = argv[1];
    std::ifstream ifs(input_file);
    if (!ifs) {
        std::cerr << "Error: Cannot open '" << input_file << "'\n";
        return 1;
    }

    std::ostringstream ss;
    ss << ifs.rdbuf();
    std::string source = ss.str();

    std::cout << "🚀 Compiling " << input_file << "...\n";

    EvoParser::Parser parser;
    EvoParser::ParseContext ctx;
    EvoParser::ParseError err;

    if (!parser.try_parse(source, ctx, err)) {
        std::cerr << "\n❌ Syntax Error in " << input_file << "\n";
        std::cerr << err.what() << "\n";
        return 1;
    }

    std::string moduleName = std::filesystem::path(input_file).stem().string();
    Elegant::LLVMCompiler compiler(ctx, moduleName);

    compiler.compile();

    std::cout << "\n--- Generated LLVM IR ---\n";
    compiler.dumpIR();

    std::string obj_file = moduleName + ".obj";
    if (compiler.emitObjectFile(obj_file)) {
        std::cout << "\n✅ Successfully emitted native object: " << obj_file << "\n";
    } else {
        std::cerr << "\n❌ Failed to emit object file.\n";
        return 1;
    }

    return 0;
}