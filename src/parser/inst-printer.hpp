# ifndef __INST_PRINTER_HPP__
# define __INST_PRINTER_HPP__

# include "llvm/IR/InstVisitor.h"
# include "llvm/Support/raw_ostream.h"

# include <map>
# include <string>
# include <memory>

using namespace llvm;

struct InstPrinter : public InstVisitor <InstPrinter>
{
  InstPrinter () {}
  // --------------------------------------------------
  // Specific Instruction type classes
  void visitReturnInst (const ReturnInst &inst);
  void visitBranchInst (const BranchInst &inst);
  void visitICmpInst (const ICmpInst &inst);  
  void visitAllocaInst (const AllocaInst &inst);
  void visitLoadInst (const LoadInst &inst);
  void visitStoreInst (const StoreInst &inst);
  
  // --------------------------------------------------
private:
  void PrintOpList (const llvm::Instruction *inst);
  void PrintPrefix (const llvm::Instruction *inst);
  void PrintArgOp (const llvm::Argument *arg);
  void PrintAllocaOp (const llvm::AllocaInst *op);

  class RegisterMap
  {
  public:
    typedef unsigned RegisterNumber;
    void Add (const llvm::Instruction *inst);
    RegisterNumber GetNumber (const llvm::Instruction *inst);
    std::string GetName (const llvm::Instruction *inst);
  private:
    std::map <const llvm::Instruction*, RegisterNumber> map_;
    RegisterNumber counter_ = 0;
  } register_map_;
};

# endif /* __INST_PRINTER_HPP__ */
