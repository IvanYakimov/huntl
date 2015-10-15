# include "llvm/IR/InstVisitor.h"
# include "llvm/Support/raw_ostream.h"

# ifndef __INST_PRINTER_HPP__
# define __INST_PRINTER_HPP__

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
};

void PrintArgOp (const Argument *op);
void PrintAllocaOp (const AllocaInst *op);

# endif /* __INST_PRINTER_HPP__ */
