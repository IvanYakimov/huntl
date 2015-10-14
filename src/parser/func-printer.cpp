// based on http://llvm.org/docs/WritingAnLLVMPass.html tutorial

# include "llvm/Pass.h"
# include "llvm/IR/Function.h"
# include "llvm/IR/Instruction.h"
# include "llvm/IR/InstIterator.h"
# include "llvm/IR/InstVisitor.h"
# include "llvm/Support/raw_ostream.h"

# include <set>

using namespace llvm;

namespace
{
  struct FuncPrinter : public FunctionPass
  {
    static char ID;
    FuncPrinter () : FunctionPass (ID) {}
    bool runOnFunction (Function &F) override;
  };
}

char FuncPrinter::ID = 0;
static RegisterPass <FuncPrinter> X("FuncPrinter", "Func Printer Pass",
				    false /* Only looks at CFG */,
				    false /* Analysis Pass */);

// TODO: check traversing order
// http://stackoverflow.com/questions/32853884/how-does-the-llvm-instvisitor-traverse-ir
struct Interpreter : public InstVisitor <Interpreter>
{
  Interpreter () {}

  // --------------------------------------------------
  // Specific Instruction type classes
  void visitReturnInst (const ReturnInst &inst)
  {
    errs () << "return inst\n";
  }

  void visitBranchInst (const BranchInst &inst)
  {
    errs () << "branch inst\n";
  }

  void visitICmpInst (const ICmpInst &inst)
  {
    errs () << "icmp inst\n";
  }
  
  void visitAllocaInst (const AllocaInst &inst)
  {
    errs () << "alloca inst";
    auto op_num = inst.getNumOperands ();
    errs () << ": " << op_num << " operands\n";
  }

  void visitLoadInst (const LoadInst &inst)
  {
    // http://www.isi.edu/~pedro/Teaching/CSCI565-Spring14/Projects/Project1-LLVM/docs/Project1-LLVM.pdf
    errs () << "LoadInst";
    auto op_num = inst.getNumOperands ();
    errs () << ": " << op_num << " ops. ";
  }

  void visitStoreInst (const StoreInst &inst)
  {
    // store i32 %x, i32* %2, align 4
    errs () << "store inst";
    auto op_num = inst.getNumOperands ();
    errs () << ": " << op_num << " operands ";
    if (Argument *arg = dyn_cast <Argument> (inst.getOperand (0)))
      {
	StringRef name = arg->getName ();
	errs () << "arg0 ";
	errs () << name.str ();
      }
    if (dyn_cast <Argument> (inst.getOperand (1)))
      errs () << "arg1 ";
    errs () << "\n";
  }
};

/// Print function
bool FuncPrinter::runOnFunction (Function &F)
{
  errs () << "------------------------------\n";
  errs () << "func: ";
  errs ().write_escaped (F.getName ()) << "\n";

  // Visit instructions
  Interpreter interpreter;
  interpreter.visit (F);

  // ----------------------------------------
  // TODO: remove, this is just for checking the instruction visitors
  std::set <Instruction*> WorkList;
  for (inst_iterator i = inst_begin (F), e = inst_end (F); i != e; i++)
    WorkList.insert (&*i);

  // it is very strange, but perhaps this loop visits instructions in incorrect order o0 !?..
  while (!WorkList.empty ())
    {
      // todo: apply Instruction Visitors http://llvm.org/doxygen/InstVisitor_8h-source.html
      // or just get operands http://stackoverflow.com/questions/8651829/getting-the-operands-in-an-llvm-instruction
      Instruction *I = *WorkList.begin ();
      WorkList.erase (WorkList.begin ());
      errs ().write_escaped (I->getOpcodeName ()) << "\n";
    }
  // ----------------------------------------
    
  // No transformations.
  return false;
}
