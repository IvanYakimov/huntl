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


struct CountReturnVisitor : public InstVisitor <CountReturnVisitor>
{
  CountReturnVisitor () {}
  void visitReturnInst (ReturnInst &I)
  {
    errs () << "return instruction\n";
  }
};

/// Print function
bool FuncPrinter::runOnFunction (Function &F)
{
  errs () << "------------------------------\n";
  errs () << "func: ";
  errs ().write_escaped (F.getName ()) << "\n";

  // Initialize instruction list
  // TODO:
  // * replace std::set by (std::list or std::vector, or another similar container)
  // * replace raw pointer by smart pointer
  std::set <Instruction*> WorkList;
  for (inst_iterator i = inst_begin (F), e = inst_end (F); i != e; i++)
    WorkList.insert (&*i);

  while (!WorkList.empty ())
    {
      // todo: apply Instruction Visitors http://llvm.org/doxygen/InstVisitor_8h-source.html
      // or just get operands http://stackoverflow.com/questions/8651829/getting-the-operands-in-an-llvm-instruction
      Instruction *I = *WorkList.begin ();
      WorkList.erase (WorkList.begin ());
      errs ().write_escaped (I->getOpcodeName ()) << "\n";
    }

  // Visit return instructions
  CountReturnVisitor ret_visitor;
  ret_visitor.visit (F);
    
  // No transformations.
  return false;
}
