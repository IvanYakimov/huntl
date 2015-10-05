// based on http://llvm.org/docs/WritingAnLLVMPass.html tutorial

# include "llvm/Pass.h"
# include "llvm/IR/Function.h"
# include "llvm/IR/Instruction.h"
# include "llvm/IR/InstIterator.h"
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

/// Print function
bool FuncPrinter::runOnFunction (Function &F)
{
  errs () << "------------------------------\n";
  errs () << "func: ";
  errs ().write_escaped (F.getName ()) << "\n";

  // Init instruction list
  std::set <Instruction*> WorkList;
  for (inst_iterator i = inst_begin (F), e = inst_end (F); i != e; i++)
    WorkList.insert (&*i);

  while (!WorkList.empty ())
    {
      // todo: apply Instruction Visitors http://llvm.org/doxygen/InstVisitor_8h-source.html
      Instruction *I = *WorkList.begin ();
      WorkList.erase (WorkList.begin ());
      errs ().write_escaped (I->getOpcodeName ()) << "\n";
    }

  // No transformations.
  return false;
}
