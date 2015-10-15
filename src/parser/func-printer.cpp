# include "func-printer.hpp"

# include "inst-printer.hpp"

/// Print function
bool FuncPrinter::runOnFunction (Function &F)
{
  errs () << "define ";
  errs () << "@" << F.getName () << "\n";

  // Visit instructions
  InstPrinter inst_printer;
  inst_printer.visit (F);

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
      // /*disabled */ errs ().write_escaped (I->getOpcodeName ()) << "\n";
    }
  // ----------------------------------------
    
  // No transformations.
  return false;
}
