# include "func-printer.hpp"

/// Print function
bool FuncPrinter::runOnFunction (Function &F)
{
  errs () << "define ";
  errs () << "@" << F.getName () << "\n";

  // Visit instructions
  InstPrinter inst_printer (&errs);
  inst_printer.visit (F);
    
  // No transformations.
  return false;
}