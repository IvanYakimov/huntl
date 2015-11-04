# include "func-printer.hpp"

#include "pattern-matcher.hpp"

/// Print function
bool FuncPrinter::runOnFunction (Function &F)
{
  errs () << "define ";
  errs () << "@" << F.getName () << "\n";

  // Visit instructions
  PatternMatcher inst_printer;
  inst_printer.visit (F);
    
  // No transformations.
  return false;
}
