# include "func-printer.hpp"


struct InstPrinter : public InstVisitor <InstPrinter>
{
  InstPrinter () {}

  // --------------------------------------------------
  // Specific Instruction type classes
  void visitReturnInst (const ReturnInst &inst)
  {
    errs () << "ret";
    errs () << "\n";
  }

  void visitBranchInst (const BranchInst &inst)
  {
    errs () << "br";
    errs () << "\n";
  }

  void visitICmpInst (const ICmpInst &inst)
  {
    errs () << "icmp";
    errs () << "\n";
  }
  
  void visitAllocaInst (const AllocaInst &inst)
  {
    errs () << "alloca inst";
    auto op_num = inst.getNumOperands ();
    errs () << ": " << op_num << " ops";
    errs () << "\n";
  }

  void visitLoadInst (const LoadInst &inst)
  {
    // http://www.isi.edu/~pedro/Teaching/CSCI565-Spring14/Projects/Project1-LLVM/docs/Project1-LLVM.pdf
    errs () << "load";
    auto op_num = inst.getNumOperands ();
    errs () << ": " << op_num << " ops. ";
    errs () << "\n";
  }

  void visitStoreInst (const StoreInst &inst)
  {
    // store i32 %x, i32* %2, align 4
    errs () << "store ";
    auto op_num = inst.getNumOperands ();
    if (Argument *op0 = dyn_cast <Argument> (inst.getOperand (0)))
      {
	// i32 %x
	Type *type = op0->getType ();
	if (type->isIntegerTy ())
	  {
	    unsigned width = type->getIntegerBitWidth ();
	    errs () << "i" << width << " ";
	  }
	StringRef name = op0->getName ();
	errs () << "%" << name.str () << ", ";
      }
    if (AllocaInst *op1 = dyn_cast <AllocaInst> (inst.getOperand (1)))
      {
	// i32* %2
	Type *type = op1->getAllocatedType ();
	if (type->isIntegerTy ())
	  {	    
	    unsigned width = type->getIntegerBitWidth ();
	    errs () << "i" << width;
	    // this is a pointer
	    errs () << "* ";
	  }
	
	unsigned allign = op1->getAlignment ();
	errs () << " align " << allign;
      }
    errs () << "\n";
  }
};

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
