# include "inst-printer.hpp"

void InstPrinter::visitReturnInst (const ReturnInst &inst)
{
  errs () << "ret";
  errs () << "\n";
}

void InstPrinter::visitBranchInst (const BranchInst &inst)
{
  errs () << "br";
  errs () << "\n";
}

void InstPrinter::visitICmpInst (const ICmpInst &inst)
{
  errs () << "icmp";
  errs () << "\n";
}

void InstPrinter::visitAllocaInst (const AllocaInst &inst)
{
  errs () << "alloca inst";
  auto op_num = inst.getNumOperands ();
  errs () << ": " << op_num << " ops";
  errs () << "\n";
}

void InstPrinter::visitLoadInst (const LoadInst &inst)
{
  // http://www.isi.edu/~pedro/Teaching/CSCI565-Spring14/Projects/Project1-LLVM/docs/Project1-LLVM.pdf
  errs () << "load";
  auto op_num = inst.getNumOperands ();
  errs () << ": " << op_num << " ops. ";
  errs () << "\n";
}


void InstPrinter::visitStoreInst (const StoreInst &inst)
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
