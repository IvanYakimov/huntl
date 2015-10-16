# include "inst-printer.hpp"

void InstPrinter::visitReturnInst (const ReturnInst &inst)
{
  errs () << "ret ";
  PrintOpList (&inst);
  errs () << "\n";
}

void InstPrinter::visitBranchInst (const BranchInst &inst)
{
  errs () << "br ";
  errs () << "\n";
}

void InstPrinter::visitICmpInst (const ICmpInst &inst)
{
  errs () << "icmp ";
  errs () << "\n";
}

void InstPrinter::visitAllocaInst (const AllocaInst &inst)
{
  register_map_.Add (&inst);
  PrintPrefix (&inst);
  errs () << "alloca ";
  PrintOpList (&inst);
  errs () << "\n";

}

void InstPrinter::visitLoadInst (const LoadInst &inst)
{
  register_map_.Add (&inst);
  PrintPrefix (&inst);
  errs () << "load ";
  PrintOpList (&inst);
  errs () << "\n";
}


void InstPrinter::visitStoreInst (const StoreInst &inst)
{
  errs () << "store ";
  PrintOpList (&inst);
  errs () << "\n";
}

void InstPrinter::PrintOpList (const Instruction *inst)
{
  auto op_num = inst->getNumOperands ();
  for (unsigned i = 0; i < op_num; i++)
    {
      Value *op = inst->getOperand (i);
      if (Argument *arg = dyn_cast <Argument> (op))
	PrintArgOp (arg);
      else if (AllocaInst *alloca = dyn_cast <AllocaInst> (op))
	PrintAllocaOp (alloca);
      else if (BinaryOperator *bin_op = dyn_cast <BinaryOperator> (op))
	PrintBinaryOperatorOp (bin_op);
      else
	{
	  Type *op_type = op->getType ();
	  errs () << " #T# ";
	  op_type->print (errs ());
	}
    }
}

void InstPrinter::PrintPrefix (const Instruction *inst)
{
  errs () << register_map_.GetName (inst) << " = ";
}

// TODO: check symbol table usage
void InstPrinter::PrintArgOp (const Argument *arg)
{
  Type *type = arg->getType ();
  if (type->isIntegerTy ())
    {
      unsigned width = type->getIntegerBitWidth ();
      errs () << "i" << width << " ";
    }
  StringRef name = arg->getName ();
  errs () << "%" << name.str () << ", ";
}

// TODO: virtual register name
// TODO: check "pointer problem"
void InstPrinter::PrintAllocaOp (const AllocaInst *op)
{
  Type *type = op->getAllocatedType ();
  if (type->isIntegerTy ())
    {	    
      unsigned width = type->getIntegerBitWidth ();
      errs () << "i" << width;
      // TODO: looks like junk code (this represents pointer)
      errs () << " #*# ";
    }
  auto reg_name = register_map_.GetName (op);
  errs () << reg_name << ", ";
  unsigned allign = op->getAlignment ();
  errs () << " align " << allign;
}

void InstPrinter::PrintBinaryOperatorOp (const BinaryOperator *bin_op)
{
  Type *type = bin_op->getType ();
  if (type->isIntegerTy ())
    {
      unsigned width = type->getIntegerBitWidth ();
      errs () << "i" << width;
      errs () << " #value# ";
    }
}

void InstPrinter::RegisterMap::Add (const llvm::Instruction *inst)
{
  map_.insert (std::pair <const Instruction*, RegisterNumber>
			(inst, ++counter_));
}

InstPrinter::RegisterMap::RegisterNumber InstPrinter::RegisterMap::GetNumber (const llvm::Instruction *inst)
{
  //todo: dummy
  return map_[inst];
}

std::string InstPrinter::RegisterMap::GetName (const llvm::Instruction *inst)
{
  auto reg_num = map_[inst];
  std::string name;
  name += "%";
  name += std::to_string (reg_num);
  return name;
}
