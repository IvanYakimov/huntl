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
  // register this instruction
  register_map_.Add (&inst);
  errs () << register_map_.GetName (&inst) << " = ";
  errs () << "alloca";
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
  errs () << "store ";
  auto op_num = inst.getNumOperands ();
  if (Argument *op0 = dyn_cast <Argument> (inst.getOperand (0)))
    {
      PrintArgOp (op0);
    }
  if (AllocaInst *op1 = dyn_cast <AllocaInst> (inst.getOperand (1)))
    {
      PrintAllocaOp (op1);
    }
  errs () << "\n";
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
      // this is a pointer
      errs () << "* ";
    }
  auto reg_name = register_map_.GetName (op);
  errs () << reg_name << " ";
  unsigned allign = op->getAlignment ();
  errs () << " align " << allign;
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
