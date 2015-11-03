# include "inst-printer.hpp"

bool InstPrinter::Case (const Instruction &inst, unsigned i)
{
  return true;
}

template <typename T, typename... Targs>
bool InstPrinter::Case (const Instruction &inst, unsigned i, T value, Targs... Fargs)
{
  // (some cryptic code) if the case matches the value
  if (isa <typename std::remove_pointer<T>::type> (inst.getOperand (i))) {
    return true && Case (inst, ++i, Fargs...);
  }
  return false;
}

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
  //PrintOpList (&inst);
  Argument *arg = NULL;
  AllocaInst *alloca = NULL;
  errs () << " arg alloca ";
  if (Case (inst, 0, arg, alloca))
    errs () << "matched";
  else
    errs () << "didn't match";
  errs () << ";\t";
  errs () << "arg arg ";
  if (Case (inst, 0, arg, arg))
    errs () << "matched";
  else
    errs () << "didn't match";
  errs () << "\n";
}

void InstPrinter::visitBinaryOperator (const BinaryOperator &inst)
{
  register_map_.Add (&inst);
  PrintPrefix (&inst);
  errs () << "#binop# ";
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
      else if (LoadInst *load = dyn_cast <LoadInst> (op))
	PrintLoadOp (load);
      else if (BinaryOperator *bin_op = dyn_cast <BinaryOperator> (op))
	PrintBinaryOperatorOp (bin_op);
      else if (ConstantInt *constant = dyn_cast <ConstantInt> (op))
	PrintConstantIntOp (constant);
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
      // TODO: looks like buggish junk code (this represents pointer)
      errs () << "* ";
    }
  auto reg_name = register_map_.GetName (op);
  errs () << reg_name << ", ";
  unsigned allign = op->getAlignment ();
  errs () << " align " << allign;
}

void InstPrinter::PrintLoadOp (const LoadInst *op)
{
  Type *type = op->getType ();
  if (type->isIntegerTy ())
    {
      unsigned width = type->getIntegerBitWidth ();
      errs () << "i" << width;
      // TODO: looks like buggish junk code (this represents pointer)
      errs () << "'*' ";
    }
  auto reg_name = register_map_.GetName (op);
  errs () << reg_name << " ";
  //errs () << reg_name << ", ";
  //unsigned allign = op->getAlignment ();
  //errs () << " align " << allign;
}

void InstPrinter::PrintBinaryOperatorOp (const BinaryOperator *bin_op)
{
  Type *type = bin_op->getType ();
  if (type->isIntegerTy ())
    {
      unsigned width = type->getIntegerBitWidth ();
      errs () << "i" << width;
      errs () << " " << register_map_.GetName (bin_op);
    }
}

void InstPrinter::PrintConstantIntOp (const ConstantInt *constant)
{
  Type *type = constant->getType ();

  unsigned width = type->getIntegerBitWidth ();
  errs () << "i" << width;
  auto const_int_val = constant->getSExtValue ();
  errs () << " ";
  errs () << const_int_val;  
}

void InstPrinter::RegisterMap::Add (const llvm::Instruction *inst)
{
  map_.insert (std::pair <const Instruction*, RegisterNumber>
			(inst, ++counter_));
}

InstPrinter::RegisterMap::RegisterNumber InstPrinter::RegisterMap::GetNumber (const llvm::Instruction *inst)
{
  //TODO: dummy
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
