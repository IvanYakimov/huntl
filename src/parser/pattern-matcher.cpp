#include "pattern-matcher.hpp"

bool PatternMatcher::Case (const Instruction &inst, unsigned i)
{
	if (inst.getNumOperands () != i)
		return false;
	else
		return true;
}

template <typename T, typename... Targs>
bool PatternMatcher::Case (const Instruction &inst, unsigned i, T value, Targs... Fargs)
{
	typedef typename std::remove_pointer <T>::type pV;
	typedef typename std::remove_pointer <pV>::type V;
	auto operand = inst.getOperand (i);
	if (isa <V> (operand)) {
		*value = dyn_cast <V> (operand);
		return true && Case (inst, ++i, Fargs...);
	}
	else
		return false;
}

void PatternMatcher::visitReturnInst (const ReturnInst &inst)
{
  errs () << "ret ";
  PrintOpList (&inst);
  errs () << "\n";
}

void PatternMatcher::visitBranchInst (const BranchInst &inst)
{
  errs () << "br ";
  errs () << "\n";
}

void PatternMatcher::visitICmpInst (const ICmpInst &inst)
{
  errs () << "icmp ";
  errs () << "\n";
}

void PatternMatcher::visitAllocaInst (const AllocaInst &inst)
{
  register_map_.Add (&inst);
  PrintPrefix (&inst);
  errs () << "alloca ";
  PrintOpList (&inst);
  errs () << "\n";

}

void PatternMatcher::visitLoadInst (const LoadInst &inst)
{
  register_map_.Add (&inst);
  PrintPrefix (&inst);
  errs () << "load ";
  PrintOpList (&inst);
  errs () << "\n";
}

void PatternMatcher::visitStoreInst (const StoreInst &inst)
{
  errs () << "store ";
  ConstantInt *const_int = NULL;
  Argument *arg = NULL;
  AllocaInst *alloca = NULL;
  if (Case (inst, 0, &const_int, &alloca)) {
	  PrintConstantInt (const_int);
	  PrintAlloca (alloca);
	  errs () << "\t#const_int alloca#";
  }
  else if (Case (inst, 0, &arg, &alloca)) {
	  PrintArg (arg);
	  PrintAlloca (alloca);
	  errs () << "\t#arg alloca#";

  }
  errs () << "\n";
}

void PatternMatcher::visitBinaryOperator (const BinaryOperator &inst)
{
  register_map_.Add (&inst);
  PrintPrefix (&inst);
  errs () << "#binop# ";
  PrintOpList (&inst);
  errs () << "\n";
}

void PatternMatcher::PrintOpList (const Instruction *inst)
{
  auto op_num = inst->getNumOperands ();
  for (unsigned i = 0; i < op_num; i++)
    {
      Value *op = inst->getOperand (i);
      if (Argument *arg = dyn_cast <Argument> (op))
		PrintArg (arg);
		  else if (AllocaInst *alloca = dyn_cast <AllocaInst> (op))
		PrintAlloca (alloca);
		  else if (LoadInst *load = dyn_cast <LoadInst> (op))
		PrintLoad (load);
		  else if (BinaryOperator *bin_op = dyn_cast <BinaryOperator> (op))
		PrintBinaryOperator (bin_op);
		  else if (ConstantInt *constant = dyn_cast <ConstantInt> (op))
		PrintConstantInt (constant);
		  else
		{
		  Type *op_type = op->getType ();
		  errs () << " #T# ";
		  op_type->print (errs ());
		}
    }
}

void PatternMatcher::PrintPrefix (const Instruction *inst)
{
  errs () << register_map_.GetName (inst) << " = ";
}

// TODO: check symbol table usage
void PatternMatcher::PrintArg (const Argument *arg)
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
void PatternMatcher::PrintAlloca (const AllocaInst *op)
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

void PatternMatcher::PrintLoad (const LoadInst *op)
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

void PatternMatcher::PrintBinaryOperator (const BinaryOperator *bin_op)
{
  Type *type = bin_op->getType ();
  if (type->isIntegerTy ())
    {
      unsigned width = type->getIntegerBitWidth ();
      errs () << "i" << width;
      errs () << " " << register_map_.GetName (bin_op);
    }
}

void PatternMatcher::PrintConstantInt (const ConstantInt *constant)
{
  Type *type = constant->getType ();

  unsigned width = type->getIntegerBitWidth ();
  errs () << "i" << width << " ";
  auto const_int_val = constant->getSExtValue ();
  errs () << const_int_val;
  errs () << ", ";
}

void PatternMatcher::RegisterMap::Add (const llvm::Instruction *inst)
{
  map_.insert (std::pair <const Instruction*, RegisterNumber>
			(inst, ++counter_));
}

PatternMatcher::RegisterMap::RegisterNumber PatternMatcher::RegisterMap::GetNumber (const llvm::Instruction *inst)
{
  //TODO: dummy
  return map_[inst];
}

std::string PatternMatcher::RegisterMap::GetName (const llvm::Instruction *inst)
{
  auto reg_num = map_[inst];
  std::string name;
  name += "%";
  name += std::to_string (reg_num);
  return name;
}
