# include "inst-printer.hpp"
using namespace llvm;

//

void InstPrinter::AddRegister (const llvm::Instruction *inst)
{
	register_map_.Add (inst);
}

// Handlers implementation

void InstPrinter::HandleStoreInst (const llvm::Instruction &inst, const llvm::Argument *arg, const llvm::AllocaInst *alloca)
{
	PrintArg (arg);
	Comma ();
	PrintAlloca (alloca);
	Endl ();
}

void InstPrinter::HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *const_int, const llvm::AllocaInst *alloca)
{
	PrintConstantInt (const_int);
	Comma ();
	PrintAlloca (alloca);
	Endl ();
}

void InstPrinter::HandleStoreInst (const llvm::Instruction &inst)
{
	//TODO: pattern matching fault handling
}

// Printing methods

void InstPrinter::Comma ()
{
	errs () << ", ";
}

void InstPrinter::Endl ()
{
	errs () << "\n";
}

void InstPrinter::PrintArg (const llvm::Argument *arg)
{
	errs () << "arg";
}

void InstPrinter::PrintAlloca (const llvm::AllocaInst *alloca)
{
	errs () << "alloca";
}

void InstPrinter::PrintConstantInt (const llvm::ConstantInt *constant)
{
	errs () << "const";
}

void InstPrinter::RegisterMap::Add(const llvm::Instruction *inst)
{
	internal_.insert (RegInfo (inst, ++reg_counter_));
}

std::string InstPrinter::RegisterMap::GetName (const llvm::Instruction *inst)
{
	auto reg_num = internal_[inst];
	std::string name;
	name += "%";
	name += std::to_string (reg_num);
	return name;
}









