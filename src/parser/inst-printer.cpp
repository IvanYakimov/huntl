# include "inst-printer.hpp"
using namespace llvm;

// Handlers implementation

void InstPrinter::HandleStoreInst (const llvm::Argument *arg, const llvm::AllocaInst *alloca)
{
	PrintArg (arg);
	Comma ();
	PrintAlloca (alloca);
	Endl ();
}

void InstPrinter::HandleStoreInst (const llvm::ConstantInt *const_int, const llvm::AllocaInst *alloca)
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

// Register map implementation

void InstPrinter::RegisterMap::Add (const Instruction *inst)
{
	internal_map_.insert (std::pair <const llvm::Instruction*, RegNum> (inst, ++counter_));
}

InstPrinter::RegisterMap::RegNum InstPrinter::RegisterMap::GetNumber (const Instruction *inst)
{
	return internal_map_ [inst];
}

std::string InstPrinter::RegisterMap::GetName (const Instruction *inst)
{
	auto reg_num = internal_map_ [inst];
	std::string name;
	name += "%";
	name += std::to_string (reg_num);
	return name;
}
