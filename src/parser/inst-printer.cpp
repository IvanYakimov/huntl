# include "inst-printer.hpp"
using namespace llvm;



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
