# include "inst-printer.hpp"
using namespace llvm;
using std::string;
//

void InstPrinter::AddRegister (const llvm::Instruction *inst)
{
	register_map_.Add(inst);
}

// Handlers implementation

void InstPrinter::HandleStoreInst (const llvm::Instruction &inst, const llvm::Argument *arg, const llvm::AllocaInst *alloca)
{
	string arg_str = ArgStr(arg),
			alloca_str = AllocaStr(alloca);
	printer_() << InstLine("store", arg_str, alloca_str);
}

void InstPrinter::HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *const_int, const llvm::AllocaInst *alloca)
{
	string const_str = ConstantIntStr(const_int),
			alloca_str = AllocaStr(alloca);
	printer_() << InstLine("store", const_str, alloca_str);
}

void InstPrinter::HandleStoreInst (const llvm::Instruction &inst)
{
	//TODO: pattern matching fault handling
}

// Printing methods

std::string InstPrinter::InstPrinter::ArgStr (const llvm::Argument *arg)
{
	string type_str = TypeStr(arg->getType());
	string name_str = NameStr (arg);
	return ProduceOperand(type_str, name_str);
}

std::string InstPrinter::AllocaStr (const llvm::AllocaInst *alloca)
{
	string type_str = TypeStr(alloca->getAllocatedType());
	string reg_name = register_map_.GetName(alloca);
	return ProduceOperand(type_str, reg_name) + AllignStr(alloca);
}

std::string InstPrinter::ConstantIntStr (const llvm::ConstantInt *constant)
{
	string type_str = TypeStr(constant->getType());
	auto val = constant->getSExtValue();
	string val_str = std::to_string(val);
	return ProduceOperand(type_str, val_str);
}

//-------------------------------------
// Helper functions
std::string InstPrinter::Separated (const std::string &separator, const std::string &endl, std::string current)
{
	return current + endl;
}

template <typename... Targs>
std::string InstPrinter::Separated (const std::string &separator, const std::string &endl, std::string current, Targs... Operands)
{
	return current + separator + Separated (separator, endl, Operands...);
}

template <typename... Targs>
std::string InstPrinter::InstLine (std::string name, Targs... Operands)
{
	//TODO: prefix
	return name + " " + Separated (", ", "\n", Operands...);
}

std::string InstPrinter::TypeStr (const llvm::Type *type)
{
	string type_str;
	if (type->isIntegerTy()) {
		type_str += "i";
		auto width = type->getIntegerBitWidth();
		type_str += std::to_string(width);
	}
	else {
		//TODO: dummy:
		type_str += "#";
	}
	return type_str;
}

std::string InstPrinter::NameStr (const llvm::Argument *arg)
{
	StringRef name_ref = arg->getName();
	return "%" + name_ref.str();
}

std::string InstPrinter::AllignStr (const llvm::AllocaInst *alloca)
{
	auto allign = alloca->getAlignment();
	return ", allign " + std::to_string (allign);
}

std::string InstPrinter::ProduceOperand (std::string prefix, std::string postfix)
{
	return prefix + " " + postfix;
}

//-------------------------------------
// Register map

void InstPrinter::RegisterMap::Add(const llvm::Instruction *inst)
{
	//TODO: isn't it a memory leak?
	internal_.insert(RegInfo(inst, ++reg_counter_));
}

std::string InstPrinter::RegisterMap::GetName (const llvm::Instruction *inst)
{
	auto reg_num = internal_[inst];
	std::string name;
	name += "%";
	name += std::to_string(reg_num);
	return name;
}
