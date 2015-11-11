# ifndef __INST_PRINTER_HPP__
# define __INST_PRINTER_HPP__

/*
author: Ivan Yakimov
date: 2015
e-mail: ivan.yakimov.research@yandex.ru
Licensed under LGPL license.
*/

// Standard Library
# include <map>
# include <utility>
# include <string>
# include <memory>
# include <functional>

// LLVM
# include "llvm/IR/Instruction.h"

// Internal
# include "pattern-matcher.hpp"

typedef std::function <llvm::raw_ostream&()> Printer;

// TODO: check - maybe remove final from methods
class InstPrinter final : public PatternMatcher
{
public:
	InstPrinter () {printer_ = &llvm::errs;}
	InstPrinter (Printer printer) {printer_ = printer;}

	~InstPrinter () {}

private:
	Printer printer_;

	virtual void AddRegister (const llvm::Instruction *inst);
	// Handlers
	virtual void HandleAllocaInst (const llvm::Instruction &inst, const llvm::Constant *const_val);
	virtual void HandleAllocaInst (const llvm::Instruction &inst);

	virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Argument *arg, const llvm::AllocaInst *alloca);
	virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *const_int, const llvm::AllocaInst *alloca);
	virtual void HandleStoreInst (const llvm::Instruction &inst);
	//
	virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::ConstantInt *const_int);
	virtual void HandleReturnInst (const llvm::Instruction &inst);

	// Helper methods
	std::string Separated (const std::string &separator, const std::string &endl, std::string current);
	template <typename... Targs>
	std::string Separated (const std::string &separator, const std::string &endl, std::string current, Targs... Operands);

	template <typename... Targs>
	std::string InstLine (std::string name, Targs... Operands);

	// Printing methods
	std::string ArgStr (const llvm::Argument *arg);
	std::string AllocaStr (const llvm::AllocaInst *alloca);
	std::string ConstantIntStr (const llvm::ConstantInt *constant);

	std::string TypeStr (const llvm::Type *type);
	std::string ArgNameStr (const llvm::Argument *arg);
	std::string AllignStr (const llvm::AllocaInst *alloca);
	std::string PrefixStr (const llvm::Instruction *inst);

	std::string ProduceOperand (std::string prefix, std::string postfix);

	class RegisterMap
	{
	public:
		void Add (const llvm::Instruction *inst);
		std::string GetName (const llvm::Instruction *inst);
	private:
		typedef unsigned RegNum;
		typedef std::pair <const llvm::Instruction*, RegNum> RegInfo;
		typedef std::map <const llvm::Instruction*, RegNum> RegMap;
		RegNum reg_counter_ = 0;
		RegMap internal_;
	} register_map_;
};

# endif /* __INST_PRINTER_HPP__ */
