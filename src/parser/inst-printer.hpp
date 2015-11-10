# ifndef __INST_PRINTER_HPP__
# define __INST_PRINTER_HPP__

/*
author: Ivan Yakimov
date: 2015
e-mail: ivan.yakimov.research@yandex.ru
Licensed under LGPL license.
*/

# include <map>
# include <utility>
# include <string>
# include <memory>

# include "llvm/IR/Instruction.h"

# include "pattern-matcher.hpp"

// TODO: check - maybe remove final from methods
class InstPrinter final : public PatternMatcher
{
public:
	InstPrinter () {}
	~InstPrinter () {}

private:
	virtual void AddRegister (const llvm::Instruction *inst);
	// Handlers
	virtual void HandleStoreInst (const llvm::Argument *arg, const llvm::AllocaInst *alloca);
	virtual void HandleStoreInst (const llvm::ConstantInt *const_int, const llvm::AllocaInst *alloca);
	virtual void HandleStoreInst (const llvm::Instruction &inst);

	// Printing methods
	void PrintArg (const llvm::Argument *arg);
	void PrintAlloca (const llvm::AllocaInst *alloca);
	void PrintConstantInt (const llvm::ConstantInt *constant);
	void Comma ();
	void Endl ();

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
