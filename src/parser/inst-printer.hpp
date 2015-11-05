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

class InstPrinter : public PatternMatcher
{
public:
	InstPrinter () {
		register_map_ = std::unique_ptr <IRegisterMap> (new RegisterMap ());
	}

	~InstPrinter () {
		//TODO:
	}

private:
	// Handlers
	virtual void HandleStoreInst (const llvm::Argument *arg, const llvm::AllocaInst *alloca) final;
	virtual void HandleStoreInst (const llvm::ConstantInt *const_int, const llvm::AllocaInst *alloca) final;
	virtual void HandleStoreInst (const llvm::Instruction &inst) final;

	// Printing methods
	void PrintArg (const llvm::Argument *arg);
	void PrintAlloca (const llvm::AllocaInst *alloca);
	void PrintConstantInt (const llvm::ConstantInt *constant);
	void Comma ();
	void Endl ();

private:
	class RegisterMap : public IRegisterMap
	{
	public:
		typedef unsigned RegNum;
		void Add (const llvm::Instruction *inst);
		RegNum GetNumber (const llvm::Instruction *inst);
		std::string GetName (const llvm::Instruction *inst);
	private:
		std::map <const llvm::Instruction *, RegNum> internal_map_;
		RegNum counter_ = 0;
	};
};

# endif /* __INST_PRINTER_HPP__ */
