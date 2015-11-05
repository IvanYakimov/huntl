# ifndef __INST_PRINTER_HPP__
# define __INST_PRINTER_HPP__

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
