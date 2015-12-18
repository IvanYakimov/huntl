# ifndef __LOCAL_MEMORY_HPP__
# define __LOCAL_MEMORY_HPP__

// STL
# include <map>

// Project
# include "../solver/expr.hpp"
# include "llvm/IR/Instruction.h"

typedef const llvm::Instruction *ConstInstPtr;

class LocalMemory {
public:
	void Alloca();
	solver::SharedExprPtr Load(ConstInstPtr address);
	void Store(ConstInstPtr address, solver::SharedExprPtr value);
private:
	std::map<ConstInstPtr, solver::SharedExprPtr> memory_;
};

# endif /* __LOCAL_MEMORY_HPP__ */
