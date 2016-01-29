# ifndef __LOCAL_MEMORY_HPP__
# define __LOCAL_MEMORY_HPP__

//TODO interruption handling (replace interruptions by exceptions)

// LLVM
# include "llvm/IR/Instruction.h"
# include "llvm/Support/raw_ostream.h"

// STL
# include <map>

// Project
# include "../solver/expr.hpp"
# include "../utils/interruption.hpp"

typedef const llvm::Value *ConstValPtr;

class LMemoryAccessFailure final : public Interruption {
public:
	LMemoryAccessFailure(ConstValPtr val) {
		val_ = val;
	}

	virtual ~LMemoryAccessFailure() {/*nothing to do*/}

	virtual void Print() {
		llvm::errs() << "\nLocal memory access failed on: " << *val_ << "\n";
	}

private:
	ConstValPtr val_ = NULL;
};

class LocalMemory {
public:
	void Alloca(ConstValPtr allocated);
	solver::SharedExpr Load(ConstValPtr address);
	void Store(ConstValPtr address, solver::SharedExpr value);
private:
	std::map<ConstValPtr, solver::SharedExpr> memory_;
};

# endif /* __LOCAL_MEMORY_HPP__ */
