#ifndef __STATE_HPP__
#define __STATE_HPP__

# include "llvm/IR/Function.h"

namespace interpreter {
	/* Declarations */
	enum class StepStatus;
	class PathConstraint;
	class ProgramCounter;

	enum class StepStauts {
		NONFORKING = 0,
		FORKING
	};

	class PathConstraint {

	};

	class ProgramCounter {

	};

	class State {
	private:
		PathConstraint path_constraint_;
		ProgramCounter program_counter_;
		llvm::Function &func_;

	public:
		StepStatus Step();
	};
}

#endif /* __STATE_HPP__ */
