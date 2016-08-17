#ifndef __SOLUTION_GENERATOR_HPP__
#define __SOLUTION_GENERATOR_HPP__

#include "holder.hpp"
#include "context.hpp"
#include "solution.hpp"
#include "activation.hpp"

#include "llvm/IR/Type.h"
#include "llvm/IR/Function.h"

namespace interpreter {
	class SolutionGenerator {
	public:
		SolutionGenerator(ContextRef context);
		~SolutionGenerator();
		SolutionPtr ProduceInteger(memory::HolderPtr holder);
		SolutionPtr HandleArg(const llvm::Type* ty, memory::HolderPtr holder);
		SolutionListPtr ProduceArgSolutions(llvm::Function* func, memory::ArgMapPtr arg_map);
		SolutionPtr ProduceRetSolution(llvm::Function* func, memory::ArgMapPtr arg_map);
	private:
		ContextRef context_;
	};
}

#endif
