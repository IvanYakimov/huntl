#ifndef __SOLUTION_GENERATOR_HPP__
#define __SOLUTION_GENERATOR_HPP__

#include "holder.hpp"
#include "context.hpp"
#include "solution.hpp"
#include "activation.hpp"

#include "llvm/IR/Type.h"
#include "llvm/IR/Function.h"

#include <list>

namespace interpreter {
	class SolutionGenerator {
	public:
		SolutionGenerator(ContextRef context);
		~SolutionGenerator();
		SolutionListPtr ProduceArgSolutions(llvm::Function* func, std::list<memory::HolderPtr>& arg_map);
		SolutionPtr ProduceRetSolution(llvm::Function* func, memory::HolderPtr arg_map);
	private:
		SolutionPtr ProduceInteger(memory::HolderPtr holder);
		SolutionPtr ProducePointerTo(memory::HolderPtr holder);
		SolutionPtr HandleArg(const llvm::Type* ty, memory::HolderPtr holder);
		ContextRef context_;
	};
}

#endif
