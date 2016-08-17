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
		IntegerPtr ProduceInteger(memory::HolderPtr holder);
		PointerPtr ProducePointerTo(memory::HolderPtr holder);
		ArrayPtr ProduceArrayOf(const llvm::ArrayType* array_type, memory::RamAddress base_address);
		SolutionPtr HandleArg(const llvm::Type* ty, memory::HolderPtr holder);
		ContextRef context_;
	};
}

#endif
