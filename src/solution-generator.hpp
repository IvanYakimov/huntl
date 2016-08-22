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
		SolutionGenerator(ContextRef context, llvm::Function* func, std::list<memory::HolderPtr>& arg_holders, memory::HolderPtr& ret_holder);
		~SolutionGenerator();
		bool ProduceSolution();
		SolutionListPtr GetArgSolutions();
		SolutionPtr GetRetSolution();
	private:
		SolutionListPtr ProduceArgSolutions();
		SolutionPtr ProduceRetSolution();
		IntegerPtr ProduceInteger(memory::HolderPtr holder);
		PointerPtr ProducePointerTo(memory::HolderPtr holder);
		ArrayPtr ProduceArrayOf(const llvm::ArrayType* array_type, memory::RamAddress base_address);
		SolutionPtr HandleArg(const llvm::Type* ty, memory::HolderPtr holder);
		ContextRef context_;
		llvm::Function* func_;
		// change to std::shared_ptr<std::list<memory::HolderPtr>>
		std::list<memory::HolderPtr>& arg_holders_;
		memory::HolderPtr& ret_holder_;
		SolutionListPtr arg_sols_;
		SolutionPtr ret_sol_;
	};
}

#endif
