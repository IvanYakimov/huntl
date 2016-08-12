#ifndef __TEST_GENERATOR_HPP__
#define __TEST_GENERATOR_HPP__

#include "llvm/IR/InstVisitor.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "holder.hpp"
#include "context.hpp"

#include <unistd.h>
#include <sys/wait.h>
#include <sys/types.h>

#include <functional>

#include <ostream>
#include <list>
#include <memory>

#include "solution.hpp"
#include "instanceof.hpp"

namespace interpreter {
	using memory::ArgMap; using memory::HolderPtr; using memory::ArgMapPtr;
 	 class TestGenerator {
 	 public:
 		 TestGenerator(llvm::Module* module, llvm::Function* target, memory::ArgMapPtr args,
 				 ContextRef context, std::ostream& file);
 		 ~TestGenerator();
 		 NONCOPYABLE(TestGenerator);
 		 void Do();
 	 private:
		ContextRef context_;
		std::ostream& file_;
		llvm::Function* target_;
		memory::ArgMapPtr args_;
		llvm::Module* module_;
		SolutionPtr ProduceInteger(HolderPtr holder);

		void PrintFunctionInfo(llvm::Function* func, std::ostream& file);
		void PrintSolution(SolutionPtr sol, std::ostream& file);
		void PrintTransition(std::ostream& file);
		void PrintSeparator(std::ostream& file);
		void PrintEndl(std::ostream& file);
		void PrintWholeSolution(llvm::Function* func, SolutionListPtr arg_sols, SolutionPtr ret_sol, std::ostream& file);
		SolutionPtr HandleArg(llvm::Type* ty, HolderPtr holder);
		SolutionListPtr ProduceArgSolutions(llvm::Function* func, ArgMapPtr arg_map);
		SolutionPtr ProduceRetSolution(llvm::Function* func, ArgMapPtr arg_map);
		std::vector<llvm::GenericValue> ProduceJITArgs(SolutionListPtr result_list);
		bool JIT(std::vector<llvm::GenericValue> jit_args, llvm::GenericValue expected);
};
}

#endif











