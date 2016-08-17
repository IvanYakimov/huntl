#ifndef __TEST_GENERATOR_HPP__
#define __TEST_GENERATOR_HPP__

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
#include "solution-printer.hpp"
#include "jit-verifier.hpp"

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
		JITVerifier jit_verifier_;
		SolutionPtr ProduceInteger(HolderPtr holder);
		SolutionPtr HandleArg(const llvm::Type* ty, HolderPtr holder);
		SolutionListPtr ProduceArgSolutions(llvm::Function* func, ArgMapPtr arg_map);
		SolutionPtr ProduceRetSolution(llvm::Function* func, ArgMapPtr arg_map);
};
}

#endif











