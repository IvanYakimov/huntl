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

namespace interpreter {
	struct Solution {
	};
	using SolutionPtr = std::shared_ptr<Solution>;
	struct Scalar : public Solution {
	public:
		Scalar(memory::ConcretePtr scalar);
		memory::ConcretePtr scalar;
	};
	using ScalarPtr = std::shared_ptr<Scalar>;
	struct Array : public Solution {
		std::list<ScalarPtr> agregate;
	};
	using ArrayPtr = std::shared_ptr<Array>;
	using SolutionList = std::list<SolutionPtr>;

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
 		 memory::ConcretePtr ProduceScalar(memory::HolderPtr holder);
 		 bool JIT(std::vector<llvm::GenericValue> jit_args, llvm::GenericValue expected);
 		SolutionPtr HandleArg(llvm::Type* ty, memory::HolderPtr holder);
 		SolutionList ProduceArgSolutions(llvm::Function* func, memory::ArgMapPtr arg_map);
 		std::vector<llvm::GenericValue> ProduceJITArgs(SolutionList result_list);
};
}

#endif











