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

namespace interpreter {
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
 		 memory::ConcretePtr HandleInteger(llvm::IntegerType* ty, memory::HolderPtr value);
 		 std::list<memory::ConcretePtr> HandlePointer(llvm::PointerType* ty, memory::HolderPtr ptr);
 		 memory::ConcretePtr HandleScalar(memory::HolderPtr holder);
 		 bool JIT(std::list<memory::ConcretePtr> arg_sol_list, memory::ConcretePtr ret_sol);
};
}

#endif











