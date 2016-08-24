#ifndef __SOLUTION_PRINTER_HPP__
#define __SOLUTION_PRINTER_HPP__

#include "holder.hpp"
#include "holder-helper.hpp"
#include "solution.hpp"
#include "instanceof.hpp"
#include "llvm/IR/Function.h"
#include "context.hpp"
#include <iostream>

namespace interpreter {
	class SolutionPrinter {
	public:
		SolutionPrinter(ContextRef context, llvm::Function* func, SolutionListPtr arg_sols, SolutionPtr ret_sol);
		~SolutionPrinter();
		void operator()(std::ostream& file);
	private:
		void PrintFunctionInfo(llvm::Function* func, std::ostream& file);
		void PrintSolution(SolutionPtr sol, std::ostream& file);
		void PrintASCII(MetaIntRef symbol, std::ostream& os);
		void PrintTransition(std::ostream& file);
		void PrintSeparator(std::ostream& file);
		void PrintEndl(std::ostream& file);

		ContextRef context_;
		llvm::Function* func_;
		SolutionListPtr arg_sols_;
		SolutionPtr ret_sol_;
	};
}

#endif
