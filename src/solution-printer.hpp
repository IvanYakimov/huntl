#ifndef __SOLUTION_PRINTER_HPP__
#define __SOLUTION_PRINTER_HPP__

#include "solution.hpp"
#include "instanceof.hpp"
#include "llvm/IR/Function.h"
#include <iostream>

namespace interpreter {
	void PrintFunctionInfo(llvm::Function* func, std::ostream& file);
	void PrintSolution(SolutionPtr sol, std::ostream& file);
	void PrintTransition(std::ostream& file);
	void PrintSeparator(std::ostream& file);
	void PrintEndl(std::ostream& file);
	void PrintWholeSolution(llvm::Function* func, SolutionListPtr arg_sols, SolutionPtr ret_sol, std::ostream& file);
}

#endif
