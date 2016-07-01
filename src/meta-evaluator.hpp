#ifndef __META_EVALUATOR_HPP__
#define __META_EVALUATOR_HPP__

// STL
#include <exception>
#include <memory>

# include "llvm/IR/InstVisitor.h"
# include "llvm/IR/Instruction.h"
# include "llvm/Support/raw_ostream.h"
# include "llvm/Support/Debug.h"

#include "display.hpp"
#include "singleton.hpp"
#include "holder.hpp"
#include "creatable.hpp"
#include "solver.hpp"
#include "expr.hpp"
#include "meta-int.hpp"
//#include "path-constraint.hpp"

namespace interpreter {
	class MetaEvaluator;
	using MetaEvaluatorPtr = std::shared_ptr<MetaEvaluator>;
	class MetaEvaluator {
	public:
		MetaEvaluator(memory::DisplayPtr display, solver::SolverPtr solver = nullptr);
		~MetaEvaluator();
		void BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right);
		void Assign (const llvm::Value *destination, memory::HolderPtr target);
		static MetaEvaluatorPtr Create(memory::DisplayPtr display, solver::SolverPtr solver = nullptr);
	private:
		memory::DisplayPtr display_;
		solver::SolverPtr solver_;
	};
}

#endif













