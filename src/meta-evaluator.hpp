#ifndef __META_EVALUATOR_HPP__
#define __META_EVALUATOR_HPP__

// STL
#include <exception>
#include <memory>

# include "llvm/IR/InstVisitor.h"
# include "llvm/IR/Instruction.h"
# include "llvm/Support/raw_ostream.h"
# include "llvm/Support/Debug.h"

#include "singleton.hpp"
#include "holder.hpp"
#include "creatable.hpp"
#include "solver.hpp"
#include "expr.hpp"
#include "local-memory.hpp"
#include "meta-int.hpp"
//#include "path-constraint.hpp"

namespace interpreter {
	class MetaEvaluator;
	using MetaEvaluatorPtr = std::shared_ptr<MetaEvaluator>;
	class MetaEvaluator {
	public:
		MetaEvaluator(memory::LocalMemoryPtr display, solver::SolverPtr solver = nullptr);
		~MetaEvaluator();
		void BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right);
		void Assign (const llvm::Value *destination, memory::HolderPtr target);
		static MetaEvaluatorPtr Create(memory::LocalMemoryPtr display, solver::SolverPtr solver = nullptr);
	private:
		memory::LocalMemoryPtr display_;
		solver::SolverPtr solver_;
		solver::SharedExpr Concrete_To_Symbolic(interpreter::MetaInt concrete_val);
		solver::Kind ExtractKindFromInst(const llvm::Instruction* inst);
		MetaInt PerformConcreteBinOp(const llvm::Instruction* inst, MetaInt left_val, MetaInt right_val);
	};
}

#endif













