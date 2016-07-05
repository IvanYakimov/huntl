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
#include "context.hpp"
#include "concrete-eval.hpp"
#include "symbolic-eval.hpp"
//#include "path-constraint.hpp"

namespace interpreter {
	class MetaEvaluator;
	using MetaEvaluatorPtr = std::shared_ptr<MetaEvaluator>;
	class MetaEvaluator {
	public:
		MetaEvaluator(interpreter::ContextRef context);
		~MetaEvaluator();
		void BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right);
		void Assign (const llvm::Value *destination, memory::HolderPtr target);
		static MetaEvaluatorPtr Create(interpreter::ContextRef context);
	private:
		interpreter::ContextRef context_;
		ConcreteEval concrete_eval_;
		SymbolicEval symbolic_eval_;
		solver::SharedExpr Concrete_To_Symbolic(interpreter::MetaInt concrete_val);
		solver::Kind ExtractKindFromInst(const llvm::Instruction* inst);
	};
}

#endif













