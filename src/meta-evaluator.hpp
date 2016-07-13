#ifndef __META_EVALUATOR_HPP__
#define __META_EVALUATOR_HPP__

// STL
#include <exception>
#include <memory>
#include <functional>

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

namespace interpreter {
	class MetaEvaluator {
	public:
		MetaEvaluator(interpreter::ContextRef context);
		~MetaEvaluator();
		NONCOPYABLE(MetaEvaluator);
		void BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right);
		void ICmpInst (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right);
		void Assign (const llvm::Value *destination, memory::HolderPtr target);
	private:
		ContextRef context_;
		ConcreteEval concrete_eval_;
		SymbolicEval symbolic_eval_;
		solver::SharedExpr Symbolize(interpreter::MetaIntRef concrete_val);
		using ConcreteFunc2 = std::function<void(const llvm::Instruction*,MetaIntRef,MetaIntRef)>;
		using SymbolicFunc2 = std::function<void(const llvm::Instruction*,solver::SharedExpr,solver::SharedExpr)>;
		void MixedEval2(const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right,
				ConcreteFunc2 F, SymbolicFunc2 G);
	};
}

#endif













