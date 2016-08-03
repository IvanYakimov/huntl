#ifndef __META_EVALUATOR_HPP__
#define __META_EVALUATOR_HPP__

// STL
#include <exception>
#include <memory>
#include <functional>

# include "llvm/IR/Instructions.h"
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
#include "meta-kind.hpp"
#include "ram-delc.hpp"

namespace interpreter {
	class MetaEvaluator {
	public:
		MetaEvaluator(interpreter::ContextRef context);
		~MetaEvaluator();
		NONCOPYABLE(MetaEvaluator);
		void BinOp (memory::RamAddress lhs, unsigned op_code, memory::HolderPtr left, memory::HolderPtr right);
		void IntComparison (memory::RamAddress lhs, llvm::ICmpInst::Predicate predicate, memory::HolderPtr left, memory::HolderPtr right);
		const llvm::BasicBlock* Branch (memory::HolderPtr condition, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
		void Assign (memory::RamAddress lhs, memory::HolderPtr rhs_holder);
		void Conversion (memory::RamAddress lhs, memory::HolderPtr rhs, utils::MetaKind kind, unsigned new_width);
	private:
		ContextRef context_;
		ConcreteEval concrete_eval_;
		SymbolicEval symbolic_eval_;
		// Helpers
		solver::SharedExpr Symbolize(interpreter::MetaIntRef concrete_val);
		template<typename Op>
		using ConcreteFunc2 = std::function<void(memory::RamAddress,Op,MetaIntRef,MetaIntRef)>;
		template<typename Op>
		using SymbolicFunc2 = std::function<void(memory::RamAddress,Op,solver::SharedExpr,solver::SharedExpr)>;
		template<typename Op>
		void MixedEval2(memory::RamAddress lhs, Op code, memory::HolderPtr left, memory::HolderPtr right, ConcreteFunc2<Op> F, SymbolicFunc2<Op> G);
	};
}

#endif













