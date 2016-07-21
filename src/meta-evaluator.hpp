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

namespace interpreter {
	class MetaEvaluator {
	public:
		MetaEvaluator(interpreter::ContextRef context);
		~MetaEvaluator();
		NONCOPYABLE(MetaEvaluator);
		void BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right);
		void IntComparison (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right);
		const llvm::BasicBlock* Branch (const llvm::Instruction *inst, memory::HolderPtr condition, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
		void Assign (const llvm::Value *lhs, memory::HolderPtr rhs_holder);
		void Dereferencing (const llvm::Value* lhs, memory::HolderPtr ptr_holder);
		void Addressing (const llvm::Value* lhs, memory::HolderPtr addr_holder);
		void Conversion (const llvm::Instruction* lhs, memory::HolderPtr rhs, utils::MetaKind kind, unsigned width);
	private:
		ContextRef context_;
		ConcreteEval concrete_eval_;
		SymbolicEval symbolic_eval_;
		solver::SharedExpr Symbolize(interpreter::MetaIntRef concrete_val);
		using ConcreteFunc2 = std::function<void(const llvm::Instruction*,MetaIntRef,MetaIntRef)>;
		using SymbolicFunc2 = std::function<void(const llvm::Instruction*,solver::SharedExpr,solver::SharedExpr)>;
		void MixedEval2(const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right,
				ConcreteFunc2 F, SymbolicFunc2 G);

		/*
		template <class InstTy>
		using ConcreteFuncTemplate = std::function<void(const InstTy*,MetaIntRef,MetaIntRef)>;
		template <class InstTy>
		using SymbolicFuncTemplate = std::function<void(const InstTy*,solver::SharedExpr,solver::SharedExpr)>;

		template <class InstTy>
		void MixedEvalTemplate(const InstTy* inst, memory::HolderPtr left, memory::HolderPtr right,
				ConcreteFuncTemplate<InstTy>, SymbolicFuncTemplate<InstTy>);
				*/
	};
}

#endif













