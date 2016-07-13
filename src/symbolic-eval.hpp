#ifndef __SYMBOLIC_EVAL_HPP__
#define __SYMBOLIC_EVAL_HPP__

#include "context.hpp"
#include "meta-int.hpp"
#include "llvm/IR/Instruction.h"
#include "expr.hpp"

namespace interpreter {
	class SymbolicEval {
	public:
		SymbolicEval(ContextRef context);
		void BinOp (const llvm::Instruction* inst, solver::SharedExpr left, solver::SharedExpr right);
		void ICmpInst (const llvm::Instruction* inst, solver::SharedExpr left, solver::SharedExpr right);
		void Assign (const llvm::Value *destination, solver::SharedExpr target);
	private:
		//solver::SharedExpr Concrete_To_Symbolic(interpreter::MetaIntRef concrete_val);
		solver::Kind ExtractKindFromInst(const llvm::Instruction* inst);
		solver::Kind ExtractKindFromICmpInst(const llvm::ICmpInst* inst);
		ContextRef context_;
	};
}

#endif
