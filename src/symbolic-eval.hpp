#ifndef __SYMBOLIC_EVAL_HPP__
#define __SYMBOLIC_EVAL_HPP__

#include "context.hpp"
#include "meta-int.hpp"
#include "llvm/Support/Casting.h"
# include "llvm/IR/Instructions.h"
#include "llvm/IR/BasicBlock.h"
#include "expr.hpp"
#include "meta-kind.hpp"

// fork support
#include <unistd.h>
#include <sys/wait.h>
#include <sys/types.h>

namespace interpreter {
	class SymbolicEval {
	public:
		SymbolicEval(ContextRef context);
		void BinOp (memory::RamAddress lhs, unsigned bin_op, solver::SharedExpr left, solver::SharedExpr right);
		void IntComparison (memory::RamAddress lhs, llvm::ICmpInst::Predicate predicate, solver::SharedExpr left, solver::SharedExpr right);
		void Conversion (memory::RamAddress lhs, solver::SharedExpr rhs, utils::MetaKind kind, unsigned width);
		void Assign (memory::RamAddress lhs, solver::SharedExpr target);
		const llvm::BasicBlock* Branch (solver::SharedExpr condition, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
		memory::HolderPtr Select(memory::RamAddress lhs, solver::SharedExpr condition, memory::HolderPtr trueval, memory::HolderPtr falseval);
	private:
		solver::Kind OpCode_To_Kind(unsigned op_code);
		solver::Kind Predicate_To_Kind(llvm::ICmpInst::Predicate predicate);
		solver::Kind ConversionHelper(utils::MetaKind kind);
		const llvm::BasicBlock* BranchHelper(const solver::SharedExpr& condition, bool branch_marker, const llvm::BasicBlock* branch_ptr);
		void FlushAll();
		ContextRef context_;
		solver::SharedExpr BoolTrue();
		solver::SharedExpr BoolFalse();
		solver::SharedExpr BitTrue();
		solver::SharedExpr BitFalse();
	};
}

#endif
