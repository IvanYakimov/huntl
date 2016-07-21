#ifndef __CONCRETE_EVAL_HPP__
#define __CONCRETE_EVAL_HPP__

#include "llvm/Support/Casting.h"
#include "llvm/IR/Instructions.h"
#include "meta-int.hpp"
#include "holder.hpp"
#include "context.hpp"
#include "meta-kind.hpp"

namespace interpreter {
	class ConcreteEval {
	public:
		ConcreteEval(interpreter::ContextRef context);
		void Conversion (const llvm::Instruction* lhs, interpreter::MetaIntRef rhs, MetaKind kind, unsigned width);
		void BinOp (const llvm::Instruction* inst, interpreter::MetaIntRef left_val, interpreter::MetaIntRef right_val);
		void IntComparison(const llvm::Instruction* inst, interpreter::MetaIntRef left_val, interpreter::MetaIntRef right_val);
		void Assign (const llvm::Value* destination, interpreter::MetaIntRef value);
		const llvm::BasicBlock* Branch (const llvm::Instruction *inst, interpreter::MetaIntRef condition, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
	private:
		const MetaInt True;
		const MetaInt False;
		interpreter::ContextRef context_;
		inline interpreter::MetaInt BinOp__helper(const llvm::Instruction* inst, interpreter::MetaIntRef left_val, interpreter::MetaIntRef right_val);
		inline bool IntComparison__helper(const llvm::ICmpInst* inst, interpreter::MetaIntRef left_val, interpreter::MetaIntRef right_val);
		inline MetaInt Conversion__helper (MetaIntRef rhs, MetaKind kind, unsigned widht);
	};
}

#endif
