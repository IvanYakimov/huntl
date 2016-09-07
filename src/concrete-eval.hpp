#ifndef __CONCRETE_EVAL_HPP__
#define __CONCRETE_EVAL_HPP__

#include "llvm/Support/Casting.h"
#include "llvm/IR/Instructions.h"
#include "meta-int.hpp"
#include "holder.hpp"
#include "context.hpp"
#include "meta-kind.hpp"
#include "ram-delc.hpp"

namespace interpreter {
	class ConcreteEval {
	public:
		ConcreteEval(interpreter::ContextRef context);
		void Conversion (memory::RamAddress lhs, interpreter::MetaIntRef rhs, utils::MetaKind kind, unsigned width);
		void BinOp (memory::RamAddress lhs, unsigned op_code, interpreter::MetaIntRef left_val, interpreter::MetaIntRef right_val);
		void IntComparison(memory::RamAddress lhs, llvm::ICmpInst::Predicate predicate, interpreter::MetaIntRef left_val, interpreter::MetaIntRef right_val);
		void Assign (memory::RamAddress lhs, interpreter::MetaIntRef value);
		const llvm::BasicBlock* Branch (interpreter::MetaIntRef condition, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
		memory::HolderPtr Select(memory::RamAddress lhs, interpreter::MetaIntRef cond, memory::HolderPtr trueval, memory::HolderPtr falseval);
	private:
		const MetaInt True;
		const MetaInt False;
		interpreter::ContextRef context_;
		MetaInt Bool_To_MetaInt(bool result);
		inline interpreter::MetaInt BinOp__helper(unsigned op_code, interpreter::MetaIntRef left_val, interpreter::MetaIntRef right_val);
		inline bool IntComparison__helper(llvm::ICmpInst::Predicate opcode, interpreter::MetaIntRef left_val, interpreter::MetaIntRef right_val);
		inline MetaInt Conversion__helper (MetaIntRef rhs, utils::MetaKind kind, unsigned widht);
	};
}

#endif
