# ifndef __STATEMENT_EVALUATOR_HPP__
# define __STATEMENT_EVALUATOR_HPP__

// STL
#include <exception>
#include <string>

#include "activation.hpp"
#include "local-memory.hpp"
#include "matcher.hpp"

// Uses
#include "meta-evaluator.hpp"
#include "meta-int.hpp"
#include "solver.hpp"
#include "context.hpp"

//TODO: use -I option to perform headers search instead of ../ (?)

namespace interpreter {
	class Evaluator final : public Matcher {
	public:
		Evaluator(interpreter::ContextRef context);
		~Evaluator();

		void Do(llvm::Module *m);
		void Do(llvm::Function *func);

	private:
		MetaEvaluator meta_eval_;
		interpreter::ContextRef context_;
		auto ProduceHolder(const llvm::ConstantInt* constant_int);
		void Trace(const llvm::Instruction& inst);
	private:
		// Return
		virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst);
		virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Constant *ret_const);
		virtual void HandleReturnInst (const llvm::Instruction &inst);

		// Branch
		virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
		virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump);

		// BinOp
		virtual void HandleBinOp (const llvm::Instruction &inst, const llvm::ConstantInt *lhs, const llvm::Value *rhs);
		virtual void HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::ConstantInt *rhs);
		virtual void HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Cmp
		virtual void HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Alloca
		virtual void HandleAllocaInst (const llvm::Instruction &inst, const llvm::ConstantInt *allocated);

		// Load
		virtual void HandleLoadInst (const llvm::Instruction &inst, const llvm::Instruction *instruction);

		// Store
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *constant_int, const llvm::Value *ptr);
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr);
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Argument *arg, const llvm::Value *ptr);

		virtual void HandleCallInst(const llvm::CallInst &inst);
};
}

# endif /* __INTERPRETER_HPP__ */













