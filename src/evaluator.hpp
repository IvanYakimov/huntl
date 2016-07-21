# ifndef __EVALUATOR_HPP__
# define __EVALUATOR_HPP__

// STL
#include <exception>
#include <string>
#include <regex>
//#include <functional>
#include <list>

// fork support
//#include <unistd.h>
//#include <sys/wait.h>
//#include <sys/types.h>

#include "activation.hpp"
#include "local-memory.hpp"
#include "matcher.hpp"

// Uses
#include "meta-evaluator.hpp"
#include "meta-int.hpp"
#include "solver.hpp"
#include "context.hpp"
#include "converter.hpp"
#include "eval-tracer.hpp"
#include "built-in-impl.hpp"

//#include "llvm/ExecutionEngine/ExecutionEngine.h"
//#include "llvm/ExecutionEngine/GenericValue.h"

//TODO: use -I option to perform headers search instead of ../ (?)

namespace interpreter {
	class Evaluator final : public Matcher {
	public:

		Evaluator(interpreter::ContextRef context);
		~Evaluator();
		NONCOPYABLE(Evaluator);
		void ProcessModule(llvm::Module *m);
		memory::HolderPtr CallFunction(llvm::Function *func, memory::ArgMapPtr args);

	private:
		MetaEvaluator meta_eval_;
		interpreter::ContextRef context_;
		EvalTracer tracer_;
		auto ProduceHolder(const llvm::ConstantInt* constant_int);
		BuiltInMap builtins_;

		bool IsPointerToPointer(const llvm::Value* value);
		bool IsDereferencing(const llvm::Instruction& load_inst, const llvm::Value* ptr);
		bool IsAddressing(const llvm::Instruction& store_inst, const llvm::Value* ptr);

	private:
		// Return
		virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst);
		virtual void HandleReturnInst (const llvm::Instruction &inst, const llvm::ConstantInt *ret_const);
		virtual void HandleReturnInst (const llvm::Instruction &inst);

		// Branch
		virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
		virtual void HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump);

		// BinOp
		virtual void HandleBinOp (const llvm::Instruction &inst, const llvm::ConstantInt *lhs, const llvm::Value *rhs);
		virtual void HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::ConstantInt *rhs);
		virtual void HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Cmp
		virtual void HandleICmpInst (const llvm::Instruction &inst, const llvm::ConstantInt *lhs, const llvm::Value *rhs);
		virtual void HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::ConstantInt *rhs);
		virtual void HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Alloca
		virtual void HandleAllocaInst (const llvm::Instruction &inst, const llvm::ConstantInt *allocated);

		// Load
		virtual void HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *target);

		// Store
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *rhs, const llvm::Value *lhs);
		virtual void HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *rhs, const llvm::Value *lhs);

		// Trunc
		virtual void HandleTruncInst (const llvm::Instruction &inst, const llvm::Value* target) = 0;
		// ZExt
		virtual void HandleZExtInst (const llvm::Instruction &inst, const llvm::Value* target) = 0;
		// SExt
		virtual void HandleSExtInst (const llvm::Instruction &inst, const llvm::Value* target) = 0;

		// Call
		virtual void HandleCallInst(const llvm::CallInst &inst);
};
}

# endif /* __INTERPRETER_HPP__ */













