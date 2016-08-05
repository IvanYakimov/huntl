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


// inherited from
#include "matcher.hpp"

// Uses
#include "meta-kind.hpp"
#include "solver.hpp"
#include "context.hpp"
#include "meta-int.hpp"
#include "converter.hpp"
#include "activation.hpp"
#include "eval-tracer.hpp"
#include "local-memory.hpp"
#include "built-in-impl.hpp"
#include "meta-evaluator.hpp"

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
		memory::ArgMapPtr InitArgMap(const llvm::CallInst &inst);
		void InitFuncRet(memory::HolderPtr ret_holder, const llvm::CallInst& inst, llvm::Function* called);
		memory::HolderPtr ProduceOperandHolder(const llvm::Value* operand);

	private:
		// Return
		virtual void HandleReturnInst (const llvm::ReturnInst &inst, const llvm::Instruction *ret_inst);
		virtual void HandleReturnInst (const llvm::ReturnInst &inst, const llvm::ConstantInt *ret_const);
		virtual void HandleReturnInst (const llvm::ReturnInst &inst);

		// Branch
		virtual void HandleBranchInst (const llvm::BranchInst &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
		virtual void HandleBranchInst (const llvm::BranchInst &inst, const llvm::BasicBlock *jump);

		// BinOp
		virtual void HandleBinOp (const llvm::BinaryOperator &inst, const llvm::ConstantInt *lhs, const llvm::Value *rhs);
		virtual void HandleBinOp (const llvm::BinaryOperator &inst, const llvm::Value *lhs, const llvm::ConstantInt *rhs);
		virtual void HandleBinOp (const llvm::BinaryOperator &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Cmp
		virtual void HandleICmpInst (const llvm::ICmpInst &inst, const llvm::ConstantInt *lhs, const llvm::Value *rhs);
		virtual void HandleICmpInst (const llvm::ICmpInst &inst, const llvm::Value *lhs, const llvm::ConstantInt *rhs);
		virtual void HandleICmpInst (const llvm::ICmpInst &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Alloca
		virtual void HandleAllocaInst (const llvm::AllocaInst &variable, const llvm::ConstantInt *value);

		// Load
		virtual void HandleLoadInst (const llvm::LoadInst &lhs, const llvm::Value *ptr);

		// Store
		virtual void HandleStoreInst (const llvm::StoreInst &inst, const llvm::ConstantInt *value, const llvm::Value *ptr);
		virtual void HandleStoreInst (const llvm::StoreInst &inst, const llvm::Value *value, const llvm::Value *ptr);

		// Trunc
		virtual void HandleTruncInst (const llvm::TruncInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty);
		// ZExt
		virtual void HandleZExtInst (const llvm::ZExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty);
		// SExt
		virtual void HandleSExtInst (const llvm::SExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty);

		// Call
		virtual void HandleCallInst(const llvm::CallInst &inst);
};
}

# endif /* __INTERPRETER_HPP__ */













