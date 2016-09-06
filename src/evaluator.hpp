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
		memory::HolderPtr ProduceHolder(const llvm::Value* target);
		BuiltInMap builtins_;
		memory::ArgMapPtr ProduceArgMap(const llvm::CallInst &inst);
		void EvaluateFunctionList(std::list<llvm::Function*> test_functions);
		void EvaluateTopFunction(llvm::Function* f);
		void AssignCallResult(const llvm::CallInst& inst, memory::HolderPtr ret_holder);
		void AssignTopFunctionArgs(memory::ArgMapPtr);

	private:
		// Return
		virtual void HandleReturnInst (const llvm::ReturnInst &inst, const llvm::Value *ret_inst);
		virtual void HandleReturnInst (const llvm::ReturnInst &inst);

		// Branch
		virtual void HandleBranchInst (const llvm::BranchInst &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse);
		virtual void HandleBranchInst (const llvm::BranchInst &inst, const llvm::BasicBlock *jump);

		// BinOp
		virtual void HandleBinOp (const llvm::BinaryOperator &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Cmp
		virtual void HandleICmpInst (const llvm::ICmpInst &inst, const llvm::Value *lhs, const llvm::Value *rhs);

		// Alloca
		virtual void HandleAllocaInst (const llvm::AllocaInst &variable, const llvm::ConstantInt *value, const llvm::Type *allocated_type);

		// Load
		virtual void HandleLoadInst (const llvm::LoadInst &lhs, const llvm::Value *ptr);

		// Store
		virtual void HandleStoreInst (const llvm::StoreInst &inst, const llvm::Value *value, const llvm::Value *ptr);

		// GetElementPtr
		virtual void HandleGetElementPtr (const llvm::GetElementPtrInst& inst, const llvm::Value *target, const llvm::Value *start_from, const llvm::Value *index);
		virtual void HandleGetElementPtr (const llvm::GetElementPtrInst& inst, const llvm::Value *target, const llvm::Value *index);

		// Trunc
		virtual void HandleTruncInst (const llvm::TruncInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty);
		// ZExt
		virtual void HandleZExtInst (const llvm::ZExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty);
		// SExt
		virtual void HandleSExtInst (const llvm::SExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty);
		// PtrToInt
		virtual void HandlePtrToInt (const llvm::PtrToIntInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty);
		// IntToPtr
		virtual void HandleIntToPtr (const llvm::IntToPtrInst &inst, const llvm::Value* target, const llvm::PointerType* dest_ty);
		// PHINode
		virtual void HandlePHINode(const llvm::PHINode &phi_node);
		// Call
		virtual void HandleCallInst(const llvm::CallInst &inst);
};
}

# endif /* __INTERPRETER_HPP__ */













