#ifndef __EVAL_TRACER_HPP__
#define __EVAL_TRACER_HPP__

#include "object.hpp"
#include "context.hpp"
#include "holder.hpp"
#include "converter.hpp"
#include "llvm/IR/InstVisitor.h"
#include "activation.hpp"

#include <regex>
#include <string>

namespace interpreter {
	class EvalTracer {
	public:
		EvalTracer(ContextRef context);
		~EvalTracer();
		NONCOPYABLE(EvalTracer);
		void Call(const llvm::Function* target, memory::ArgMapPtr args, bool status = true);
		void Block(const llvm::BasicBlock* next);
		void Assign(const llvm::Value& target);
		void Func(const llvm::Function* target);
		void Ret(const llvm::Value* target);
		void Ret();
		std::string TraceLevel();
	private:
		ContextRef context_;
		unsigned level_ = 0;
	};
}

#endif
