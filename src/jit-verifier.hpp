#ifndef __JIT_VERIFIER_HPP__
#define __JIT_VERIFIER_HPP__

#include "context.hpp"
#include "solution.hpp"
#include "holder.hpp"

#include <memory>
#include <vector>

#include "llvm/IR/InstVisitor.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"

namespace interpreter {
	class JITVerifier {
	public:
		JITVerifier(ContextRef context);
		~JITVerifier();
		std::vector<llvm::GenericValue> ProduceJITArgs(SolutionListPtr result_list);
		bool JIT(std::vector<llvm::GenericValue> jit_args, llvm::GenericValue expected);
	private:
		ContextRef context_;
	};
}

#endif
