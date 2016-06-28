#ifndef __META_EVALUATOR_HPP__
#define __META_EVALUATOR_HPP__

// STL
#include <exception>

# include "llvm/IR/InstVisitor.h"
# include "llvm/IR/Instruction.h"
# include "llvm/Support/raw_ostream.h"
# include "llvm/Support/Debug.h"

#include "bitvec.hpp"
// Inherited from
//#include "matcher.hpp"

// Uses
#include "display.hpp"
#include "singleton.hpp"
#include "holder.hpp"
//#include "path-constraint.hpp"

namespace interpreter {
	class MetaEvaluator {
	public:
		MetaEvaluator(memory::DisplayPtr display);
		~MetaEvaluator();
		void BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right);
		void Assign (const llvm::Value *destination, const llvm::ConstantInt *target);
		void Assign (const llvm::Value *destination, const llvm::Instruction *target);
	private:
		memory::DisplayPtr display_;
	};
}

#endif













