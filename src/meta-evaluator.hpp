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
//#include "path-constraint.hpp"

namespace interpreter {
	class MetaEvaluator {
	public:
		MetaEvaluator();
		~MetaEvaluator();
		void Assign (const llvm::Value *destination, const llvm::ConstantInt *target);
		void Assign (const llvm::Value *destination, const llvm::Instruction *target);
	};
}

#endif













