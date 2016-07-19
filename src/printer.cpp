#include "printer.hpp"

namespace utils {
	using namespace llvm;
	std::string Printer::PrintType(const llvm::Value *val) {
		if (isa<Value>(val)) {
			if (isa<Argument>(val))
				return "argument";
			else if (isa<BasicBlock>(val))
				return "basic-block";
			else if (isa<User>(val)) {
				if (isa<Constant>(val)) {
					if (isa<ConstantInt>(val))
						return "const-int";
					else if (isa<ConstantFP>(val))
						return "const-fp";
					else if (isa<ConstantPointerNull>(val))
						return "const-nullptr";
					else
						return "a-constant";
				}
				else if (isa<Instruction>(val)) {
					if (isa<BinaryOperator>(val))
						return "binop";
					else if (isa<ReturnInst>(val))
						return "ret";
					else if (isa<LoadInst>(val))
						return "load";
					else if (isa<StoreInst>(val))
						return "store";
					else if (isa<AllocaInst>(val))
						return "alloca";
					else if (isa<CmpInst>(val))
						return "cmp";
					else if (isa<BranchInst>(val))
						return "br";
					else
						return "an-instruction";
				}
				/*else if (isa<Operator>(val)) {
					return "an-operator";
				}*/
			}
			else
				return "a-value";
		}
	}
}
