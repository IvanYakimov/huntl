#include "matcher-stub.hpp"

namespace interpreter {
	using namespace llvm;

	class Printer {
	//template<class... Args>
	//std::string PrintType(const llvm::Value *val, Args... args);
	//std::string PrintType(const llvm::Value *val);
	public:
		template<class... Args>
		static void Do(Args... args) {
			errs() << "[ " + PrintType(args...) + " ]\n";
		}

	private:
		static std::string PrintType(const llvm::Value *val) {
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

		template<class... Args>
		static std::string PrintType(const llvm::Value *val, Args... args) {
			return PrintType(val) + " " + PrintType(args...);
		}
	};

	// Return
	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
		Printer::Do(&inst, ret_inst);
		FAIL();
	}

	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst, const llvm::Constant *ret_const) {
		Printer::Do(&inst, ret_const);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Constant>(ret_const));
	}

	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst, const llvm::Value *ret_val) {
		Printer::Do(&inst, ret_val);
		FAIL();
	}

	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst) {
		Printer::Do(&inst);
		ASSERT_TRUE(isa<Instruction>(inst));
		FAIL();
	}

	// Branch
	void MatcherStub::HandleBranchInst (const llvm::Instruction &inst,
		  const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		Printer::Do(&inst, cond, iftrue, iffalse);
		FAIL();
	}

	void MatcherStub::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {
		Printer::Do(&inst, jump);
		FAIL();
	}

	// Cmp
	void MatcherStub::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {
		Printer::Do(&inst, lhs, rhs);
		FAIL();
	}

	// Alloca
	void MatcherStub::HandleAllocaInst (const llvm::Instruction &inst, const llvm::Value *allocated) {
		Printer::Do(&inst, allocated);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Value>(allocated));
	}

	// Load
	void MatcherStub::HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr) {
		Printer::Do(&inst, ptr);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Value>(ptr));
	}

	// Store
	void MatcherStub::HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *val, const llvm::Value *ptr) {
		Printer::Do(&inst, val, ptr);
		FAIL();
	}

	void MatcherStub::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {
		Printer::Do(&inst, instruction, ptr);
		FAIL();
	}

	void MatcherStub::HandleStoreInst (const llvm::Instruction &inst, const llvm::Constant *constant, const llvm::Value *ptr) {
		Printer::Do(&inst, constant, ptr);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Constant>(constant)
				and isa<Value>(ptr));
	}
}




















