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

		template<class... Args>
		static std::string PrintType(const llvm::Value *val, Args... args) {
			return PrintType(val) + " " + PrintType(args...);
		}
	};

	// Return
	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
		Printer::Do(&inst, ret_inst);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Instruction>(ret_inst));
	}

	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst, const llvm::Constant *ret_const) {
		Printer::Do(&inst, ret_const);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Constant>(ret_const));
	}

	void MatcherStub::HandleReturnInst (const llvm::Instruction &inst) {
		Printer::Do(&inst);
		ASSERT_TRUE(isa<Instruction>(inst));
	}

	// Branch
	void MatcherStub::HandleBranchInst (const llvm::Instruction &inst,
		  const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		Printer::Do(&inst, cond, iftrue, iffalse);
		ASSERT_TRUE(isa<Value>(cond)
				and isa<BasicBlock>(iftrue)
				and isa<BasicBlock>(iffalse));
	}

	void MatcherStub::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {
		Printer::Do(&inst, jump);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<BasicBlock>(jump));
	}

	// BinOp
	void MatcherStub::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {
		Printer::Do(&inst, lhs, rhs);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Value>(lhs)
				and isa<Value>(rhs));
	}

	// Cmp
	void MatcherStub::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {
		Printer::Do(&inst, lhs, rhs);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Value>(lhs)
				and isa<Value>(rhs));
	}

	// Alloca
	void MatcherStub::HandleAllocaInst (const llvm::Instruction &inst, const llvm::ConstantInt *allocated) {
		Printer::Do(&inst, allocated);
		errs() << allocated->getZExtValue() << "\n";
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<ConstantInt>(allocated));
	}

	// Load
	void MatcherStub::HandleLoadInst (const llvm::Instruction &inst, const llvm::Value *ptr) {
		Printer::Do(&inst, ptr);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Value>(ptr));
	}

	void MatcherStub::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {
		errs() << ptr->getName() << "\n";
		Printer::Do(&inst, instruction, ptr);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Instruction>(instruction)
				and isa<Value>(ptr));
	}

	void MatcherStub::HandleStoreInst (const llvm::Instruction &inst, const llvm::Constant *constant, const llvm::Value *ptr) {
		errs() << ptr->getName() << "\n";
		Printer::Do(&inst, constant, ptr);
		ASSERT_TRUE(isa<Instruction>(inst)
				and isa<Constant>(constant)
				and isa<Value>(ptr));
	}
}




















