#include "evaluator.hpp"

//TODO: refactoring:
//#include "llvm/IR/Instruction.h"
using namespace llvm;

namespace interpreter {
	class Printer {
	//template<class... Args>
	//std::string PrintType(const llvm::Value *val, Args... args);
	//std::string PrintType(const llvm::Value *val);
	public:
		template<class... Args>
		static std::string Do(Args... args) {
			return + "[ " + PrintType(args...) + " ]";
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
	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
		// Load holder from '&inst'
		// Store it to 'ret_inst'
		llvm::errs() << inst << "\n";
		meta_eval_.Assign(&inst, ret_inst);
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::Constant *ret_const) {
		// Produce	new concrete holder
		// Store it in 'ret_const'
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst) {
	}

	// Branch
	void Evaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
	}

	void Evaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {
	}

	// BinOp
	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {

	}

	// Cmp
	void Evaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *lhs, const llvm::Value *rhs) {
		auto get_op = [](const llvm::Instruction &inst) {
			auto icmp_inst = llvm::dyn_cast<llvm::ICmpInst>(&inst);
			switch (icmp_inst->getPredicate()) {
				//case CmpInst::Predicate::ICMP_SLT: return solver::BinOp::LESS_THAN;
				//default: InterruptionHandler::Do(new InterpretationFailure(inst));
			};
		};

		// Load left and right args.
		// Produce expression, use get_op, defined above
	}

	// Alloca
	void Evaluator::HandleAllocaInst (const llvm::Instruction &inst, const llvm::ConstantInt *allocated) {
		errs() << inst << "\n";
		// Get 'allocated' value
		llvm::IntegerType* ty = allocated->getType();
		auto width = ty->getBitWidth();
		const llvm::APInt& val = allocated->getValue();
		auto holder = memory::Concrete::Create(val);
		auto display = utils::GetInstance<memory::Display>();
		// Alloca to 'inst'
		display->Alloca(&inst, holder);
		display->Print();
	}

	// Load
	void Evaluator::HandleLoadInst (const llvm::Instruction &inst, const llvm::Instruction *instruction) {
		// (assert (= v e))
		// Load object form 'ptr'
		// Store (associate) object to '&inst'
		errs() << inst << "\n";
		meta_eval_.Assign(&inst, instruction);

		/*

		auto display = utils::GetInstance<memory::Display>();
		auto loaded_rhs = display->Load(ptr);
		// Store holder to ptr
		if (memory::IsConcrete(loaded_rhs)) {
			solver::BitVec rhs_val = Object::UpCast<memory::Concrete>(loaded_rhs)->Get();
			auto updated_lhs = memory::Concrete::Create(rhs_val);
			display->Store(&inst, updated_lhs);
		}
		else {
			assert (false && "not impl");
		}
		display->Print();
		*/
	}

	// Store
	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *constant_int, const llvm::Value *ptr) {
		errs() << inst << "\n";
		meta_eval_.Assign(ptr, constant_int);
		/*
		// Get value of 'constant_int'
		llvm::APInt value = constant_int->getValue();
		auto holder = memory::Concrete::Create(value);
		// Store it to 'ptr'
		auto display = utils::GetInstance<memory::Display>();
		display->Store(ptr, holder);
		display->Print();
		*/
	}

	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {
		meta_eval_.Assign(ptr, instruction);
		/*
		// Load holder from instruction
		auto display = utils::GetInstance<memory::Display>();
		auto loaded_rhs = display->Load(instruction);
		// Store holder to ptr
		if (memory::IsConcrete(loaded_rhs)) {
			solver::BitVec rhs_val = Object::UpCast<memory::Concrete>(loaded_rhs)->Get();
			auto updated_lhs = memory::Concrete::Create(rhs_val);
			display->Store(ptr, updated_lhs);
		}
		else {
			assert (false && "not impl");
		}
		*/
	}
}








