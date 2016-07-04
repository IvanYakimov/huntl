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

	Evaluator::Evaluator(memory::ActivationRecordPtr activation, solver::SolverPtr solver) {
		display_ = memory::Display::Create();
		solver_ = solver;
		activation_ = activation;
		meta_eval_ = interpreter::MetaEvaluator::Create(display_, solver_);
	}

	Evaluator::~Evaluator() {

	}


	void Evaluator::Do(llvm::Module *m) {
		errs() << "$$$$$$$$$$$$$$$$$$$$$$$$$$$\nvisit module:\n";
		errs() << "funcs in module: \n";
		for (auto f_it = m->begin(); f_it != m->end(); f_it++) {
			errs() << f_it->getName() << "\n";
		}
		visit (m);
	}

	void Evaluator::Do(llvm::Function *f) {
		const std::string mksym_ = "mksym_";
		const std::string test_ = "test_";
		std::string name = f->getName().str();
		if (name.substr(mksym_.length()) == mksym_) {
			if (name == "mksym_i32") {
				assert (false and "make symbolic call");
			}
			else
				assert (false and "not implemented");
		}
		else if (name.substr(test_.length()) == test_) {

		}
		else {
			visit (f);
		}
	}

	auto Evaluator::ProduceHolder(const llvm::ConstantInt* allocated) {
		// Get 'allocated' value
		llvm::IntegerType* ty = allocated->getType();
		auto width = ty->getBitWidth();
		const llvm::APInt& val = allocated->getValue();
		auto holder = memory::Concrete::Create(val);
		return holder;
	}

	void Evaluator::Trace(const llvm::Instruction& inst) {
		llvm::outs() << "------------------------------------\n";
		llvm::outs() << "{\n";
		llvm::outs() << inst << "\n";
		display_->Print();
		if (solver_)
			solver_->Print();
		llvm::outs() << "}\n";
	}

	// Return
	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
		// Load holder from '&inst'
		// Store it to 'ret_inst'
		auto holder = display_->Load(ret_inst);
		meta_eval_->Assign(&inst, holder);
		activation_->SetRet(holder);
		Trace(inst);
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::Constant *ret_const) {
		// Produce	new concrete holder
		// Store it in 'ret_const'
		assert (false && "not implemented");
		Trace(inst);
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst) {
		assert (false && "not implemented");
		Trace(inst);
	}

	// Branch
	void Evaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		assert (false && "not implemented");
	}

	void Evaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {
		assert (false && "not implemented");
	}

	// BinOp
	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::ConstantInt *left, const llvm::Value *right) {
		auto left_holder = ProduceHolder(left);
		auto right_holder = display_->Load(right);
		meta_eval_->BinOp(&inst, left_holder, right_holder);
		Trace(inst);
	}

	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		auto left_holder = display_->Load(left);
		auto right_holder = ProduceHolder(right);
		meta_eval_->BinOp(&inst, left_holder, right_holder);
		Trace(inst);
	}

	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *left, const llvm::Value *right) {
		auto left_holder = display_->Load(left);
		auto right_holder = display_->Load(right);
		meta_eval_->BinOp(&inst, left_holder, right_holder);
		Trace(inst);
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
		assert (false && "not implemented");
	}

	// Alloca
	void Evaluator::HandleAllocaInst (const llvm::Instruction &inst, const llvm::ConstantInt *allocated) {
		// Get 'allocated' value
		auto holder = ProduceHolder(allocated);
		//auto display = utils::GetInstance<memory::Display>();
		// Alloca to 'inst'
		display_->Alloca(&inst, holder);
		Trace(inst);
	}

	// Load
	void Evaluator::HandleLoadInst (const llvm::Instruction &inst, const llvm::Instruction *instruction) {
		// (assert (= v e))
		// Load object form 'ptr'
		// Store (associate) object to '&inst'
		auto holder = display_->Load(instruction);
		meta_eval_->Assign(&inst, holder);
		Trace(inst);
	}

	// Store
	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *constant_int, const llvm::Value *ptr) {
		auto holder = ProduceHolder(constant_int);
		meta_eval_->Assign(ptr, holder);
		Trace(inst);
	}

	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {
		auto holder = display_->Load(instruction);
		meta_eval_->Assign(ptr, holder);
		Trace(inst);
	}

	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::Argument *arg, const llvm::Value *ptr) {
		auto holder = activation_->GetArg(arg);
		meta_eval_->Assign(ptr, holder);
		Trace(inst);
	}

	void Evaluator::HandleCallInst(const llvm::CallInst &inst) {

	}
}





















