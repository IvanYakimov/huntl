#include "evaluator.hpp"

//TODO: refactoring:
//#include "llvm/IR/Instruction.h"
using namespace llvm;

namespace interpreter {
	using utils::Create;
	using memory::ArgMap;
	using memory::HolderPtr;

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

	Evaluator::Evaluator(interpreter::ContextRef context) :
			context_(context),
			meta_eval_(context) {
	}

	Evaluator::~Evaluator() {

	}

	Evaluator::MkSym::MkSym(ContextRef context, unsigned size) : context_(context), size_(size) {}
	memory::HolderPtr Evaluator::MkSym::operator()(llvm::Function* f, memory::ArgMapPtr args) {
		//assert (args->empty() == true);
		return memory::Symbolic::Create(context_.Solver().MkVar(context_.Solver().MkBitVectorType(size_)));
	}

	void Evaluator::ProcessModule(llvm::Module *m) {
		errs() << "------------------------\nvisit module:\n";
		errs() << "funcs in module: \n";
		assert (m->begin() != m->end());
		std::list<llvm::Function*> test_functions;
		for (auto f_it = m->begin(); f_it != m->end(); f_it++) {
			std::string name = f_it->getName().str();

			std::regex mksym_regex("mksym_");
			std::smatch mksym_matches;
			auto matched_mksym = std::regex_search(name, mksym_matches, mksym_regex);

			std::regex test_NAME_regex("test_");
			std::smatch test_NAME_matches;
			auto matched_test_NAMEs = std::regex_search(name, test_NAME_matches, test_NAME_regex);

			if (matched_mksym == 1) {
				std::string suffix = mksym_matches.suffix();
				std::regex iuN_regex("[[:digit:]]+");
				std::smatch iuN_match;
				auto matched_iuN = std::regex_search(suffix, iuN_match, iuN_regex);
				if (matched_iuN == 1) {
					std::string subtype = iuN_match.prefix();
					std::string bitwidth_str = *iuN_match.begin();
					int bitwidth_val = std::stoi(bitwidth_str);
					builtins_.emplace(f_it, MkSym(context_, bitwidth_val));
					errs() << "builtint matched: " << name << "\n";
				}
			}
			else if (matched_test_NAMEs == 1) {
					errs() << "test matched: " << name << "\n";
					test_functions.push_back(f_it);
			}
			else {
				errs() << "ordinary function: " << name << "\n";
			}
		}

		for (auto it = test_functions.begin(); it != test_functions.end(); it++) {
			auto args = utils::Create<interpreter::ArgMap>();
			auto ret = CallFunction(*it,args);
		}
	}

	memory::HolderPtr Evaluator::CallFunction(llvm::Function *f, memory::ArgMapPtr args) {
		memory::HolderPtr ret_val = nullptr;
		auto is_builtin = builtins_.find(f);
		if (is_builtin != builtins_.end()) {
			context_.Push(); {
			ret_val = is_builtin->second(f, args);
			}
			context_.Pop();
		}
		else {
			// push
			context_.Push(); {
				// initiate args
				for_each(args->begin(), args->end(), [&](auto pair){
					auto addr = pair.first;
					auto hldr = pair.second;
					// assign
					meta_eval_.Assign(addr, hldr);
				});

				visit (f);

				/*
				// save new arg valuesy (it is useful for test generation purposes)
				for_each(args->begin(), args->end(), [&](auto pair) {
					pair.second = context_.Top()->Load(pair.first);
				});
				*/

				ret_val = context_.Top()->RetVal.Get();
			}
			context_.Pop(); // pop
		}
		return ret_val;
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

		llvm::errs() << "------------------------------------\n";
		llvm::errs() << "{\n";
		llvm::errs() << inst << "\n";
		context_.Top()->Print();
		context_.Solver().Print();
		llvm::errs() << "}\n";
	}

	// Return
	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
		// Load holder from '&inst'
		// Store it to 'ret_inst'
		auto holder = context_.Top()->Load(ret_inst);
		meta_eval_.Assign(&inst, holder);
		context_.Top()->RetVal.Set(holder);
		Trace(inst);
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::ConstantInt *ret_const) {
		// Produce	new concrete holder
		auto holder = ProduceHolder(ret_const);
		// Store it in 'ret_const'
		meta_eval_.Assign(&inst, holder);
		context_.Top()->RetVal.Set(holder);
		//assert (false && "not implemented");
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
		auto right_holder = context_.Top()->Load(right);
		meta_eval_.BinOp(&inst, left_holder, right_holder);
		Trace(inst);
	}

	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = ProduceHolder(right);
		meta_eval_.BinOp(&inst, left_holder, right_holder);
		Trace(inst);
	}

	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *left, const llvm::Value *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = context_.Top()->Load(right);
		meta_eval_.BinOp(&inst, left_holder, right_holder);
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
		//TODO: move to meta_eval_
		context_.Top()->Alloca(&inst, holder);
		Trace(inst);
	}

	// Load
	void Evaluator::HandleLoadInst (const llvm::Instruction &inst, const llvm::Instruction *instruction) {
		// (assert (= v e))
		// Load object form 'ptr'
		// Store (associate) object to '&inst'
		auto holder = context_.Top()->Load(instruction);
		meta_eval_.Assign(&inst, holder);
		Trace(inst);
	}

	// Store
	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *constant_int, const llvm::Value *ptr) {
		auto holder = ProduceHolder(constant_int);
		meta_eval_.Assign(ptr, holder);
		Trace(inst);
	}

	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {
		auto holder = context_.Top()->Load(instruction);
		meta_eval_.Assign(ptr, holder);
		Trace(inst);
	}

	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::Argument *arg, const llvm::Value *ptr) {
		auto holder = context_.Top()->Load(arg);
		meta_eval_.Assign(ptr, holder);
		Trace(inst);
	}

	void Evaluator::HandleCallInst(const llvm::CallInst &inst) {
		//TODO: meta_eval_.Assign(...) for all operand values
		auto called = inst.getCalledFunction();
		assert (called != nullptr and "indirect function invocation not supported");
		memory::ArgMapPtr argmap = utils::Create<ArgMap>();
		auto args = called->arg_begin();
		for (auto i = 0; i != inst.getNumArgOperands(); i++) {
			auto address = inst.getArgOperand(i);
			auto holder = context_.Top()->Load(address);
			argmap->emplace(args, holder);
			args++;
		}

		//TODO: Put constrains for args x1,x2...xn back to the caller!!!?????????

		memory::HolderPtr ret_holder = CallFunction(called, argmap);
		assert (ret_holder != nullptr);

		meta_eval_.Assign(&inst, ret_holder);
	}
}





















