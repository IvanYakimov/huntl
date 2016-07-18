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

	Evaluator::Gen::Gen(ContextRef context, llvm::Function* target, llvm::Module* module) :
			context_(context), target_(target), module_(module) {}
	memory::HolderPtr Evaluator::Gen::operator()(llvm::Function* f, memory::ArgMapPtr args) {
		//TODO:
		//std::cerr << "with (" << args->size() << ") args:\n";
		std::list<memory::ConcretePtr> arg_sol_list;
		memory::ConcretePtr ret_sol;

		if (context_.Solver().IsSat() == true) {
			for(auto pair = args->begin(); pair != args->end(); pair++) {
				//std::cerr << *pair.second << "\n";
				HolderPtr holder = pair->second;
				if (memory::IsConcrete(holder)) {

				}
				else if (memory::IsSymbolic(holder)) {
					solver::SharedExpr e = memory::GetExpr(holder);
					interpreter::MetaInt val = context_.Solver().GetValue(e);
					holder = memory::Concrete::Create(val);
				}
				else
					assert (false and "unexpected behavior");


				auto ch = std::dynamic_pointer_cast<memory::Concrete>(holder);
				assert(ch != nullptr);
				if (std::next(pair,1) != args->end())
					arg_sol_list.push_back(ch);
				else
					ret_sol = ch;
			}
		}
		else
			assert (false and "not implemented");
		//std::cerr << "\n//----------------------------\nAUTOMATICALLY GENERATED TEST CASE FOR\n";
		std::cerr << "\n";
		std::cerr << target_->getName().str() << ":\t\t";
		for_each(arg_sol_list.begin(), arg_sol_list.end(), [&](auto arg_sol) {
			std::cerr << *arg_sol << " ";
		});

		std::cerr << " --> ";
		std::cerr << *ret_sol << "\n";

		//---------------------------------------------------------------------------
		// JIT:
		llvm::ExecutionEngine* jit = llvm::EngineBuilder(module_).create();
		std::vector<llvm::GenericValue> jit_args;

		for_each(arg_sol_list.begin(), arg_sol_list.end(), [&](auto arg_sol) {
			llvm::GenericValue gval;
			gval.IntVal = memory::GetValue(arg_sol);
			jit_args.push_back(gval);
		});

		llvm::GenericValue gres = jit->runFunction(target_, jit_args);

		//errs() << "\n//JIT verification - DONE. Result: " << gres.IntVal << "\n";

		assert(memory::GetValue(ret_sol) == gres.IntVal and "generated ret-value MUST be equivalent to one returned from JIT!");

		//std::cerr << "//END.\n//-----------------------------------\n\n";
		exit(0);
		//assert (false and "not implemented");
	}

	void Evaluator::ProcessModule(llvm::Module *m) {
		//errs() << "------------------------\nvisit module:\n";
		//errs() << "funcs in module: \n";
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

			std::regex gen_TARGET_regex("gen_");
			std::smatch gen_TARGET_matches;
			auto matched_gen_TARGETs = std::regex_search(name, gen_TARGET_matches, gen_TARGET_regex);

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
					//errs() << "builtint matched: " << name << "\n";
				}
			}
			else if (matched_test_NAMEs == 1) {
					//errs() << "test matched: " << name << "\n";
					test_functions.push_back(f_it);
			}
			else if (matched_gen_TARGETs == 1) {
				//errs() << "gen matched: " << name << "; ";
				std::string target_name = gen_TARGET_matches.suffix();

				StringRef llvm_styled_target_name(target_name.c_str());
				llvm::Function* target = m->getFunction(llvm_styled_target_name);
				//errs() << "with target: " << target->getName() << "\n";
				if (target == nullptr) {
					errs() << "no " << llvm_styled_target_name << " target found. stop." << "\n";
					exit(0);
				}
				builtins_.emplace(f_it, Gen(context_, target, m));
			}
			else {
				//this is ordinary function
			}
			//exit(0);
		}

		pid_t child_pid = 0;
		int ch_status = 0;
		for (auto it = test_functions.begin(); it != test_functions.end(); it++) {
			errs().flush();
			std::flush(std::cerr);
			child_pid = fork();
			if (child_pid > 0) {
				wait(&ch_status);
			}
			else {
				auto args = utils::Create<interpreter::ArgMap>();
				auto ret = CallFunction(*it,args);
			}
		}
	}

	memory::HolderPtr Evaluator::CallFunction(llvm::Function *f, memory::ArgMapPtr args) {
		// llvm::errs() << "call " << f->getName() << "\n";
		memory::HolderPtr ret_val = nullptr;
		auto is_builtin = builtins_.find(f);
		if (is_builtin != builtins_.end()) {
			//llvm::errs() << "this is a builtin function!\n";
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

				const llvm::BasicBlock* next_block = &*f->begin();
				context_.Top()->PC.Set(next_block);
				while (next_block != nullptr) {
					visit (const_cast<llvm::BasicBlock*>(next_block));
					next_block = context_.Top()->PC.Get();
				}

				//visit (f);

				ret_val = context_.Top()->RetVal.Get();
			}
			context_.Pop(); // pop
			//llvm::errs() << "return from " << f->getName() << "\n";
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
		/*
		llvm::errs() << "------------------------------------\n";
		llvm::errs() << "{\n";
		*/
		//llvm::errs() << inst << "\n";
		/*
		context_.Top()->Print();
		context_.Solver().Print();
		llvm::errs() << "}\n";
		*/
	}

	// Return
	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
		// Load holder from '&inst'
		// Store it to 'ret_inst'
		auto holder = context_.Top()->Load(ret_inst);
		meta_eval_.Assign(&inst, holder);
		context_.Top()->RetVal.Set(holder);
		context_.Top()->PC.Set(nullptr);
		Trace(inst);
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::ConstantInt *ret_const) {
		// Produce	new concrete holder
		auto holder = ProduceHolder(ret_const);
		// Store it in 'ret_const'
		meta_eval_.Assign(&inst, holder);
		context_.Top()->RetVal.Set(holder);
		context_.Top()->PC.Set(nullptr);
		//assert (false && "not implemented");
		Trace(inst);
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst) {
		assert (false && "not implemented");
		Trace(inst);
	}

	// Branch
	void Evaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		auto cond_holder = context_.Top()->Load(cond);
		assert (cond_holder != nullptr and "only instruction is supported yet");
		auto next = meta_eval_.Branch(&inst, cond_holder, iftrue, iffalse);
		context_.Top()->PC.Set(next);
		/*
		errs() << "################## BRACH MYSTERY!! ####################\n";
		errs() << inst << "\n";
		errs() << "cond:" << *cond << "\n";
		errs() << "iftrue: " << *iftrue << "\n";
		errs() << "iffalse: " << *iffalse << "\n";
		errs() << "################## BRACH MYSTERY!! ####################\n";
		*/
		//visit(next);
		Trace(inst);
	}

	void Evaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {
		auto next = jump;
		context_.Top()->PC.Set(next);
		//visit(next);
		Trace(inst);
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
	void Evaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::ConstantInt *left, const llvm::Value *right) {
		auto left_holder = ProduceHolder(left);
		auto right_holder = context_.Top()->Load(right);
		meta_eval_.IntComparison(&inst, left_holder, right_holder);

		// Load left and right args.
		// Produce expression, use get_op, defined above
		Trace(inst);
		//assert (false && "not implemented");
	}

	void Evaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = ProduceHolder(right);

		meta_eval_.IntComparison(&inst, left_holder, right_holder);
		// Load left and right args.
		// Produce expression, use get_op, defined above
		Trace(inst);
		//assert (false && "not implemented");
	}

	void Evaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *left, const llvm::Value *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = context_.Top()->Load(right);

		/*
		auto get_op = [](const llvm::Instruction &inst) {
			auto icmp_inst = llvm::dyn_cast<llvm::ICmpInst>(&inst);
			switch (icmp_inst->getPredicate()) {
				//case CmpInst::Predicate::ICMP_SLT: return solver::BinOp::LESS_THAN;
				//default: InterruptionHandler::Do(new InterpretationFailure(inst));
			};
		};
		*/

		meta_eval_.IntComparison(&inst, left_holder, right_holder);
		Trace(inst);
		// Load left and right args.
		// Produce expression, use get_op, defined above
		//assert (false && "not implemented");
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
		//llvm::errs() << "call " << inst.getCalledFunction()->getName() << "\n";
		//TODO: meta_eval_.Assign(...) for all operand values
		auto called = inst.getCalledFunction();
		assert (called != nullptr and "indirect function invocation not supported");
		memory::ArgMapPtr argmap = utils::Create<ArgMap>();
		auto args = called->arg_begin();
		for (auto i = 0; i != inst.getNumArgOperands(); i++) {
			auto operand = inst.getArgOperand(i);
			HolderPtr holder = nullptr;

			if (llvm::isa<llvm::ConstantInt>(operand)) {
				holder = ProduceHolder(llvm::dyn_cast<llvm::ConstantInt>(operand));
			}
			else {
				holder = context_.Top()->Load(operand);
			}

			assert (holder != nullptr);
			argmap->emplace(args, holder);
			args++;
		}
		assert (args == called->arg_end());

		//TODO: Put constrains for args x1,x2...xn back to the caller!!!?????????

		memory::HolderPtr ret_holder = CallFunction(called, argmap);
		assert (ret_holder != nullptr);

		meta_eval_.Assign(&inst, ret_holder);
	}
}





















