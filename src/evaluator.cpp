#include "evaluator.hpp"

//TODO: refactoring:
//#include "llvm/IR/Instruction.h"
using namespace llvm;

namespace interpreter {
	using utils::Create;
	using memory::ArgMap;
	using memory::HolderPtr;
	using memory::Undef;

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
		//context_.Top()->PC.Set(nullptr);
		//TODO: fix this bug:
		exit(0);
		//assert (false and "not implemented");
		return memory::Undef::Create();
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

	void Evaluator::TraceCall(const llvm::Function* target, bool status) {
		if (status == true) {
			std::clog << TraceLevel() << "call " << target->getName().str() << std::endl;
			level_++;
		}
		else {
			level_--;
			std::clog << TraceLevel() << "back from " << target->getName().str() << std::endl;
		}
	}

	void Evaluator::TraceFunc(const llvm::Function* target) {
		std::clog << utils::ToString(*target) << std::endl;
	}

	std::string Evaluator::TraceLevel() {
		std::string res;
		for (int i = 0; i < level_; i++)
			res += "-";
		res += " ";
		return res;
	}

	memory::HolderPtr Evaluator::CallFunction(llvm::Function *f, memory::ArgMapPtr args) {
		// llvm::errs() << "call " << f->getName() << "\n";
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
				TraceCall(f, true);
				// initiate args
				for_each(args->begin(), args->end(), [&](auto pair){
					auto addr = pair.first;
					auto hldr = pair.second;
					// assign
					meta_eval_.Assign(addr, hldr);
				});

				const llvm::BasicBlock* next_block = &*f->begin();
				context_.Top()->PC.Set(next_block);
				TraceFunc(f);
				//TraceBlock(next_block);
				while (next_block != nullptr) {
					visit (const_cast<llvm::BasicBlock*>(next_block));
					next_block = context_.Top()->PC.Get();
				}
				ret_val = context_.Top()->RetVal.Get();
				TraceCall(f,false);
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

#define TRACE_BR

	void Evaluator::TraceBlock(const llvm::BasicBlock* next) {
#ifdef TRACE_BR
		if (next != nullptr)
			std::clog << utils::ToString(*next) << std::endl;
		else
			std::clog << "--end--" << std::endl;
#endif
	}

//#define TRACE_INST_NAMES
#define TRACE_TARGET_VAL

	void Evaluator::TraceAssign(const llvm::Instruction& inst, const llvm::Value* target) {
#ifdef TRACE_INST_NAMES
		std::clog << utils::ToString(inst) << std::endl;
#endif
#ifdef TRACE_TARGET_VAL
		if (llvm::isa<llvm::StoreInst>(inst))
			assert (target != nullptr);
		else
			(target = &inst);
		std::string target_full_name = utils::ToString(*target);
		HolderPtr holder = context_.Top()->Load(target);
		std::regex r(" = ");
		std::smatch r_match;
		if (std::regex_search(target_full_name, r_match, r)) {
			std::clog << TraceLevel() << r_match.prefix() << " <- " << *holder << std::endl;
		}
		else
			assert (false and "regex failed");
#endif
		//llvm::errs() << inst << "\n";
		//context_.Top()->Print();
		//context_.Solver().Print();
	}

	// Return
	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
		auto holder = context_.Top()->Load(ret_inst);
		meta_eval_.Assign(&inst, holder);
		context_.Top()->RetVal.Set(holder);
		context_.Top()->PC.Set(nullptr);
		//TraceAssign(inst, ret_inst);
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::ConstantInt *ret_const) {
		auto holder = ProduceHolder(ret_const);
		meta_eval_.Assign(&inst, holder);
		context_.Top()->RetVal.Set(holder);
		context_.Top()->PC.Set(nullptr);
		//TraceAssign(inst, ret_const);
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst) {
		auto undef = memory::Undef::Create();
		context_.Top()->RetVal.Set(undef);
		context_.Top()->PC.Set(nullptr);
		//TraceAssign(inst);
	}

	// Branch
	void Evaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		auto cond_holder = context_.Top()->Load(cond);
		assert (cond_holder != nullptr and "only instruction is supported yet");
		auto next = meta_eval_.Branch(&inst, cond_holder, iftrue, iffalse);
		context_.Top()->PC.Set(next);
		TraceBlock(next);
	}

	void Evaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {
		auto next = jump;
		context_.Top()->PC.Set(next);
		TraceBlock(next);
	}

	// BinOp
	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::ConstantInt *left, const llvm::Value *right) {
		auto left_holder = ProduceHolder(left);
		auto right_holder = context_.Top()->Load(right);
		meta_eval_.BinOp(&inst, left_holder, right_holder);
		TraceAssign(inst);
	}

	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = ProduceHolder(right);
		meta_eval_.BinOp(&inst, left_holder, right_holder);
		TraceAssign(inst);
	}

	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *left, const llvm::Value *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = context_.Top()->Load(right);
		meta_eval_.BinOp(&inst, left_holder, right_holder);
		TraceAssign(inst);
	}

	// Cmp
	void Evaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::ConstantInt *left, const llvm::Value *right) {
		auto left_holder = ProduceHolder(left);
		auto right_holder = context_.Top()->Load(right);
		meta_eval_.IntComparison(&inst, left_holder, right_holder);
		TraceAssign(inst);
	}

	void Evaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = ProduceHolder(right);

		meta_eval_.IntComparison(&inst, left_holder, right_holder);
		TraceAssign(inst);
	}

	void Evaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *left, const llvm::Value *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = context_.Top()->Load(right);

		meta_eval_.IntComparison(&inst, left_holder, right_holder);
		TraceAssign(inst);

	}

	// Alloca
	void Evaluator::HandleAllocaInst (const llvm::Instruction &inst, const llvm::ConstantInt *allocated) {
		auto holder = ProduceHolder(allocated);
		context_.Top()->Alloca(&inst, holder);
		TraceAssign(inst);
	}

	// Load
	void Evaluator::HandleLoadInst (const llvm::Instruction &inst, const llvm::Instruction *instruction) {
		auto holder = context_.Top()->Load(instruction);
		meta_eval_.Assign(&inst, holder);
		TraceAssign(inst);
	}

	// Store
	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *constant_int, const llvm::Value *ptr) {
		auto holder = ProduceHolder(constant_int);
		meta_eval_.Assign(ptr, holder);
		TraceAssign(inst, ptr);
	}

	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::Instruction *instruction, const llvm::Value *ptr) {
		auto holder = context_.Top()->Load(instruction);
		meta_eval_.Assign(ptr, holder);
		TraceAssign(inst, ptr);
	}

	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::Argument *arg, const llvm::Value *ptr) {
		auto holder = context_.Top()->Load(arg);
		meta_eval_.Assign(ptr, holder);
		TraceAssign(inst, ptr);
	}

	void Evaluator::HandleCallInst(const llvm::CallInst &inst) {
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

		memory::HolderPtr ret_holder = CallFunction(called, argmap);

		if (called->getReturnType()->isVoidTy()) {
			assert (utils::instanceof<Undef>(ret_holder));
		}
		else {
			assert (ret_holder != nullptr);
			meta_eval_.Assign(&inst, ret_holder);
		}
	}
}





















