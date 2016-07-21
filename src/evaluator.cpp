#include "evaluator.hpp"

//TODO: refactoring:
//#include "llvm/IR/Instruction.h"
using namespace llvm;

namespace interpreter {
	using utils::Create;
	using memory::ArgMap;
	using memory::HolderPtr;
	using memory::Undef;
	using utils::MetaKind;

	Evaluator::Evaluator(interpreter::ContextRef context) :
			context_(context),
			meta_eval_(context),
			tracer_(context) {
	}

	Evaluator::~Evaluator() {

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
				tracer_.Call(f, true);
				// initiate args
				for_each(args->begin(), args->end(), [&](auto pair){
					auto addr = pair.first;
					auto hldr = pair.second;
					// assign
					meta_eval_.Assign(addr, hldr);
				});

				const llvm::BasicBlock* next_block = &*f->begin();
				context_.Top()->PC.Set(next_block);
				tracer_.Func(f);
				//tracer_.Block(next_block);
				//TODO: refactoring
				while (next_block != nullptr) {
					visit (const_cast<llvm::BasicBlock*>(next_block));
					next_block = context_.Top()->PC.Get();
				}
				ret_val = context_.Top()->RetVal.Get();
				tracer_.Call(f,false);
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

	// Return
	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::Instruction *ret_inst) {
		auto holder = context_.Top()->Load(ret_inst);
		meta_eval_.Assign(&inst, holder);
		context_.Top()->RetVal.Set(holder);
		context_.Top()->PC.Set(nullptr);
		tracer_.Ret(ret_inst);
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst, const llvm::ConstantInt *ret_const) {
		auto holder = ProduceHolder(ret_const);
		meta_eval_.Assign(&inst, holder);
		context_.Top()->RetVal.Set(holder);
		context_.Top()->PC.Set(nullptr);
		tracer_.Ret(ret_const);
	}

	void Evaluator::HandleReturnInst (const llvm::Instruction &inst) {
		auto undef = memory::Undef::Create();
		context_.Top()->RetVal.Set(undef);
		context_.Top()->PC.Set(nullptr);
		tracer_.Ret();
	}

	// Branch
	void Evaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		auto cond_holder = context_.Top()->Load(cond);
		assert (cond_holder != nullptr and "only instruction is supported yet");
		auto next = meta_eval_.Branch(&inst, cond_holder, iftrue, iffalse);
		context_.Top()->PC.Set(next);
		tracer_.Block(next);
	}

	void Evaluator::HandleBranchInst (const llvm::Instruction &inst, const llvm::BasicBlock *jump) {
		auto next = jump;
		context_.Top()->PC.Set(next);
		tracer_.Block(next);
	}

	// BinOp
	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::ConstantInt *left, const llvm::Value *right) {
		auto left_holder = ProduceHolder(left);
		auto right_holder = context_.Top()->Load(right);
		meta_eval_.BinOp(&inst, left_holder, right_holder);
		tracer_.Assign(inst);
	}

	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = ProduceHolder(right);
		meta_eval_.BinOp(&inst, left_holder, right_holder);
		tracer_.Assign(inst);
	}

	void Evaluator::HandleBinOp (const llvm::Instruction &inst, const llvm::Value *left, const llvm::Value *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = context_.Top()->Load(right);
		meta_eval_.BinOp(&inst, left_holder, right_holder);
		tracer_.Assign(inst);
	}

	// Cmp
	void Evaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::ConstantInt *left, const llvm::Value *right) {
		auto left_holder = ProduceHolder(left);
		auto right_holder = context_.Top()->Load(right);
		meta_eval_.IntComparison(&inst, left_holder, right_holder);
		tracer_.Assign(inst);
	}

	void Evaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = ProduceHolder(right);

		meta_eval_.IntComparison(&inst, left_holder, right_holder);
		tracer_.Assign(inst);
	}

	void Evaluator::HandleICmpInst (const llvm::Instruction &inst, const llvm::Value *left, const llvm::Value *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = context_.Top()->Load(right);

		meta_eval_.IntComparison(&inst, left_holder, right_holder);
		tracer_.Assign(inst);

	}

	// Alloca
	void Evaluator::HandleAllocaInst (const llvm::Instruction &inst, const llvm::ConstantInt *allocated) {
		auto holder = ProduceHolder(allocated);
		context_.Top()->Alloca(&inst, holder);
		tracer_.Assign(inst);
	}

	// see: http://stackoverflow.com/questions/12879673/check-pointer-to-pointer-type-in-llvm
	bool Evaluator::IsPointerToPointer(const Value* V) {
	    const Type* ty = V->getType();
	    if (ty->isPointerTy() && ty->getContainedType(0)->isPointerTy())
	    	return true;
	    else
	    	return false;
	}

	bool Evaluator::IsDereferencing(const llvm::Instruction& load_inst, const llvm::Value* ptr) {
		return IsPointerToPointer(ptr);
	}

	bool Evaluator::IsAddressing(const llvm::Instruction& store_inst, const llvm::Value* ptr) {
		return IsPointerToPointer(ptr);
	}

	// Load
	void Evaluator::HandleLoadInst (const llvm::Instruction &lhs, const llvm::Value *rhs) {
		if (IsDereferencing(lhs, rhs)) {
			auto ptr_holder = context_.Top()->Load(rhs);
			meta_eval_.Dereferencing(&lhs, ptr_holder);
		}
		else {
			auto rhs_holder = context_.Top()->Load(rhs);
			meta_eval_.Assign(&lhs, rhs_holder);
		}
		tracer_.Assign(lhs);
	}

	// Store
	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::ConstantInt *rhs, const llvm::Value *lhs) {
		if (IsAddressing(inst, lhs)) {
			assert (false and "unexpected addressing operation (casting)");
		}
		else {
			auto holder = ProduceHolder(rhs);
			meta_eval_.Assign(lhs, holder);
		}
		tracer_.Assign(*lhs);
	}

	void Evaluator::HandleStoreInst (const llvm::Instruction &inst, const llvm::Value *rhs, const llvm::Value *lhs) {
		if (IsAddressing(inst, lhs)) {
			memory::RamAddress address = context_.Top()->AddressOf(rhs);
			auto address_holder = memory::Concrete::Create(MetaInt(memory::Ram::machine_word_bitsize_, address));
			meta_eval_.Addressing(lhs, address_holder);
		}
		else {
			auto holder = context_.Top()->Load(rhs);
			meta_eval_.Assign(lhs, holder);
		}
		tracer_.Assign(*lhs);
	}

	// Trunc
	void Evaluator::HandleTruncInst (const llvm::TruncInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		auto holder = context_.Top()->Load(target);
		auto width = dest_ty->getBitWidth();
		meta_eval_.Conversion(&inst, holder, MetaKind::Trunc, width);
	}

	// ZExt
	void Evaluator::HandleZExtInst (const llvm::ZExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		auto holder = context_.Top()->Load(target);
		auto width = dest_ty->getBitWidth();
		meta_eval_.Conversion(&inst, holder, MetaKind::ZExt, width);
	}

	// SExt
	void Evaluator::HandleSExtInst (const llvm::SExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		auto holder = context_.Top()->Load(target);
		auto width = dest_ty->getBitWidth();
		meta_eval_.Conversion(&inst, holder, MetaKind::Trunc, width);
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





















