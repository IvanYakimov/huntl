#include "evaluator.hpp"

//TODO: refactoring:
//#include "llvm/IR/Instruction.h"
using namespace llvm;

namespace interpreter {
	using utils::Create;
	using memory::ArgMap;
	using memory::ArgMapPtr;
	using memory::HolderPtr;
	using memory::Undef;
	using utils::MetaKind;
	using llvm::Value;

	Evaluator::Evaluator(interpreter::ContextRef context) :
			context_(context),
			meta_eval_(context),
			tracer_(context) {
	}

	Evaluator::~Evaluator() {

	}

	void Evaluator::ProcessModule(llvm::Module *m) {
		//TODO: extract parsing code:
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
				}
			}
			else if (matched_test_NAMEs == 1) {
					test_functions.push_back(f_it);
			}
			else if (matched_gen_TARGETs == 1) {
				std::string target_name = gen_TARGET_matches.suffix();

				StringRef llvm_styled_target_name(target_name.c_str());
				llvm::Function* target = m->getFunction(llvm_styled_target_name);
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
				for (auto pair = args->begin(); pair != args->end(); pair++){
					auto variable = pair->first;
					auto hldr = pair->second;
					// assign
					auto location = context_.Top()->GetLocation(variable);
					meta_eval_.Assign(location, hldr);
					tracer_.Assign(*variable);
				}

				const llvm::BasicBlock* next_block = &*f->begin();
				context_.Top()->PC.Set(next_block);
				while (next_block != nullptr) {
					visit (const_cast<llvm::BasicBlock*>(next_block));
					next_block = context_.Top()->PC.Get();
				}

				ret_val = context_.Top()->RetVal.Get();
			}
			context_.Pop(); // pop
		}
		return ret_val;
	}

	HolderPtr Evaluator::ProduceHolder(const llvm::Value* target) {
		HolderPtr holder = nullptr;
		if (llvm::isa<llvm::ConstantInt>(target)) {
			const llvm::ConstantInt* target_const = llvm::dyn_cast<llvm::ConstantInt>(target);
			assert(target_const != nullptr);
			llvm::IntegerType* int_ty = target_const->getType();
			auto width = int_ty->getBitWidth();
			const llvm::APInt& val = target_const->getValue();
			holder = memory::Concrete::Create(val);
		}
		else {
			holder = context_.Top()->Load(target);
		}
		assert (holder != nullptr);
		return holder;
	}

	// Return
	void Evaluator::HandleReturnInst (const llvm::ReturnInst &inst, const llvm::Instruction *ret_inst) {
		//HolderPtr holder = context_.Top()->Load(ret_inst);
		HolderPtr holder = ProduceHolder(ret_inst);
		meta_eval_.Return(inst, holder);
	}

	void Evaluator::HandleReturnInst (const llvm::ReturnInst &inst, const llvm::ConstantInt *ret_const) {
		//HolderPtr holder = ProduceHolder(ret_const);
		HolderPtr holder = ProduceHolder(ret_const);
		meta_eval_.Return(inst, holder);
	}

	void Evaluator::HandleReturnInst (const llvm::ReturnInst &inst) {
		meta_eval_.Return(inst);
	}

	// Branch
	void Evaluator::HandleBranchInst (const llvm::BranchInst &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		//auto cond_holder = context_.Top()->Load(cond);
		HolderPtr cond_holder = ProduceHolder(cond);
		assert (cond_holder != nullptr and "only instruction is supported yet");
		auto next = meta_eval_.Branch(cond_holder, iftrue, iffalse);
		context_.Top()->PC.Set(next);
	}

	void Evaluator::HandleBranchInst (const llvm::BranchInst &inst, const llvm::BasicBlock *jump) {
		auto next = jump;
		context_.Top()->PC.Set(next);
	}

	// BinOp
	void Evaluator::HandleBinOp (const llvm::BinaryOperator &inst, const llvm::ConstantInt *left, const llvm::Value *right) {
		//auto left_holder = ProduceHolder(left);
		//auto right_holder = context_.Top()->Load(right);
		HolderPtr left_holder = ProduceHolder(left);
		HolderPtr right_holder = ProduceHolder(right);
		meta_eval_.BinOp(inst, left_holder, right_holder);
	}

	void Evaluator::HandleBinOp (const llvm::BinaryOperator &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		//auto left_holder = context_.Top()->Load(left);
		//auto right_holder = ProduceHolder(right);
		HolderPtr left_holder = ProduceHolder(left);
		HolderPtr right_holder = ProduceHolder(right);
		meta_eval_.BinOp(inst, left_holder, right_holder);
	}

	void Evaluator::HandleBinOp (const llvm::BinaryOperator &inst, const llvm::Value *left, const llvm::Value *right) {
		//auto left_holder = context_.Top()->Load(left);
		//auto right_holder = context_.Top()->Load(right);
		HolderPtr left_holder = ProduceHolder(left);
		HolderPtr right_holder = ProduceHolder(right);
		meta_eval_.BinOp(inst, left_holder, right_holder);
	}

	// Cmp
	void Evaluator::HandleICmpInst (const llvm::ICmpInst &inst, const llvm::ConstantInt *left, const llvm::Value *right) {
		//auto left_holder = ProduceHolder(left);
		//auto right_holder = context_.Top()->Load(right);
		HolderPtr left_holder = ProduceHolder(left);
		HolderPtr right_holder = ProduceHolder(right);
		meta_eval_.IntComparison(inst, left_holder, right_holder);
	}

	void Evaluator::HandleICmpInst (const llvm::ICmpInst &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		//auto left_holder = context_.Top()->Load(left);
		//auto right_holder = ProduceHolder(right);
		HolderPtr left_holder = ProduceHolder(left);
		HolderPtr right_holder = ProduceHolder(right);
		meta_eval_.IntComparison(inst, left_holder, right_holder);
	}

	void Evaluator::HandleICmpInst (const llvm::ICmpInst &inst, const llvm::Value *left, const llvm::Value *right) {
		//auto left_holder = context_.Top()->Load(left);
		//auto right_holder = context_.Top()->Load(right);
		HolderPtr left_holder = ProduceHolder(left);
		HolderPtr right_holder = ProduceHolder(right);
		meta_eval_.IntComparison(inst, left_holder, right_holder);
	}

	// Alloca
	void Evaluator::HandleAllocaInst (const llvm::AllocaInst &inst, const llvm::ConstantInt *allocated) {
		/*
		// note: variable is a pointer to the fresh allocated value
		// x = alloca:
		//
		// *x [0] = 4
		//  _ [4] = 1
		*/
		auto holder = ProduceHolder(allocated);
		meta_eval_.Alloca(inst, holder);
	}

	// Load
	void Evaluator::HandleLoadInst (const llvm::LoadInst &lhs, const llvm::Value *ptr) {
		/*
		// lhs = *rhs
		 */
		//auto ptr_holder = context_.Top()->Load(ptr);
		HolderPtr ptr_holder = ProduceHolder(ptr);
		meta_eval_.Load(lhs, ptr_holder);
	}

	// Store
	void Evaluator::HandleStoreInst (const llvm::StoreInst &inst, const llvm::ConstantInt *value, const llvm::Value *ptr) {
		/*
		// "store val *ptr" treated as follow: "*ptr = val"
		//
		// *ptr	[0] = 4
		//	_ 	[4] = 1		// initial allocated value = 1
		//
		// store val *ptr
		//
		// *ptr	[0] = 4
		//	_ 	[4] = val	// now ptr point to _, which is equivalent to val
		 */
		//auto value_holder = ProduceHolder(value);
		HolderPtr value_holder = ProduceHolder(value);
		//auto ptr_holder = context_.Top()->Load(ptr);
		HolderPtr ptr_holder = ProduceHolder(ptr);
		meta_eval_.Store(inst, value_holder, ptr_holder);
	}

	/*
	// https://blog.felixangell.com/an-introduction-to-llvm-in-go/
	/* see: http://llvm.org/docs/tutorial/OCamlLangImpl7.html
	 * In LLVM, all memory accesses are explicit with load/store instructions,
	 * and it is carefully designed not to have (or need) an “address-of” operator.
	 */
	void Evaluator::HandleStoreInst (const llvm::StoreInst &inst, const llvm::Value *value, const llvm::Value *ptr) {
		/*
		// *ptr = value
		 */
		//auto value_holder = context_.Top()->Load(value);
		HolderPtr value_holder = ProduceHolder(value);
		//auto ptr_holder = context_.Top()->Load(ptr);
		HolderPtr ptr_holder = ProduceHolder(ptr);
		meta_eval_.Store(inst, value_holder, ptr_holder);
	}

	// Trunc
	void Evaluator::HandleTruncInst (const llvm::TruncInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		//auto holder = context_.Top()->Load(target);
		HolderPtr holder = ProduceHolder(target);
		auto width = dest_ty->getBitWidth();
		auto lhs_address = context_.Top()->GetLocation(&inst);
		meta_eval_.Conversion(lhs_address, holder, MetaKind::Trunc, width);
	}

	// ZExt
	void Evaluator::HandleZExtInst (const llvm::ZExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		//auto holder = context_.Top()->Load(target);
		HolderPtr holder = ProduceHolder(target);
		auto width = dest_ty->getBitWidth();
		auto lhs_address = context_.Top()->GetLocation(&inst);
		meta_eval_.Conversion(lhs_address, holder, MetaKind::ZExt, width);
	}

	// SExt
	void Evaluator::HandleSExtInst (const llvm::SExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		//auto holder = context_.Top()->Load(target);
		HolderPtr holder = ProduceHolder(target);
		auto width = dest_ty->getBitWidth();
		auto lhs_address = context_.Top()->GetLocation(&inst);
		meta_eval_.Conversion(lhs_address, holder, MetaKind::SExt, width);
	}

	llvm::Function* ExtractCalledFunction(const llvm::CallInst& inst) {
		llvm::Function* called = inst.getCalledFunction();
		assert(called != nullptr and "invalid function call");
		return called;
	}

	void Evaluator::HandleCallInst(const llvm::CallInst &inst) {
		auto called = ExtractCalledFunction(inst);
		ArgMapPtr argmap = InitArgMap(inst);
		HolderPtr ret_holder = CallFunction(called, argmap);
		InitFuncRet(ret_holder, inst, called);
	}

	//----------------------------------------------------------------------------
	// Helpers

	memory::ArgMapPtr Evaluator::InitArgMap(const llvm::CallInst &inst) {
		memory::ArgMapPtr argmap = utils::Create<ArgMap>();
		auto called = ExtractCalledFunction(inst);
		auto args = called->arg_begin();
		for (auto i = 0; i != inst.getNumArgOperands(); i++) {
			auto operand = inst.getArgOperand(i);
			HolderPtr holder = ProduceHolder(operand);
			argmap->emplace(args, holder);
			args++;
		}
		assert (args == called->arg_end());
		return argmap;
	}

	void Evaluator::InitFuncRet(memory::HolderPtr ret_holder, const llvm::CallInst& inst, llvm::Function* called) {
		if (called->getReturnType()->isVoidTy()) {
			assert(utils::instanceof<Undef>(ret_holder));
		} else {
			assert(ret_holder != nullptr);
			auto lhs_address = context_.Top()->GetLocation(&inst);
			meta_eval_.Assign(lhs_address, ret_holder);
		}
	}
}





















