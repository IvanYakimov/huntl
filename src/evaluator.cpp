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

			std::regex str_TEXT_regex("str_");
			std::smatch str_TEXT_matches;
			auto matched_str_TEXTs = std::regex_search(name, str_TEXT_matches, str_TEXT_regex);

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
			else if (matched_str_TEXTs == 1) {

			}
			else {
				//this is ordinary function
			}
		}

		EvaluateFunctionList(test_functions);
	}

	memory::HolderPtr Evaluator::CallFunction(llvm::Function *f, memory::ArgMapPtr arg_map) {
		memory::HolderPtr ret_val = nullptr;
		auto it = builtins_.find(f);
		if (it != builtins_.end()) {
			context_.Push(); {
				ret_val = it->second(f, arg_map);
			}
			context_.Pop();
		}
		else {
			context_.Push(); {
				AssignTopFunctionArgs(arg_map);
				EvaluateTopFunction(f);
				ret_val = context_.Top()->RetVal.Get();
			}
			context_.Pop();
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
	void Evaluator::HandleReturnInst (const llvm::ReturnInst &inst, const llvm::Value *ret_inst) {
		HolderPtr holder = ProduceHolder(ret_inst);
		meta_eval_.Return(inst, holder);
	}

	void Evaluator::HandleReturnInst (const llvm::ReturnInst &inst) {
		meta_eval_.Return(inst);
	}

	// Branch
	void Evaluator::HandleBranchInst (const llvm::BranchInst &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
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
	void Evaluator::HandleBinOp (const llvm::BinaryOperator &inst, const llvm::Value *left, const llvm::Value *right) {
		HolderPtr left_holder = ProduceHolder(left);
		HolderPtr right_holder = ProduceHolder(right);
		meta_eval_.BinOp(inst, left_holder, right_holder);
	}

	// Cmp
	void Evaluator::HandleICmpInst (const llvm::ICmpInst &inst, const llvm::Value *left, const llvm::Value *right) {
		HolderPtr left_holder = ProduceHolder(left);
		HolderPtr right_holder = ProduceHolder(right);
		meta_eval_.IntComparison(inst, left_holder, right_holder);
	}

	// Alloca
	void Evaluator::HandleAllocaInst (const llvm::AllocaInst &inst, const llvm::ConstantInt *allocated, const llvm::Type* allocated_type) {
		//auto holder = ProduceHolder(allocated);
		//meta_eval_.Alloca(inst, holder);
		meta_eval_.Alloca(inst, allocated_type);
	}

	// Load
	void Evaluator::HandleLoadInst (const llvm::LoadInst &lhs, const llvm::Value *ptr) {
		HolderPtr ptr_holder = ProduceHolder(ptr);
		meta_eval_.Load(lhs, ptr_holder);
	}

	// Store
	void Evaluator::HandleStoreInst (const llvm::StoreInst &inst, const llvm::Value *value, const llvm::Value *ptr) {
		HolderPtr value_holder = ProduceHolder(value);
		HolderPtr ptr_holder = ProduceHolder(ptr);
		meta_eval_.Store(inst, value_holder, ptr_holder);
	}

	void Evaluator::HandleGetElementPtr (const llvm::GetElementPtrInst& inst, const llvm::Value *target, const llvm::ConstantInt *start_from, const llvm::ConstantInt *index) {
		HolderPtr target_holder = ProduceHolder(target);
		HolderPtr base_holder = ProduceHolder(start_from);
		HolderPtr idx_holder = ProduceHolder(index);
		if (inst.isInBounds()) {
			Type* ty = target->getType();
			if (ty->isPointerTy() and ty->getContainedType(0)->isArrayTy()) {
				ArrayType* arr_ty = llvm::dyn_cast<ArrayType>(ty->getContainedType(0));
				meta_eval_.GetElementPtr(inst, arr_ty, target_holder, base_holder, idx_holder);
			}
			else
				assert (! "only ptr to array supported");

		}
		else
			assert (! "unbound access not implemented");
	}

	// Trunc
	void Evaluator::HandleTruncInst (const llvm::TruncInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		HolderPtr holder = ProduceHolder(target);
		auto width = dest_ty->getBitWidth();
		auto lhs_address = context_.Top()->GetLocation(&inst);
		meta_eval_.Conversion(lhs_address, holder, MetaKind::Trunc, width);
	}

	// ZExt
	void Evaluator::HandleZExtInst (const llvm::ZExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		HolderPtr holder = ProduceHolder(target);
		auto width = dest_ty->getBitWidth();
		auto lhs_address = context_.Top()->GetLocation(&inst);
		meta_eval_.Conversion(lhs_address, holder, MetaKind::ZExt, width);
	}

	// SExt
	void Evaluator::HandleSExtInst (const llvm::SExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		HolderPtr holder = ProduceHolder(target);
		auto width = dest_ty->getBitWidth();
		auto lhs_address = context_.Top()->GetLocation(&inst);
		meta_eval_.Conversion(lhs_address, holder, MetaKind::SExt, width);
	}

	// PtrToInt
	void Evaluator::HandlePtrToInt (const llvm::PtrToIntInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		HolderPtr holder = ProduceHolder(target);
		assert (memory::IsConcrete(holder));
		auto to_width = dest_ty->getBitWidth();
		auto from_width = memory::Ram::machine_word_bitsize_;
		auto lhs_address = context_.Top()->GetLocation(&inst);
		if (to_width < from_width)
			meta_eval_.Conversion(lhs_address, holder, MetaKind::Trunc, to_width);
		else if (to_width > from_width)
			meta_eval_.Conversion(lhs_address, holder, MetaKind::SExt, to_width);
		else
			meta_eval_.Assign(lhs_address, holder);
	}

	// IntToPtr
	void Evaluator::HandleIntToPtr (const llvm::IntToPtrInst &inst, const llvm::Value* target, const llvm::PointerType* dest_ty) {
		HolderPtr holder = ProduceHolder(target);
		assert (memory::IsConcrete(holder));
		llvm::Type* target_ty = target->getType();
		llvm::IntegerType* int_target_ty = llvm::dyn_cast<IntegerType>(target_ty);
		auto from_width = int_target_ty->getBitWidth();
		auto to_width = memory::Ram::machine_word_bitsize_;
		auto lhs_address = context_.Top()->GetLocation(&inst);
		if (to_width < from_width)
			meta_eval_.Conversion(lhs_address, holder, MetaKind::Trunc, to_width);
		else if (to_width > from_width)
			meta_eval_.Conversion(lhs_address, holder, MetaKind::SExt, to_width);
		else
			meta_eval_.Assign(lhs_address, holder);
	}

	llvm::Function* ExtractCalledFunction(const llvm::CallInst& inst) {
		llvm::Function* called = inst.getCalledFunction();
		assert(called != nullptr and "invalid function call");
		return called;
	}

	void Evaluator::HandleCallInst(const llvm::CallInst &inst) {
		auto called = ExtractCalledFunction(inst);
		ArgMapPtr argmap = ProduceArgMap(inst);
		HolderPtr ret_holder = CallFunction(called, argmap);
		AssignCallResult(inst, ret_holder);
	}

	//----------------------------------------------------------------------------
	// Helpers

	memory::ArgMapPtr Evaluator::ProduceArgMap(const llvm::CallInst &inst) {
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

	void Evaluator::EvaluateFunctionList(std::list<llvm::Function*> test_functions) {
		pid_t child_pid = 0;
		int ch_status = 0;
		for (auto it = test_functions.begin(); it != test_functions.end(); it++) {
			errs().flush();
			std::flush(std::cerr);
			child_pid = fork();
			if (child_pid > 0) {
				wait(&ch_status);
			} else {
				auto args = utils::Create<interpreter::ArgMap>();
				auto ret = CallFunction(*it, args);
			}
		}
	}

	void Evaluator::EvaluateTopFunction(llvm::Function* f) {
		const llvm::BasicBlock* next_block = &*f->begin();
		context_.Top()->PC.Set(next_block);
		while (next_block != nullptr) {
			visit(const_cast<llvm::BasicBlock*>(next_block));
			next_block = context_.Top()->PC.Get();
		}
	}


	void Evaluator::AssignTopFunctionArgs(ArgMapPtr args) {
		for (auto pair = args->begin(); pair != args->end(); pair++){
			auto variable = pair->first;
			auto hldr = pair->second;
			// assign
			auto location = context_.Top()->GetLocation(variable);
			meta_eval_.Assign(location, hldr);
			tracer_.Assign(*variable);
		}
	}

	void Evaluator::AssignCallResult(const llvm::CallInst& inst, memory::HolderPtr ret_holder) {
		auto called = ExtractCalledFunction(inst);
		if (called->getReturnType()->isVoidTy()) {
			assert(utils::instanceof<Undef>(ret_holder));
		} else {
			assert(ret_holder != nullptr);
			auto lhs_address = context_.Top()->GetLocation(&inst);
			meta_eval_.Assign(lhs_address, ret_holder);
		}
	}
}





















