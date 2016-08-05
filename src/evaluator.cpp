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
				tracer_.Call(f, args, true);

				// alloca

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
				tracer_.Func(f);
				//tracer_.Block(next_block);
				//TODO: refactoring
				while (next_block != nullptr) {
					visit (const_cast<llvm::BasicBlock*>(next_block));
					next_block = context_.Top()->PC.Get();
				}
				ret_val = context_.Top()->RetVal.Get();
				tracer_.Call(f, args, false);
			}
			context_.Pop(); // pop
		}
		return ret_val;
	}

	auto Evaluator::ProduceHolder(const llvm::ConstantInt* allocated) {
		llvm::IntegerType* ty = allocated->getType();
		auto width = ty->getBitWidth();
		const llvm::APInt& val = allocated->getValue();
		auto holder = memory::Concrete::Create(val);
		return holder;
	}

	// Return
	void Evaluator::HandleReturnInst (const llvm::ReturnInst &inst, const llvm::Instruction *ret_inst) {
		HolderPtr holder = context_.Top()->Load(ret_inst);
		meta_eval_.Return(inst, holder);
		tracer_.Ret(ret_inst);
	}

	void Evaluator::HandleReturnInst (const llvm::ReturnInst &inst, const llvm::ConstantInt *ret_const) {
		HolderPtr holder = ProduceHolder(ret_const);
		meta_eval_.Return(inst, holder);
		tracer_.Ret(ret_const);
	}

	void Evaluator::HandleReturnInst (const llvm::ReturnInst &inst) {
		meta_eval_.Return(inst);
		tracer_.Ret();
	}

	// Branch
	void Evaluator::HandleBranchInst (const llvm::BranchInst &inst, const llvm::Value *cond, const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		auto cond_holder = context_.Top()->Load(cond);
		assert (cond_holder != nullptr and "only instruction is supported yet");
		auto next = meta_eval_.Branch(cond_holder, iftrue, iffalse);
		context_.Top()->PC.Set(next);
		tracer_.Block(next);
	}

	void Evaluator::HandleBranchInst (const llvm::BranchInst &inst, const llvm::BasicBlock *jump) {
		auto next = jump;
		context_.Top()->PC.Set(next);
		tracer_.Block(next);
	}

	// BinOp
	void Evaluator::HandleBinOp (const llvm::BinaryOperator &inst, const llvm::ConstantInt *left, const llvm::Value *right) {
		auto left_holder = ProduceHolder(left);
		auto right_holder = context_.Top()->Load(right);
		//auto lhs_address = context_.Top()->GetLocation(&inst);
		//auto bin_op = inst.getOpcode();
		//meta_eval_.BinOp(lhs_address, bin_op, left_holder, right_holder);
		meta_eval_.BinOp(inst, left_holder, right_holder);
		tracer_.Assign(inst);
	}

	void Evaluator::HandleBinOp (const llvm::BinaryOperator &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = ProduceHolder(right);
		//auto lhs_address = context_.Top()->GetLocation(&inst);
		//auto bin_op = inst.getOpcode();
		//meta_eval_.BinOp(lhs_address, bin_op, left_holder, right_holder);
		meta_eval_.BinOp(inst, left_holder, right_holder);
		tracer_.Assign(inst);
	}

	void Evaluator::HandleBinOp (const llvm::BinaryOperator &inst, const llvm::Value *left, const llvm::Value *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = context_.Top()->Load(right);
		//auto lhs_address = context_.Top()->GetLocation(&inst);
		//auto op_code = inst.getOpcode();
		//meta_eval_.BinOp(lhs_address, op_code, left_holder, right_holder);
		meta_eval_.BinOp(inst, left_holder, right_holder);
		tracer_.Assign(inst);
	}

	// Cmp
	void Evaluator::HandleICmpInst (const llvm::ICmpInst &inst, const llvm::ConstantInt *left, const llvm::Value *right) {
		auto left_holder = ProduceHolder(left);
		auto right_holder = context_.Top()->Load(right);
		auto lhs_address = context_.Top()->GetLocation(&inst);
		auto predicate = inst.getPredicate();
		meta_eval_.IntComparison(lhs_address, predicate, left_holder, right_holder);
		tracer_.Assign(inst);
	}

	void Evaluator::HandleICmpInst (const llvm::ICmpInst &inst, const llvm::Value *left, const llvm::ConstantInt *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = ProduceHolder(right);
		auto predicate = inst.getPredicate();
		auto lhs_address = context_.Top()->GetLocation(&inst);
		meta_eval_.IntComparison(lhs_address, predicate, left_holder, right_holder);
		tracer_.Assign(inst);
	}

	void Evaluator::HandleICmpInst (const llvm::ICmpInst &inst, const llvm::Value *left, const llvm::Value *right) {
		auto left_holder = context_.Top()->Load(left);
		auto right_holder = context_.Top()->Load(right);
		auto lhs_address = context_.Top()->GetLocation(&inst);
		auto predicate = inst.getPredicate();
		meta_eval_.IntComparison(lhs_address, predicate, left_holder, right_holder);
		tracer_.Assign(inst);

	}

	// Alloca
	void Evaluator::HandleAllocaInst (const llvm::AllocaInst &inst, const llvm::ConstantInt *allocated) {
		// variable is a pointer to the fresh allocated value
		// x = alloca:
		//
		// *x [0] = 4
		//  _ [4] = 1
		//

		auto holder = ProduceHolder(allocated);
		auto lhs_address = context_.Top()->GetLocation(&inst);
		auto target_address = context_.Top()->Alloca(holder);
		auto target_address_holder = memory::Concrete::Create(interpreter::MetaInt(memory::Ram::machine_word_bitsize_, target_address));
		meta_eval_.Assign(lhs_address, target_address_holder);
		tracer_.Assign(inst);
		//std::clog << "alloca [" << target_address << "] <- " << *holder << std::endl;
	}

	// Load
	void Evaluator::HandleLoadInst (const llvm::LoadInst &lhs, const llvm::Value *rhs) {
		// lhs = *rhs
		auto rhs_holder = context_.Top()->Load(rhs);
		// dereferencing START
		assert (memory::IsConcrete(rhs_holder));
		MetaIntRef rhs_holder_value = memory::GetValue(rhs_holder);
		memory::RamAddress target_address = rhs_holder_value.getZExtValue();
		auto target_holder = context_.Ram().Stack().Read(target_address, memory::Ram::def_align_);
		// dereferencing END
		auto lhs_address = context_.Top()->GetLocation(&lhs);
		//meta_eval_.Assign(lhs_address, rhs_holder);
		meta_eval_.Assign(lhs_address, target_holder);
		//std::clog << "[" << lhs_address << "]" << " <- " << *target_holder << std::endl;
		//tracer_.Assign(lhs);
	}

	// Store
	void Evaluator::HandleStoreInst (const llvm::StoreInst &inst, const llvm::ConstantInt *c1, const llvm::Value *x_ptr) {
		// store c1 *x 	treated as follow:	*x = c1
		//
		// *x [0] = 4
		//	_ [4] = 1
		//
		// store c1 *x
		//
		// *x [0] = 4
		//	_ [4] = c1

		auto c1_holder = ProduceHolder(c1);
		//auto lhs_address = context_.Top()->GetLocation(lhs);
		// dereferencing START
		auto x_ptr_holder = context_.Top()->Load(x_ptr);
		assert (memory::IsConcrete(x_ptr_holder));
		MetaIntRef x_ptr_concrete_value = memory::GetValue(x_ptr_holder);
		memory::RamAddress unnamed_memory_cell = x_ptr_concrete_value.getZExtValue();
		// dereferencing END
		meta_eval_.Assign(unnamed_memory_cell, c1_holder);

		//std::clog << "[" << unnamed_memory_cell << "]" << " <- " << *c1_holder << std::endl;

		//meta_eval_.Assign(lhs_address, holder);
		//tracer_.Assign(*x_ptr);
	}

	// https://blog.felixangell.com/an-introduction-to-llvm-in-go/
	/* see: http://llvm.org/docs/tutorial/OCamlLangImpl7.html
	 * In LLVM, all memory accesses are explicit with load/store instructions,
	 * and it is carefully designed not to have (or need) an “address-of” operator.
	 */

	void Evaluator::HandleStoreInst (const llvm::StoreInst &inst, const llvm::Value *rhs, const llvm::Value *x_ptr) {
		// *x = rhs
		auto rhs_holder = context_.Top()->Load(rhs);
		// dereferencing START
		auto x_ptr_holder = context_.Top()->Load(x_ptr);
		assert (memory::IsConcrete(x_ptr_holder));
		MetaIntRef x_ptr_concrete_value = memory::GetValue(x_ptr_holder);
		memory::RamAddress unnamed_memory_cell = x_ptr_concrete_value.getZExtValue();
		// dereferencing END
		meta_eval_.Assign(unnamed_memory_cell, rhs_holder);

		//std::clog << "[" << unnamed_memory_cell << "]" << " <- " << *rhs_holder << std::endl;
	}

	// Trunc
	void Evaluator::HandleTruncInst (const llvm::TruncInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		auto holder = context_.Top()->Load(target);
		auto width = dest_ty->getBitWidth();
		auto lhs_address = context_.Top()->GetLocation(&inst);
		meta_eval_.Conversion(lhs_address, holder, MetaKind::Trunc, width);
	}

	// ZExt
	void Evaluator::HandleZExtInst (const llvm::ZExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		auto holder = context_.Top()->Load(target);
		auto width = dest_ty->getBitWidth();
		auto lhs_address = context_.Top()->GetLocation(&inst);
		meta_eval_.Conversion(lhs_address, holder, MetaKind::ZExt, width);
	}

	// SExt
	void Evaluator::HandleSExtInst (const llvm::SExtInst &inst, const llvm::Value* target, const llvm::IntegerType* dest_ty) {
		auto holder = context_.Top()->Load(target);
		auto width = dest_ty->getBitWidth();
		auto lhs_address = context_.Top()->GetLocation(&inst);
		meta_eval_.Conversion(lhs_address, holder, MetaKind::SExt, width);
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
			else
				holder = context_.Top()->Load(operand);

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
			auto lhs_address = context_.Top()->GetLocation(&inst);
			meta_eval_.Assign(lhs_address, ret_holder);
		}
	}
}





















