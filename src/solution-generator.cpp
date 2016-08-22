#include "solution-generator.hpp"

namespace interpreter {
	using memory::HolderPtr; using memory::ArgMapPtr;
	using llvm::Type; using llvm::IntegerType; using llvm::PointerType; using llvm::ArrayType;
	using std::list;

	SolutionGenerator::SolutionGenerator(ContextRef context, llvm::Function* func, std::list<memory::HolderPtr>& arg_holders, memory::HolderPtr& ret_holder)
	: context_(context), func_(func),
	  arg_holders_(arg_holders), ret_holder_(ret_holder),
	  arg_sols_(nullptr), ret_sol_(nullptr) {
		assert (func_ != nullptr);
	}
	SolutionGenerator::~SolutionGenerator() {}

	IntegerPtr SolutionGenerator::ProduceInteger(HolderPtr holder) {
		SolutionPtr result = nullptr;
		if (memory::IsConcrete(holder)) {
			MetaIntRef val = memory::GetValue(holder);
			return Integer::Create(val);
		} else if (memory::IsSymbolic(holder)) {
			solver::SharedExpr e = memory::GetExpr(holder);
			interpreter::MetaIntRef val = context_.Solver().GetValue(e);
			return Integer::Create(val);
		} else
			assert(false and "unexpected behavior");
	}

	bool SolutionGenerator::ProduceSolution() {
		if (context_.Solver().IsSat()) {
			arg_sols_ = ProduceArgSolutions();
			ret_sol_ = ProduceRetSolution();
			return true;
		}
		else
			return false;
	}

	SolutionListPtr SolutionGenerator::GetArgSolutions() {
		assert (arg_sols_ != nullptr);
		return arg_sols_;
	}

	SolutionPtr SolutionGenerator::GetRetSolution() {
		assert (ret_sol_ != nullptr);
		return ret_sol_;
	}

	ArrayPtr SolutionGenerator::ProduceArrayOf(const llvm::ArrayType* array_type, memory::RamAddress base_address) {
		ArrayPtr array = Array::Create();
		auto arr_size = array_type->getNumElements();
		auto el_ty = array_type->getElementType();
		assert (el_ty->isIntegerTy());
		auto integer_el_ty = llvm::dyn_cast<llvm::IntegerType>(el_ty);
		auto width = integer_el_ty->getBitWidth();
		assert (width > 0 and width % 8 == 0);
		unsigned el_align = width / 8;
		for (int i = 0; i < arr_size; i++) {
			auto holder = context_.Ram().Stack().Read(base_address + i * el_align);
			SolutionPtr sol = ProduceInteger(holder);
			array->PushBack(sol);
		}
		return array;
	}

	PointerPtr SolutionGenerator::ProducePointerTo(memory::HolderPtr holder) {
		assert (memory::IsConcrete(holder));
		// 1. Dereference the pointer
		MetaIntRef ptr_address_metaint = memory::GetValue(holder);
		memory::RamAddress ptr_target = ptr_address_metaint.getZExtValue();
		const llvm::Type* meta_type = context_.Ram().Stack().GetMetaType(ptr_target);
		if (meta_type->isArrayTy()) {
			const llvm::ArrayType* array_type = llvm::dyn_cast<llvm::ArrayType>(meta_type);
			ArrayPtr array = ProduceArrayOf(array_type, ptr_target);
			assert (array != nullptr);
			return Pointer::Create(array);
		}
		else {
			HolderPtr dereferenced = context_.Ram().Stack().Read(ptr_target);
			if (meta_type->isIntegerTy()) {
				return Pointer::Create(ProduceInteger(dereferenced));
			}
			else if (meta_type->isPointerTy()) {
				return Pointer::Create(ProducePointerTo(dereferenced));
			}
			else
				assert (false and "unexpected type of pointer");
		}
	}

	SolutionPtr SolutionGenerator::HandleArg(const Type* ty, HolderPtr holder) {
		if (ty->isIntegerTy()) {
			return ProduceInteger(holder);
		}
		else if (ty->isPointerTy()) {
			return ProducePointerTo(holder);
		}
		else
			assert (false and "unexpected");
	}

	SolutionListPtr SolutionGenerator::ProduceArgSolutions() {
		SolutionListPtr results = utils::Create<SolutionList>();
		auto farg_iterator = func_->arg_begin();
		auto argmap_iterator = arg_holders_.begin();
		while (farg_iterator != func_->arg_end()) {
			Type* ty = farg_iterator->getType();
			HolderPtr holder = *argmap_iterator;
			SolutionPtr res = HandleArg(ty, holder);
			assert (res != nullptr);
			results->push_back(res);
			argmap_iterator++;
			farg_iterator++;
		}
		assert (results->size() == arg_holders_.size());
		return results;
	}

	SolutionPtr SolutionGenerator::ProduceRetSolution() {
		assert (ret_holder_ != nullptr);
		llvm::Type* ret_ty = func_->getReturnType();
		assert (not ret_ty->isVoidTy());
		return HandleArg(ret_ty, ret_holder_);
	}
}
