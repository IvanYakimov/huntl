#include "solution-generator.hpp"

namespace interpreter {
	using memory::HolderPtr; using memory::ArgMapPtr;
	using llvm::Type; using llvm::IntegerType; using llvm::PointerType; using llvm::ArrayType;
	using std::list;

	SolutionGenerator::SolutionGenerator(ContextRef context) : context_(context) {}
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

	PointerPtr SolutionGenerator::ProducePointerTo(memory::HolderPtr holder) {
		assert (memory::IsConcrete(holder));
		// 1. Dereference the pointer
		MetaIntRef ptr_address_metaint = memory::GetValue(holder);
		memory::RamAddress ptr_target = ptr_address_metaint.getZExtValue();
		const llvm::Type* meta_type = context_.Ram().Stack().GetMetaType(ptr_target);
		if (meta_type->isArrayTy()) {
			const llvm::ArrayType* array_type = llvm::dyn_cast<llvm::ArrayType>(meta_type);
			ArrayPtr array = Array::Create();
			auto arr_size = array_type->getNumElements();
			auto el_ty = array_type->getElementType();
			assert (el_ty->isIntegerTy());
			auto integer_el_ty = llvm::dyn_cast<llvm::IntegerType>(el_ty);
			auto width = integer_el_ty->getBitWidth();
			assert (width > 0 and width % 8 == 0);
			unsigned el_align = width / 8;
			for (int i = 0; i < arr_size; i++) {
				auto holder = context_.Ram().Stack().Read(ptr_target + i * el_align);
				SolutionPtr sol = ProduceInteger(holder);
				array->PushBack(sol);
			}
			return Pointer::Create(array);
			//std::cerr << "array size: " << array_type->getNumElements() << std::endl;
		}
		else if (meta_type->isIntegerTy() or meta_type->isPointerTy()) {
			HolderPtr ptr_holder = context_.Ram().Stack().Read(ptr_target);
			// 2. Create result for the appropriate object
			const llvm::Type* addressed_ty = context_.Ram().Stack().GetType(ptr_target);

			return Pointer::Create(HandleArg(addressed_ty, ptr_holder));
			// node
		}
		else
			assert ("unexpected");
	}

	SolutionPtr SolutionGenerator::HandleArg(const Type* ty, HolderPtr holder) {
		if (ty->isIntegerTy()) {
			return ProduceInteger(holder);
		}
		else if (ty->isPointerTy()) {
			return ProducePointerTo(holder);
		}
		else
			assert (! "unexpected");
	}

	SolutionListPtr SolutionGenerator::ProduceArgSolutions(llvm::Function* func, list<HolderPtr>& arg_map) {
		SolutionListPtr results = utils::Create<SolutionList>();
		//SolutionList results;
		auto farg_iterator = func->arg_begin();
		auto argmap_iterator = arg_map.begin();
		// for all args of TARGET (not gen_TARGET) function
		while (farg_iterator != func->arg_end()) {
			Type* ty = farg_iterator->getType();
			//HolderPtr holder = argmap_iterator->second;
			HolderPtr holder = *argmap_iterator;
			SolutionPtr res = HandleArg(ty, holder);
			assert (res != nullptr);
			results->push_back(res);
			argmap_iterator++;
			farg_iterator++;
		}
		//assert (results->size() == arg_map->size() - 1);
		assert (results->size() == arg_map.size());
		return results;
	}

	SolutionPtr SolutionGenerator::ProduceRetSolution(llvm::Function* func, HolderPtr holder) {
		assert (holder != nullptr);
		// the last item of gen_TARGET argument list references to the TARGET return value
		llvm::Type* ret_ty = func->getReturnType();
		assert (not ret_ty->isVoidTy());
		//auto argmap_iterator = arg_map->rbegin();
		//HolderPtr holder = argmap_iterator->second;
		return HandleArg(ret_ty, holder);
	}
}
