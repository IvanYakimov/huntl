#include "test-generator.hpp"

namespace interpreter {
	using std::dynamic_pointer_cast;
	using memory::HolderPtr;
	using memory::Concrete; using memory::Symbolic;
	using memory::ConcretePtr; using memory::SymbolicPtr;
	using memory::IsConcrete; using memory::IsSymbolic;
	using llvm::Type; using llvm::PointerType; using llvm::IntegerType;
	using llvm::Value;
	using memory::ArgMapPtr; using memory::ArgMap;
	using llvm::GenericValue;

	TestGenerator::TestGenerator(llvm::Module* module, llvm::Function* target, memory::ArgMapPtr args,
			ContextRef context, std::ostream& file) :
					module_(module),
					target_(target),
					args_(args),
					context_(context),
					file_(file) {
	}

	TestGenerator::~TestGenerator() {

	}

	bool ArgValidation(llvm::Function* func) {
		auto res = true;
		for (auto it = func->arg_begin(); it != func->arg_end(); it++) {
			auto ty = it->getType();
			if (ty->isIntegerTy())
				res = res and true;
			else if (ty->isPointerTy() and ty->getContainedType(0)->isIntegerTy())
				res = res and true;
			else
				res = res and false;
		}
		return res;
	}

	SolutionPtr TestGenerator::ProduceInteger(HolderPtr holder) {
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

	SolutionPtr TestGenerator::HandleArg(const Type* ty, HolderPtr holder) {
		if (ty->isIntegerTy()) {
			// this can be or integer const
			return ProduceInteger(holder);
			//or implicit array of integers
		}
		else if (ty->isPointerTy()) {
			assert (memory::IsConcrete(holder));
			// 1. Dereference the pointer
			MetaIntRef ptr_address_metaint = memory::GetValue(holder);
			memory::RamAddress ptr_target = ptr_address_metaint.getZExtValue();
			const llvm::Type* meta_type = context_.Ram().Stack().GetMetaType(ptr_target);
			if (meta_type->isArrayTy()) {
				const llvm::ArrayType* array_type = llvm::dyn_cast<llvm::ArrayType>(meta_type);
				ArrayPtr array = Array::Create();
				auto arr_size = array_type->getNumElements();
				for (int i = 0; i < arr_size; i++) {
					auto holder = context_.Ram().Stack().Read(ptr_target + i * memory::kDefAlign, memory::kDefAlign);
					SolutionPtr sol = ProduceInteger(holder);
					array->PushBack(sol);
				}
				return Pointer::Create(array);
				//std::cerr << "array size: " << array_type->getNumElements() << std::endl;
			}
			else if (meta_type->isIntegerTy() or meta_type->isPointerTy()){
				auto align = memory::kDefAlign;
				HolderPtr ptr_holder = context_.Ram().Stack().Read(ptr_target, align);
				// 2. Create result for the appropriate object
				const llvm::Type* addressed_ty = context_.Ram().Stack().GetType(ptr_target);

				return Pointer::Create(HandleArg(addressed_ty, ptr_holder));
				// node
			}
			else
				assert ("unexpected");
		}
		else
			assert (! "unexpected");
	}

	SolutionListPtr TestGenerator::ProduceArgSolutions(llvm::Function* func, ArgMapPtr arg_map) {
		SolutionListPtr results = utils::Create<SolutionList>();
		//SolutionList results;
		auto farg_iterator = func->arg_begin();
		auto argmap_iterator = arg_map->begin();
		// for all args of TARGET (not gen_TARGET) function
		while (farg_iterator != func->arg_end()) {
			Type* ty = farg_iterator->getType();
			HolderPtr holder = argmap_iterator->second;
			SolutionPtr res = HandleArg(ty, holder);
			assert (res != nullptr);
			results->push_back(res);
			argmap_iterator++;
			farg_iterator++;
		}
		assert (results->size() == arg_map->size() - 1);
		return results;
	}

	SolutionPtr TestGenerator::ProduceRetSolution(llvm::Function* func, ArgMapPtr arg_map) {
		// the last item of gen_TARGET argument list references to the TARGET return value
		llvm::Type* ret_ty = func->getReturnType();
		auto argmap_iterator = arg_map->rbegin();
		HolderPtr holder = argmap_iterator->second;
		return HandleArg(ret_ty, holder);
	}

	void TestGenerator::PrintSolution(SolutionPtr sol, std::ostream& file) {
		if (utils::instanceof<Integer>(sol)) {
			IntegerPtr integer = std::dynamic_pointer_cast<Integer>(sol);
			file << integer->Get();
		}
		else if (utils::instanceof<Pointer>(sol)) {
			PointerPtr pointer = std::dynamic_pointer_cast<Pointer>(sol);
			file << "*";
			PrintSolution(pointer->Dereference(), file);
			//assert (! "not impl");
		}
		else if (utils::instanceof<Array>(sol)) {
			ArrayPtr array = std::dynamic_pointer_cast<Array>(sol);
			file << "\'";
			for (int i = 0; i < array->GetSize(); i++) {
				SolutionPtr el_sol = array->GetElement(i);
				PrintSolution(el_sol, file);
			}
			file << "\'";
		}
		else
			assert (! "unexpected type of argument");
	}

	void TestGenerator::PrintFunctionInfo(llvm::Function* func, std::ostream& file) {
		file << func->getName().str() << ": ";
	}

	void TestGenerator::PrintSeparator(std::ostream& file) {
		file << " ";
	}

	void TestGenerator::PrintTransition(std::ostream& file) {
		file << " => ";
	}

	void TestGenerator::PrintEndl(std::ostream& file) {
		file << std::endl;
	}

	void TestGenerator::PrintWholeSolution(llvm::Function* func, SolutionListPtr arg_sols, SolutionPtr ret_sol, std::ostream& file) {
		assert (func != nullptr and arg_sols != nullptr and ret_sol != nullptr);
		assert (func->arg_size() == arg_sols->size());

		PrintFunctionInfo(func, file);
		auto it = arg_sols->begin();
		while (it != arg_sols->end()) {
			PrintSolution(*it, file);
			if (++it != arg_sols->end())
				PrintSeparator(file);
		}
		PrintTransition(file);
		PrintSolution(ret_sol, file);
		PrintEndl(file);
	}

	void TestGenerator::Do() {
		//assert (ArgValidation(target_) == true and "argument types validation failed");
		SolutionListPtr arg_sols;
		SolutionPtr ret_sol;
		if (context_.Solver().IsSat() == true) {
			arg_sols = ProduceArgSolutions(target_, args_);
			ret_sol = ProduceRetSolution(target_, args_);
		}
		else
			assert (false and "not implemented");

		PrintWholeSolution(target_, arg_sols, ret_sol, file_);

		exit(0);

		//---------------------------------------------------------------------------
		// JIT:
		std::vector<GenericValue> jit_args = ProduceJITArgs(arg_sols);
		//assert (JIT(arg_sol_list, ret_sol) and "JIT verification failed");
	}

	std::vector<llvm::GenericValue> ProduceJITArgs(SolutionListPtr result_list) {
		/*
		std::vector<llvm::GenericValue> jit_args;
		ResultList::iterator;
		llvm::GenericValue gres;
		for_each(arg_sol_list.begin(), arg_sol_list.end(), [&](auto arg_sol) {
			llvm::GenericValue gval;
			gval.IntVal = memory::GetValue(arg_sol);
			jit_args.push_back(gval);
		});
		*/
	}

	bool TestGenerator::JIT(std::vector<GenericValue> jit_args, GenericValue expected) {
		//---------------------------------------------------------------------------
		// JIT:
		//exit(0);
		llvm::ExecutionEngine* jit = llvm::EngineBuilder(module_).create();

		// http://ktown.kde.org/~zrusin/main.cpp
		// http://stackoverflow.com/questions/19807875/how-to-convert-a-genericvalue-to-value-in-llvm
		GenericValue gres;
		gres = jit->runFunction(target_, jit_args);
		ConcretePtr jit_res = dynamic_pointer_cast<Concrete>(Concrete::Create(gres.IntVal));
		if (gres.IntVal != expected.IntVal) {

			//llvm::errs() << "// jit res: " << gres.IntVal << std::endl;
		}

		return (expected.IntVal == gres.IntVal);
	}
}
