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

	memory::ConcretePtr TestGenerator::ProduceScalar(HolderPtr holder) {
		ConcretePtr result = nullptr;
		if (memory::IsConcrete(holder)) {
			result = dynamic_pointer_cast<Concrete>(holder);
		} else if (memory::IsSymbolic(holder)) {
			solver::SharedExpr e = memory::GetExpr(holder);
			interpreter::MetaInt val = context_.Solver().GetValue(e);
			result = dynamic_pointer_cast<Concrete>(Concrete::Create(val));
		} else
			assert(false and "unexpected behavior");
		assert(result != nullptr and "cast failed");
		return result;
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

	SolutionPtr TestGenerator::HandleArg(Type* ty, HolderPtr holder) {
		if (ty->isIntegerTy()) {
			// leaf
			ConcretePtr res = ProduceScalar(holder);
			return std::make_shared<Scalar>(res);
		}
		else if (ty->isPointerTy() and ty->getContainedType(0)->isIntegerTy()) {
			// node
			// 1. Dereference pointer
			// 2. Create array from integers
		}
		else
			assert (! "bad");
	}

	SolutionList TestGenerator::ProduceArgSolutions(llvm::Function* func, ArgMapPtr arg_map) {
		SolutionList results;
		auto farg_iterator = func->arg_begin();
		auto argmap_iterator = arg_map->begin();
		// for all args of TARGET (not gen_TARGET) function
		while (farg_iterator != func->arg_end()) {
			Type* ty = farg_iterator->getType();
			HolderPtr holder = argmap_iterator->second;
			SolutionPtr res = HandleArg(ty, holder);
			assert (res != nullptr);
			results.push_back(res);
			argmap_iterator++;
			farg_iterator++;
		}
		assert (results.size() == arg_map->size() - 1);
		return results;
	}

	/*
	SolutionPtr TestGenerator::ProduceRetSolution(llvm::Function* func, ArgMapPtr arg_map) {
		llvm::Type* ret_ty = func->getReturnType();
		// the last item of gen_TARGET argument list references to the TARGET return value
		auto argmap_iterator = arg_map->rbegin();
		HolderPtr = argmap_iterator->second;
		SolutionPtr res = HandleArg(ret_ty, holder);
		assert (res != nullptr);
		return res;
	}
	*/

	void PrintResults(const llvm::Function* func, SolutionList results) {

	}

	void TestGenerator::Do() {
		assert (ArgValidation(target_) == true and "argument types validation failed");
		SolutionList arg_sols;
		SolutionPtr ret_sol;
		if (context_.Solver().IsSat() == true) {
			arg_sols = ProduceArgSolutions(target_, args_);
			//ret_sol = ProduceRetSolution(target_, args_);
			/*
			for(auto pair = args_->begin(); pair != args_->end(); pair++) {
				HolderPtr holder = pair->second;
				auto ch = HandleScalar(holder);
				if (std::next(pair,1) != args_->end())
					arg_sol_list.push_back(ch);
				else
					ret_sol = ch;
			}
			*/
		}
		else
			assert (false and "not implemented");

		std::cerr << "DONE.\n";
		abort();

		/*
		file_ << "\n";
		file_ << target_->getName().str() << ":\t";
		for_each(arg_sol_list.begin(), arg_sol_list.end(), [&](auto arg_sol) {
			file_ << *arg_sol << " ";
		});

		file_ << " ==> ";
		file_ << *ret_sol << "\n";
		*/

		//---------------------------------------------------------------------------
		// JIT:
		std::vector<GenericValue> jit_args = ProduceJITArgs(arg_sols);
		//assert (JIT(arg_sol_list, ret_sol) and "JIT verification failed");
	}

	std::vector<llvm::GenericValue> ProduceJITArgs(SolutionList result_list) {
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
