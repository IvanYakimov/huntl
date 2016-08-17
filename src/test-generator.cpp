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
					file_(file),
					jit_verifier_(context),
					sol_gen_(context){
	}

	TestGenerator::~TestGenerator() {

	}

	/*
	ArgMapPtr CloneArgMap(ArgMapPtr target) {
		ArgMapPtr fresh_map = utils::Create<ArgMap>();
		for (auto i = target->begin(); i != target->end(); ++i) {
			fresh_map->emplace(i->first, i->second);
		}
		assert (fresh_map->size() == target->size());
		return fresh_map;
	}
	*/

	//TODO: implement void function support
	void TestGenerator::Do() {
		SolutionListPtr arg_sols;
		SolutionPtr ret_sol;

		std::list<HolderPtr> target_args;
		auto begin = args_->begin();
		for (auto it = args_->begin(); it != args_->end(); ++it) {
			target_args.push_back(it->second);
		}
		//target_args.pop_back(); // remove last item - it is a ret value of target function!
		HolderPtr target_ret = target_args.back();
		target_args.pop_back(); // remove last item - it is a ret value of target function!
		//HolderPtr target_ret = args_->rbegin()->second;

		if (context_.Solver().IsSat() == true) {
			arg_sols = sol_gen_.ProduceArgSolutions(target_, target_args);
			ret_sol = sol_gen_.ProduceRetSolution(target_, target_ret);
		}
		else
			assert (false and "not implemented");

		PrintWholeSolution(target_, arg_sols, ret_sol, file_);

		exit(0);

		//---------------------------------------------------------------------------
		// JIT:
		std::vector<GenericValue> jit_args = jit_verifier_.ProduceJITArgs(arg_sols);
		//assert (JIT(arg_sol_list, ret_sol) and "JIT verification failed");
	}
}















