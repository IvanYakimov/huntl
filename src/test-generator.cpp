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
					jit_verifier_(context)
					{
	}

	TestGenerator::~TestGenerator() {

	}

#include "options.hpp"

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
		SolutionGenerator sol_gen(context_, target_, target_args, target_ret);

		if (sol_gen.ProduceSolution()) {
			arg_sols = sol_gen.GetArgSolutions();
			ret_sol = sol_gen.GetRetSolution();
		}
		else
			assert (false and "the PC is unsatisfiable");

		ReadabilityOptimizer optimizer(context_, arg_sols, ret_sol);

		//optimizer.IntOptPass();
		#ifdef RESTRICTION_PASS
		optimizer.RestrictionPass();
		#ifdef CONCRETIZATION_PASS
		optimizer.ConcretizationPass();
		#endif
		#endif

		SolutionPrinter printer(context_, target_, arg_sols, ret_sol);
		printer(file_);

		exit(0);

		//---------------------------------------------------------------------------
		// JIT:
		//std::vector<GenericValue> jit_args = jit_verifier_.ProduceJITArgs(arg_sols);
		//assert (JIT(arg_sol_list, ret_sol) and "JIT verification failed");
	}
}















