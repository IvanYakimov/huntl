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

	void TestGenerator::Do() {
		SolutionListPtr arg_sols;
		SolutionPtr ret_sol;
		if (context_.Solver().IsSat() == true) {
			arg_sols = sol_gen_.ProduceArgSolutions(target_, args_);
			//TODO: implement void function support
			ret_sol = sol_gen_.ProduceRetSolution(target_, args_);
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















