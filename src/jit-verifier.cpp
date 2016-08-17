#include "jit-verifier.hpp"

namespace interpreter {
	using llvm::GenericValue;
	using memory::Concrete; using memory::ConcretePtr;
	using std::dynamic_pointer_cast;

	JITVerifier::JITVerifier(ContextRef context) : context_(context) {}
	JITVerifier::~JITVerifier() {}

	std::vector<llvm::GenericValue> JITVerifier::ProduceJITArgs(SolutionListPtr result_list) {
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

	bool JITVerifier::JIT(std::vector<GenericValue> jit_args, GenericValue expected) {
		//---------------------------------------------------------------------------
		// JIT:
		//exit(0);
		llvm::Module* module_ = nullptr;
		llvm::Function* target_ = nullptr;
		abort();
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
