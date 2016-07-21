#include "test-generator.hpp"

namespace interpreter {
	using memory::HolderPtr;

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

	void TestGenerator::Do() {
		std::list<memory::ConcretePtr> arg_sol_list;
		memory::ConcretePtr ret_sol;
		if (context_.Solver().IsSat() == true) {
			for(auto pair = args_->begin(); pair != args_->end(); pair++) {
				HolderPtr holder = pair->second;
				if (memory::IsConcrete(holder)) {

				}
				else if (memory::IsSymbolic(holder)) {
					solver::SharedExpr e = memory::GetExpr(holder);
					interpreter::MetaInt val = context_.Solver().GetValue(e);
					holder = memory::Concrete::Create(val);
				}
				else
					assert (false and "unexpected behavior");

				auto ch = std::dynamic_pointer_cast<memory::Concrete>(holder);
				assert(ch != nullptr);
				if (std::next(pair,1) != args_->end())
					arg_sol_list.push_back(ch);
				else
					ret_sol = ch;
			}
		}
		else
			assert (false and "not implemented");
		file_ << "\n";
		file_ << target_->getName().str() << ":\t";
		for_each(arg_sol_list.begin(), arg_sol_list.end(), [&](auto arg_sol) {
			file_ << *arg_sol << " ";
		});

		file_ << " ==> ";
		file_ << *ret_sol << "\n";

		//---------------------------------------------------------------------------
		// JIT:
		llvm::ExecutionEngine* jit = llvm::EngineBuilder(module_).create();
		std::vector<llvm::GenericValue> jit_args;
		llvm::GenericValue gres;

		for_each(arg_sol_list.begin(), arg_sol_list.end(), [&](auto arg_sol) {
			llvm::GenericValue gval;
			gval.IntVal = memory::GetValue(arg_sol);
			jit_args.push_back(gval);
		});

		gres = jit->runFunction(target_, jit_args);

		assert(memory::GetValue(ret_sol) == gres.IntVal and "generated ret-value MUST be equivalent to one returned from JIT!");
	}
}
