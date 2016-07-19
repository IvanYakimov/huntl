#include "built-in-impl.hpp"

namespace interpreter {
	using memory::HolderPtr;
	MkSym::MkSym(ContextRef context, unsigned size) : context_(context), size_(size) {}
	memory::HolderPtr MkSym::operator()(llvm::Function* f, memory::ArgMapPtr args) {
		//assert (args->empty() == true);
		return memory::Symbolic::Create(context_.Solver().MkVar(context_.Solver().MkBitVectorType(size_)));
	}

	Gen::Gen(ContextRef context, llvm::Function* target, llvm::Module* module) :
			context_(context), target_(target), module_(module) {}
	memory::HolderPtr Gen::operator()(llvm::Function* f, memory::ArgMapPtr args) {
		//TODO:
		//std::cerr << "with (" << args->size() << ") args:\n";
		std::list<memory::ConcretePtr> arg_sol_list;
		memory::ConcretePtr ret_sol;

		if (context_.Solver().IsSat() == true) {
			for(auto pair = args->begin(); pair != args->end(); pair++) {
				//std::cerr << *pair.second << "\n";
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
				if (std::next(pair,1) != args->end())
					arg_sol_list.push_back(ch);
				else
					ret_sol = ch;
			}
		}
		else
			assert (false and "not implemented");
		//std::cerr << "\n//----------------------------\nAUTOMATICALLY GENERATED TEST CASE FOR\n";
		std::cerr << "\n";
		std::cerr << target_->getName().str() << ":\t\t";
		for_each(arg_sol_list.begin(), arg_sol_list.end(), [&](auto arg_sol) {
			std::cerr << *arg_sol << " ";
		});

		std::cerr << " --> ";
		std::cerr << *ret_sol << "\n";

		//---------------------------------------------------------------------------
		// JIT:
		llvm::ExecutionEngine* jit = llvm::EngineBuilder(module_).create();
		std::vector<llvm::GenericValue> jit_args;

		for_each(arg_sol_list.begin(), arg_sol_list.end(), [&](auto arg_sol) {
			llvm::GenericValue gval;
			gval.IntVal = memory::GetValue(arg_sol);
			jit_args.push_back(gval);
		});

		llvm::GenericValue gres = jit->runFunction(target_, jit_args);

		//errs() << "\n//JIT verification - DONE. Result: " << gres.IntVal << "\n";

		assert(memory::GetValue(ret_sol) == gres.IntVal and "generated ret-value MUST be equivalent to one returned from JIT!");

		//std::cerr << "//END.\n//-----------------------------------\n\n";
		//context_.Top()->PC.Set(nullptr);
		//TODO: fix this bug:
		exit(0);
		//assert (false and "not implemented");
		return memory::Undef::Create();
	}
}
