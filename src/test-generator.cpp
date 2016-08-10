#include "test-generator.hpp"

namespace interpreter {
	using std::dynamic_pointer_cast;
	using memory::HolderPtr;
	using memory::Concrete; using memory::Symbolic;
	using memory::ConcretePtr; using memory::SymbolicPtr;
	using memory::IsConcrete; using memory::IsSymbolic;

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

	memory::ConcretePtr TestGenerator::HandleInteger(llvm::IntegerType* ty, memory::HolderPtr value) {

	}

	std::list<memory::ConcretePtr> TestGenerator::HandlePointer(llvm::PointerType* ty, memory::HolderPtr ptr) {

	}

	ConcretePtr HandleScalar(memory::HolderPtr holder) {

	}

	memory::ConcretePtr TestGenerator::HandleScalar(HolderPtr holder) {
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

	void TestGenerator::Do() {
		assert (ArgValidation(target_) == true and "argument types validation failed");
		auto args = target_->arg_begin();
		std::list<memory::ConcretePtr> arg_sol_list;
		memory::ConcretePtr ret_sol;
		if (context_.Solver().IsSat() == true) {
			for(auto pair = args_->begin(); pair != args_->end(); pair++) {
				HolderPtr holder = pair->second;
				auto ch = HandleScalar(holder);
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
		//exit(0);
		assert (JIT(arg_sol_list, ret_sol) and "JIT verification failed");
	}


	bool TestGenerator::JIT(std::list<memory::ConcretePtr> arg_sol_list, memory::ConcretePtr ret_sol) {
		//---------------------------------------------------------------------------
		// JIT:
		//exit(0);
		llvm::ExecutionEngine* jit = llvm::EngineBuilder(module_).create();
		std::vector<llvm::GenericValue> jit_args;
		llvm::GenericValue gres;
		for_each(arg_sol_list.begin(), arg_sol_list.end(), [&](auto arg_sol) {
			llvm::GenericValue gval;
			gval.IntVal = memory::GetValue(arg_sol);
			jit_args.push_back(gval);
		});
		// http://ktown.kde.org/~zrusin/main.cpp
		// http://stackoverflow.com/questions/19807875/how-to-convert-a-genericvalue-to-value-in-llvm
		gres = jit->runFunction(target_, jit_args);
		ConcretePtr jit_res = dynamic_pointer_cast<Concrete>(Concrete::Create(gres.IntVal));
		if (*ret_sol != *jit_res) {
			std::cerr << "// jit res: " << *jit_res << std::endl;
		}

		return (memory::GetValue(ret_sol) == gres.IntVal);
	}
}
