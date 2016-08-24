#include "readability-optimizer.hpp"

namespace interpreter {
	ReadabilityOptimizer::ReadabilityOptimizer(ContextRef context, SolutionListPtr arg_sols, SolutionPtr ret_sol) :
		context_(context), arg_sols_(arg_sols), ret_sol_(ret_sol) {
	}

	ReadabilityOptimizer::~ReadabilityOptimizer() {

	}

	void ReadabilityOptimizer::RestrictionHelper(SolutionPtr sol) {
		if (utils::instanceof<Integer>(sol)) {
			IntegerPtr integer = std::dynamic_pointer_cast<Integer>(sol);
			//f (integer);
			HolderPtr holder = integer->Get();
			unsigned width = GetWidth(holder);
			if (width == 8) {
				// readability optimization
			}
			std::cerr << width << " ";
		}
		else if (utils::instanceof<Pointer>(sol)) {
			PointerPtr pointer = std::dynamic_pointer_cast<Pointer>(sol);
			//f (pointer);
			RestrictionHelper(pointer->Dereference());
		}
		else if (utils::instanceof<Array>(sol)) {
			ArrayPtr array = std::dynamic_pointer_cast<Array>(sol);
			//f (array);
			for (int i = 0; i < array->GetSize(); i++) {
				SolutionPtr el_sol = array->GetElement(i);
				RestrictionHelper(el_sol);
			}
		}
		else
			assert (! "unexpected type of argument");
	}

	void ReadabilityOptimizer::RestrictionPass() {
		for (auto it = arg_sols_->begin(); it != arg_sols_->end(); ++it) {
			RestrictionHelper(*it);
		}
		std::cerr << " :- ";
		RestrictionHelper(ret_sol_);
		std::cerr << "\n";
	}

	void ReadabilityOptimizer::ConcretizationPass() {

	}
}











