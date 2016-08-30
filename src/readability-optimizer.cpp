#include "readability-optimizer.hpp"

namespace interpreter {
	using memory::IsConcrete; using memory::IsSymbolic;
	using solver::SharedExpr; using solver::BitVec; using solver::Kind; using solver::InfiniteInt;

	ReadabilityOptimizer::ReadabilityOptimizer(ContextRef context, SolutionListPtr arg_sols, SolutionPtr ret_sol) :
		context_(context), arg_sols_(arg_sols), ret_sol_(ret_sol), bigrammer_() {
	}

	ReadabilityOptimizer::~ReadabilityOptimizer() {

	}

	bool ReadabilityOptimizer::TryApplyConstraint(const SharedExpr& constraint) {
		bool probe_result = false;
		context_.Solver().Push();
		{
			context_.Solver().Constraint(constraint);
			probe_result = context_.Solver().IsSat();
		}
		context_.Solver().Pop();
		if (probe_result == true)
			context_.Solver().Constraint(constraint);
		assert(context_.Solver().IsSat() and "pc damaged while optimization");
		return probe_result;
	}

	bool ReadabilityOptimizer::TryMakeAlphabetic(const SharedExpr& x) {
		SharedExpr a = context_.Solver().MkConst(BitVec(8, InfiniteInt('a')));
		SharedExpr z = context_.Solver().MkConst(BitVec(8, InfiniteInt('z')));
		SharedExpr A = context_.Solver().MkConst(BitVec(8, InfiniteInt('A')));
		SharedExpr Z = context_.Solver().MkConst(BitVec(8, InfiniteInt('Z')));
		SharedExpr truth = context_.Solver().MkConst(true);
		SharedExpr x_sge_a = context_.Solver().MkExpr(Kind::BITVECTOR_SGE, x, a);
		SharedExpr x_sle_z = context_.Solver().MkExpr(Kind::BITVECTOR_SLE, x, z);
		SharedExpr a_x_z = context_.Solver().MkExpr(Kind::AND, x_sge_a, x_sle_z);
		SharedExpr x_sge_A = context_.Solver().MkExpr(Kind::BITVECTOR_SGE, x, A);
		SharedExpr x_sle_Z = context_.Solver().MkExpr(Kind::BITVECTOR_SLE, x, Z);
		SharedExpr A_x_Z = context_.Solver().MkExpr(Kind::AND, x_sge_A, x_sle_Z);
		SharedExpr maybe_x_alpha = context_.Solver().MkExpr(Kind::OR, a_x_z, A_x_Z);
		SharedExpr x_indeed_alpha = context_.Solver().MkExpr(Kind::IFF, maybe_x_alpha, truth);
		return TryApplyConstraint(x_indeed_alpha);
	}

	bool ReadabilityOptimizer::TryMakeReadable(const SharedExpr& x) {
		SharedExpr space = context_.Solver().MkConst(BitVec(8, InfiniteInt(' ')));
		SharedExpr tilda = context_.Solver().MkConst(BitVec(8, InfiniteInt('~')));
		SharedExpr truth = context_.Solver().MkConst(true);
		SharedExpr x_sge_space = context_.Solver().MkExpr(Kind::BITVECTOR_SGE, x, space);
		SharedExpr x_sle_tilda = context_.Solver().MkExpr(Kind::BITVECTOR_SLE, x, tilda);
		SharedExpr maybe_x_readable = context_.Solver().MkExpr(Kind::AND, x_sge_space, x_sle_tilda);
		SharedExpr x_indeed_readable = context_.Solver().MkExpr(Kind::IFF, maybe_x_readable, truth);
		return TryApplyConstraint(x_indeed_readable);
	}

	void ReadabilityOptimizer::RestrictionHelperInteger(SharedExpr x) {
		if (TryMakeReadable(x) == true) {
			TryMakeAlphabetic(x);
		}
	}

	void ReadabilityOptimizer::RestrictionHelper(SolutionPtr sol) {
		if (utils::instanceof<Integer>(sol)) {
			IntegerPtr integer = std::dynamic_pointer_cast<Integer>(sol);
			HolderPtr holder = integer->Get();
			unsigned width = GetWidth(holder);
			if (width == 8 and IsSymbolic(holder)) {
				RestrictionHelperInteger(GetExpr(holder));
			}
		} else if (utils::instanceof<Pointer>(sol)) {
			PointerPtr pointer = std::dynamic_pointer_cast<Pointer>(sol);
			RestrictionHelper(pointer->Dereference());
		} else if (utils::instanceof<Array>(sol)) {
			ArrayPtr array = std::dynamic_pointer_cast<Array>(sol);
			for (int i = 0; i < array->GetSize(); i++) {
				SolutionPtr el_sol = array->GetElement(i);
				RestrictionHelper(el_sol);
			}
		} else
			assert (! "unexpected type of argument");
	}

	void ReadabilityOptimizer::HandleBigram(SolutionPtr first, SolutionPtr second) {
		IntegerPtr a_intsol = ToInteger(first);
		HolderPtr a_holder = a_intsol->Get();
		IntegerPtr b_intsol = ToInteger(second);
		HolderPtr b_holder = b_intsol->Get();
		MetaIntRef a_val = Concretize(context_.Solver(), a_holder);
		if (IsSymbolic(b_holder)) {
			char a = GetChar(a_val);
			SharedExpr b_sym = GetExpr(b_holder);
			SharedExpr truth = context_.Solver().MkConst(true);
			char best_next = 0;
			if (std::islower(a)) {
				best_next = bigrammer_.LowerByLower(a);
				//std::cerr << "(" << a << " -> " << best_next << ")";
				SharedExpr best_next_sym = context_.Solver().MkConst(BitVec(8, InfiniteInt(best_next)));
				SharedExpr b_maybe_best = context_.Solver().MkExpr(Kind::EQUAL, b_sym, best_next_sym);
				//SharedExpr b_indeed_best = context_.Solver().MkExpr(Kind::IFF, b_maybe_best, truth);
				TryApplyConstraint(b_maybe_best);
					//std::cerr << b_maybe_best << std::endl;
			} else if (std::isupper(a)) {
				// not implemented
			} else {
				// do nothing
			}
		}
	}

	void ReadabilityOptimizer::ConcretizationHelper(SolutionPtr sol) {
		if (utils::instanceof<Integer>(sol)) {
			IntegerPtr integer = std::dynamic_pointer_cast<Integer>(sol);
		} else if (utils::instanceof<Pointer>(sol)) {
			PointerPtr pointer = std::dynamic_pointer_cast<Pointer>(sol);
			ConcretizationHelper(pointer->Dereference());
		} else if (utils::instanceof<Array>(sol)) {
			ArrayPtr array = std::dynamic_pointer_cast<Array>(sol);
			if (array->IsString() and array->GetSize() > 1) {
				for (int i = 0; i < array->GetSize() - 1; i++) {
					HandleBigram(array->GetElement(i), array->GetElement(i+1));
				}
				//std::cerr << "\n";
			} else {
				for (int i = 0; i < array->GetSize(); i++) {
					SolutionPtr el_sol = array->GetElement(i);
					ConcretizationHelper(el_sol);
				}
			}
		}
		else
			assert (! "unexpected type of argument");
	}

	void ReadabilityOptimizer::RestrictionPass() {
		for (auto it = arg_sols_->begin(); it != arg_sols_->end(); ++it) {
			RestrictionHelper(*it);
		}
		RestrictionHelper(ret_sol_);
	}

	void ReadabilityOptimizer::ConcretizationPass() {
		if (context_.Solver().IsSat()) {
			for (auto it = arg_sols_->begin(); it != arg_sols_->end(); ++it) {
				ConcretizationHelper(*it);
			}
			ConcretizationHelper(ret_sol_);
		}
		else
			assert (false and "pc must be satisfable");
	}
}











