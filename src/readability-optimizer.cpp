#include "readability-optimizer.hpp"

namespace interpreter {
	using memory::IsConcrete; using memory::IsSymbolic;
	using solver::SharedExpr; using solver::BitVec; using solver::Kind; using solver::InfiniteInt;

	ReadabilityOptimizer::ReadabilityOptimizer(ContextRef context, SolutionListPtr arg_sols, SolutionPtr ret_sol) :
		context_(context), arg_sols_(arg_sols), ret_sol_(ret_sol) {
	}

	ReadabilityOptimizer::~ReadabilityOptimizer() {

	}

	void ReadabilityOptimizer::TryMakeAlphabetic(const SharedExpr& x) {
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
		SharedExpr A_x_Z = context_.Solver().MkExpr(Kind::BITVECTOR_AND, x_sge_A, x_sle_Z);
		SharedExpr maybe_x_alpha = context_.Solver().MkExpr(Kind::OR, a_x_z, A_x_Z);
		SharedExpr x_indeed_alpha = context_.Solver().MkExpr(Kind::IFF, maybe_x_alpha, truth);
		TryMake__Helper(x_indeed_alpha);
	}

	void ReadabilityOptimizer::TryMake__Helper(const SharedExpr& constraint) {
		bool readability_probe = false;
		context_.Solver().Push();
		{
			context_.Solver().Constraint(constraint);
			readability_probe = context_.Solver().IsSat();
		}
		context_.Solver().Pop();
		if (readability_probe == true)
			context_.Solver().Constraint(constraint);
	}

	void ReadabilityOptimizer::TryMakeReadable(const SharedExpr& x) {
		SharedExpr space = context_.Solver().MkConst(BitVec(8, InfiniteInt(' ')));
		SharedExpr tilda = context_.Solver().MkConst(BitVec(8, InfiniteInt('~')));
		SharedExpr truth = context_.Solver().MkConst(true);
		SharedExpr x_sge_space = context_.Solver().MkExpr(Kind::BITVECTOR_SGE, x, space);
		SharedExpr x_sle_tilda = context_.Solver().MkExpr(Kind::BITVECTOR_SLE, x, tilda);
		SharedExpr maybe_x_readable = context_.Solver().MkExpr(Kind::AND, x_sge_space, x_sle_tilda);
		SharedExpr x_indeed_readable = context_.Solver().MkExpr(Kind::IFF, maybe_x_readable, truth);
		TryMake__Helper(x_indeed_readable);
	}

	void ReadabilityOptimizer::RestrictionHelperInteger(SharedExpr x) {
		TryMakeReadable(x);
		TryMakeAlphabetic(x);
	}

	void ReadabilityOptimizer::RestrictionHelper(SolutionPtr sol) {
		if (utils::instanceof<Integer>(sol)) {
			IntegerPtr integer = std::dynamic_pointer_cast<Integer>(sol);
			HolderPtr holder = integer->Get();
			unsigned width = GetWidth(holder);
			if (width == 8 and IsSymbolic(holder)) {
				RestrictionHelperInteger(GetExpr(holder));
			}
		}
		else if (utils::instanceof<Pointer>(sol)) {
			PointerPtr pointer = std::dynamic_pointer_cast<Pointer>(sol);
			RestrictionHelper(pointer->Dereference());
		}
		else if (utils::instanceof<Array>(sol)) {
			ArrayPtr array = std::dynamic_pointer_cast<Array>(sol);
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
		RestrictionHelper(ret_sol_);
	}

	void ReadabilityOptimizer::ConcretizationPass() {

	}
}











