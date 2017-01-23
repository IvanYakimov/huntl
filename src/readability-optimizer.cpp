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

  SharedExpr ReadabilityOptimizer::CharConstraint(Kind relation, SharedExpr var, char symbol) {
    SharedExpr c = context_.Solver().MkConst(BitVec(8, InfiniteInt(symbol)));
    SharedExpr var_R_c = context_.Solver().MkExpr(relation, var, c);
    return var_R_c;
  }

  template <typename T>
  SharedExpr ReadabilityOptimizer::IntConstraint(Kind relation, SharedExpr var, T value) {
    SharedExpr c = context_.Solver().MkConst(BitVec(sizeof(T)*8, InfiniteInt(value)));
    SharedExpr var_R_c = context_.Solver().MkExpr(relation, var, c);
    return var_R_c;
  }

  template <typename T>
  bool ReadabilityOptimizer::TryPutInRange(SharedExpr x, T lower, T upper) {
    SharedExpr x_sge_lower = IntConstraint<T>(Kind::BITVECTOR_SGE, x, lower);
    SharedExpr x_sle_upper = IntConstraint<T>(Kind::BITVECTOR_SLE, x, upper);
    SharedExpr lower_x_upper = context_.Solver().MkExpr(Kind::AND, x_sge_lower, x_sle_upper);
    return TryApplyConstraint(lower_x_upper);
  }

  bool ReadabilityOptimizer::TryMakeAlphabetic(const SharedExpr& x) {
    // Is it (truth) really neaded?
    SharedExpr truth = context_.Solver().MkConst(true);
    SharedExpr x_sge_a = CharConstraint(Kind::BITVECTOR_SGE, x, 'a');
    SharedExpr x_sle_z = CharConstraint(Kind::BITVECTOR_SLE, x, 'z');
    SharedExpr x_sge_A = CharConstraint(Kind::BITVECTOR_SGE, x, 'A');
    SharedExpr x_sle_Z = CharConstraint(Kind::BITVECTOR_SLE, x, 'Z');
    SharedExpr a_x_z = context_.Solver().MkExpr(Kind::AND, x_sge_a, x_sle_z);
    SharedExpr A_x_Z = context_.Solver().MkExpr(Kind::AND, x_sge_A, x_sle_Z);
    SharedExpr maybe_x_alpha = context_.Solver().MkExpr(Kind::OR, a_x_z, A_x_Z);
    SharedExpr x_indeed_alpha = context_.Solver().MkExpr(Kind::IFF, maybe_x_alpha, truth);
    return TryApplyConstraint(x_indeed_alpha);
  }

  bool ReadabilityOptimizer::TryMakeReadable(const SharedExpr& x) {
    SharedExpr truth = context_.Solver().MkConst(true);
    SharedExpr x_sge_space = CharConstraint(Kind::BITVECTOR_SGE, x, ' ');
    SharedExpr x_sle_tilda = CharConstraint(Kind::BITVECTOR_SLE, x, '~');
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

#include "options.hpp"
  
  void ReadabilityOptimizer::HandleUnigram(SolutionPtr one) {
#ifdef RANDOM_FIRST
    IntegerPtr a_intsol = ToInteger(one);
    HolderPtr a_holder = a_intsol->Get();
    if (IsSymbolic(a_holder)) {
      SharedExpr a = GetExpr(a_holder);
      char best = UnigramModel::GetLower();
      SharedExpr a_eq_best = CharConstraint(Kind::EQUAL, a, best);
      TryApplyConstraint(a_eq_best);
    }
#endif
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
#warning "uppercase letters support not implemented"
	//assert (false and "uppercase letters support not implemented");
      } else {
	// do nothing
	;
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
	HandleUnigram(array->GetElement(0));
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

  void ReadabilityOptimizer::IntOptHelper(SolutionPtr sol) {
    if (utils::instanceof<Integer>(sol)) {
      IntegerPtr integer = std::dynamic_pointer_cast<Integer>(sol);
      HolderPtr holder = integer->Get();
      unsigned width = GetWidth(holder);
      if ((width == 16 or width == 32 or width == 64) and IsSymbolic(holder)) {
	auto x = GetExpr(holder);
	if (TryPutInRange(x, -10, 10))
	  return;
	else if (TryPutInRange(x, -100, 100))
	  return;
	else if (TryPutInRange(x, -1000, 1000))
	  return;
	else
	  return;
      }
    } else if (utils::instanceof<Pointer>(sol)) {
      PointerPtr pointer = std::dynamic_pointer_cast<Pointer>(sol);
      IntOptHelper(pointer->Dereference());
    } else if (utils::instanceof<Array>(sol)) {
      ArrayPtr array = std::dynamic_pointer_cast<Array>(sol);
      for (int i = 0; i < array->GetSize(); i++) {
	SolutionPtr el_sol = array->GetElement(i);
	IntOptHelper(el_sol);
      }
    } else
      assert (! "unexpected type of argument");
  }

  void ReadabilityOptimizer::IntOptPass() {
    for (auto it = arg_sols_->begin(); it != arg_sols_->end(); ++it) {
      IntOptHelper(*it);
    }
    IntOptHelper(ret_sol_);
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











