# include "z3-solver.hpp"

namespace solver
{
  Z3Solver :: Z3Solver ()
  {
    context_ = std::make_shared <z3::context> ();
    solver_ = std::make_unique <z3::solver> (*context_);
  }

  Z3Solver :: ~Z3Solver () {}

  void Z3Solver :: AssertExpr (const IExpr& expr)
  {
    
  }

  void Z3Solver :: Push ()
  {
    solver_->push ();
  }

  void Z3Solver :: Pop ()
  {
    solver_->pop ();
  }
}
