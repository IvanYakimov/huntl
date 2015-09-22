# include "z3-solver.hpp"

namespace solver
{
  Z3Solver :: Z3Solver ()
  {
    z3_context_ = std::make_shared <z3::context> ();
    z3_solver_ = std::make_unique <z3::solver> (*z3_context_);
  }

  Z3Solver :: ~Z3Solver ()
  {
    
  }
}
