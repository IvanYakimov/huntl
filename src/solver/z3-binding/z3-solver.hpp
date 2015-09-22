// internals
# include "../isolver.hpp"

// z3
# include <z3++.h>

// std
# include <memory>

namespace solver
{
  class Z3Solver : public ISolver
  {
    Z3Solver ();
    ~Z3Solver ();

  private:
    std::shared_ptr <z3::context> z3_context_;
    std::unique_ptr <z3::solver> z3_solver_;
  };
}
