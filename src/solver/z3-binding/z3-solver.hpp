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
  public:
    Z3Solver ();
    ~Z3Solver ();
    
    virtual void AssertExpr (const IExpr& expr) = 0;
    virtual void Push () = 0;
    virtual void Pop () = 0;

  private:
    std::shared_ptr <z3::context> context_;
    std::unique_ptr <z3::solver> solver_;
  };
}
