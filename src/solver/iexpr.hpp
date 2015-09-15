# include <memory>

namespace Solver
{
  class IExpr
  {
    virtual IExpr & operator= (const IExpr& obj) = 0;
  };
}
