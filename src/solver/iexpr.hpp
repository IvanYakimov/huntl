// std
# include <memory>

namespace solver
{
  class IExpr
  {
    virtual std::unique_ptr <void> Get () = 0;
  };
}
