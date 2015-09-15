# include "iexpr.hpp"

namespace Solver
{
  /**
 * Interface for an abstract incremental solver.
 * @author Ivan Yakimov, e-mail: ivan.yakimov.research@yandex.ru
 * @date 14.09.2015
 */
  class ISolver
  {
    /** 
     * Add a new expression to the assertion stack.
     */
    virtual void AssertExpr (const IExpr& expr) = 0;

    /**
     * Create a new scope on top of the assertion stack.
     */
    virtual void Push () = 0;

    /**
     * Remove a scope from top of the assertion stack.
     */
    virtual void Pop () = 0;
  };
}
