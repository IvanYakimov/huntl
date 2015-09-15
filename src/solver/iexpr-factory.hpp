# include "iexpr.hpp"

namespace Solver
{
  /**
   * Interface for an expression factory.
   * Each method takes one or more instances of classes that implement IExpr interface
   * and returns a new instance (same type) representing an appropriate expression.
   * Note that this factory returns a smart pointer std::unique_ptr < IExpr >, so a
   * caller acquires responsibility for the produced object (factory product).
   * @author Ivan Yakiomv, e-mail: ivan.yakimov.research@yandex.ru
   * @date 15.09.2015
   */
  class IExprFactory
  {
    /**
     * Create new expression representing "not a" operation.
     */
    virtual std::unique_ptr <IExpr> Not
    (const IExpr& a) = 0;

    /**
     * Create new expression representing "a + b" operation.
     */
    virtual std::unique_ptr <IExpr> Addition
    (const IExpr& a, const IExpr& b) = 0;

    /**
     * Create new expression representing "a - b" operation.
     */
    virtual std::unique_ptr <IExpr> Subtraction
    (const IExpr& a, const IExpr& b) = 0;

    /**
     * Create new expression representing "a * b" operation.
     */
    virtual std::unique_ptr <IExpr> Multiplication
    (const IExpr& a, const IExpr& b) = 0;

    /** 
     * Create new expression representing "a / b" operation.
     */
    virtual std::unique_ptr <IExpr> Division
    (const IExpr& a, const IExpr& b) = 0;

    /**
     * Create new expression representing "a = b" relation.
     */
    virtual std::unique_ptr <IExpr> Equal
    (const IExpr& a, const IExpr& b) = 0;

    /**
     * Create new expression representing "a > b" relation.
     */
    virtual std::unique_ptr <IExpr> GreaterThan
    (const IExpr& a, const IExpr& b) = 0;

    /**
     * Create new expression representing "a < b" relation.
     */
    virtual std::unique_ptr <IExpr> LessThen
    (const IExpr& a, const IExpr& b) = 0;
  };
}
