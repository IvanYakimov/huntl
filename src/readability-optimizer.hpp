#ifndef __READABILITY_OPTIMIZER_HPP__
#define __READABILITY_OPTIMIZER_HPP__

#include "context.hpp"
#include "solution.hpp"
#include "holder.hpp"
#include "holder-helper.hpp"
#include "solver.hpp"
#include "unigram-model.hpp"
#include "bigram-model.hpp"

namespace interpreter {
  class ReadabilityOptimizer {
  public:
    ReadabilityOptimizer(ContextRef context, SolutionListPtr arg_sols, SolutionPtr ret_sol);
    ~ReadabilityOptimizer();
    void IntOptPass();
    void RestrictionPass();
    void ConcretizationPass();
  private:
    ContextRef context_;
    SolutionListPtr arg_sols_;
    SolutionPtr ret_sol_;
    BigramModel bigrammer_;
    void HandleUnigram(SolutionPtr one);
    void HandleBigram(SolutionPtr first, SolutionPtr second);
    void ConcretizationHelper(SolutionPtr sol);
    void IntOptHelper(SolutionPtr sol);
    void RestrictionHelper(SolutionPtr sol);
    void RestrictionHelperInteger(solver::SharedExpr variable);
    bool TryMakeReadable(const solver::SharedExpr& x);
    bool TryMakeAlphabetic(const solver::SharedExpr& x);
    bool TryApplyConstraint(const solver::SharedExpr& constraint);
    solver::SharedExpr CharConstraint(solver::Kind relation, solver::SharedExpr var, char symbol);
    template <typename T>
    solver::SharedExpr IntConstraint(solver::Kind relation, solver::SharedExpr var, T value);
    template <typename T>
    bool TryPutInRange(solver::SharedExpr var, T lower, T upper);
  };
}

#endif
