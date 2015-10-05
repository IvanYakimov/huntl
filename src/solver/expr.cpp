# include "expr.hpp"

//TODO: documentation
//TODO: testing

namespace solver
{
  std::ostream& VariableExpr :: operator << (std::ostream& out)
  {
    out << name () << id ();
  }

  std::ostream& UnaryExpr :: operator << (std::ostream& out)
  {
    out << "(" << name () << child () << ")";
  }

  std::ostream& BinaryExpr :: operator << (std::ostream& out)
  {
    out << "(" << name () << left_child () << right_child () << ")";
  }
}
