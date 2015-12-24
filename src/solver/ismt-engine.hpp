# include "expr.hpp"

namespace solver
{
  /**
 * Interface for an abstract incremental solver.
 * @author Ivan Yakimov, e-mail: ivan.yakimov.research@yandex.ru
 * @date 14.09.2015
 */
	typedef enum {
		  UNSAT,
		  SAT,
		  UNKNOWN
	}Sat;

	class Value {
		//TODO
	};

	class ISmtEngine
	{
	public:
		virtual ~ISmtEngine() {}

		virtual void AssertExpr (SharedExprPtr expr) = 0;

		virtual Sat CheckSat() = 0;

		virtual Value GetValue(SharedVariablePtr varible) = 0;
	};
}
