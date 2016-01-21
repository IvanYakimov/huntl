#ifndef __ISMT_ENGINE_HPP__
#define __ISMT_ENGINE_HPP__

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

	class ISMTEngine
	{
	public:
		virtual ~ISMTEngine() {}
		virtual void Assert (SharedExprPtr expr) = 0;
		virtual Sat CheckSat() = 0;
		virtual std::int32_t GetValue(SharedExprPtr varible) = 0;
	};
}

#endif
