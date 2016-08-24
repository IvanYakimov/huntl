#include "holder-helper.hpp"

namespace interpreter {
	using solver::SolverRef;

	MetaInt Concretize(SolverRef solver, memory::HolderPtr holder) {
		if (memory::IsConcrete(holder)) {
			MetaInt val = memory::GetValue(holder);
			return val;
			//return Integer::Create(holder);
		} else if (memory::IsSymbolic(holder)) {
			solver::SharedExpr e = memory::GetExpr(holder);
			interpreter::MetaInt val = solver.GetValue(e);
			return val;
			//return Integer::Create(holder);
		}
		else
			assert (false and "not expected");
	}
}
