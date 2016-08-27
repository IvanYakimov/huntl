#include "holder-helper.hpp"

namespace interpreter {
	using solver::SolverRef;

	MetaInt Concretize(SolverRef solver, memory::HolderPtr holder) {
		//if (solver.IsSat()) {
			if (memory::IsConcrete(holder)) {
				return memory::GetValue(holder);
			} else if (memory::IsSymbolic(holder)) {
				solver::SharedExpr e = memory::GetExpr(holder);
				return solver.GetValue(e);
			}
			assert (false and "not expected");
		/*}
		else
			assert (false and "can't return value for unsatisfable PC");*/
	}

	unsigned GetWidth(memory::HolderPtr holder) {
		if (memory::IsConcrete(holder)) {
			MetaIntRef value = memory::GetValue(holder);
			return value.getBitWidth();
		} else if (memory::IsSymbolic(holder)) {
			solver::SharedExpr expr = memory::GetExpr(holder);
			solver::Type type = expr.getType();
			if (type.isBitVector()) {
				solver::BitVecTy bv_type = static_cast<solver::BitVecTy>(type);
				return bv_type.getSize();
			}
			else
				assert (false and "not expected");
		}
		assert (false and "not expected");
	}
}












