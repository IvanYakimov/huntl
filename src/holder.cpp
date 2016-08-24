#include "holder.hpp"

namespace memory {
	using interpreter::MetaIntRef;
	using interpreter::MetaInt;
	using solver::SolverRef;
	using solver::SharedExpr;


	bool IsSymbolic(HolderPtr holder) {
		return utils::instanceof<Symbolic>(holder);
	}

	bool IsConcrete(HolderPtr holder) {
		return (utils::instanceof<Concrete>(holder));
	}

	bool IsUndef(HolderPtr holder) {
		return (utils::instanceof<Undef>(holder));
	}

	const solver::SharedExpr& GetExpr(memory::HolderPtr holder) {
		assert(memory::IsSymbolic(holder));
		return Object::UpCast<memory::Symbolic>(holder)->Get();
	}

	const interpreter::MetaInt& GetValue(memory::HolderPtr holder) {
		assert(memory::IsConcrete(holder));
		return Object::UpCast<memory::Concrete>(holder)->Get();
	}

	bool Undef::Equals (const Object& rhs) const {
		return false;
	}

	HolderPtr Undef::Create() {
		return utils::Create<Holder, Undef>();
	}

	std::ostream& Undef::ToStream(std::ostream &os, const Object& obj) const {
		os << "undef";
		return os;
	}

	unsigned WidthToAlign(unsigned width) {
		assert (width > 0);
		if (width % 8 == 0)
			return width % 8;
		else if (width == 1)
			return memory::kBoolAlign;
	}

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













