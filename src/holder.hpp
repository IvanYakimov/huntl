#ifndef __HOLDER_HPP__
#define __HOLDER_HPP__

#include "bitvec.hpp"
#include "expr.hpp"
#include "instanceof.hpp"
#include "wrapper.hpp"
#include "creatable.hpp"

namespace memory {
	class Holder;

	using HolderPtr = std::shared_ptr<Holder>;

	using Concrete = utils::Wrapper<Holder, solver::BitVec, solver::BitVec_print_, solver::BitVec_compare_>;
	using Symbolic = utils::Wrapper<Holder, solver::Expr>;

	bool IsSymbolic(HolderPtr holder);
	bool IsConcrete(HolderPtr holder);

	class Holder : public Object {
	public:
		COMPARABLE(Holder);
		PRINTABLE(Holder);
		virtual ~Holder(){}
	};

}

#endif













