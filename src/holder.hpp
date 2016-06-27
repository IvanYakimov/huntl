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

	using Concrete = utils::Wrapper<Holder, interpreter::BitVec, interpreter::BitVec_print_, interpreter::BitVec_compare_>;
	using Symbolic = utils::Wrapper<Holder, solver::SharedExpr>;

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













