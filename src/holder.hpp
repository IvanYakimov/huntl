#ifndef __HOLDER_HPP__
#define __HOLDER_HPP__

#include "expr.hpp"
#include "instanceof.hpp"
#include "wrapper.hpp"
#include "creatable.hpp"
#include "meta-int.hpp"

namespace memory {
	class Holder;

	using HolderPtr = std::shared_ptr<Holder>;

	using Concrete = utils::Wrapper<Holder, interpreter::MetaInt, interpreter::MetaInt_print_, interpreter::MetaInt_compare_>;
	using Symbolic = utils::Wrapper<Holder, solver::SharedExpr>;

	bool IsSymbolic(HolderPtr holder);
	bool IsConcrete(HolderPtr holder);

	class Holder : public Object {
	public:
		COMPARABLE(Holder);
		PRINTABLE(Holder);
		virtual ~Holder(){}
	};

	solver::SharedExpr GetExpr(memory::HolderPtr holder);
	interpreter::MetaInt GetValue(memory::HolderPtr holder);
}

#endif













