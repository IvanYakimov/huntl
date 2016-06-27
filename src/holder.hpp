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

	class Holder : public Object {
	public:
		COMPARABLE(Holder);
		PRINTABLE(Holder);
		virtual ~Holder(){}
	};

	template <typename B>
	using ObjHolder = utils::Wrapper<Holder, B>;

	class Undef : public Holder {
	public:
		COMPARABLE(Undef);
		PRINTABLE(Undef);
		virtual bool Equals (const Object& rhs) const;
		virtual std::ostream& ToStream(std::ostream &os, const Object& obj) const;
		Undef();
		static HolderPtr Create();
	};

	using Concrete = utils::Wrapper<Holder, solver::BitVec, solver::BitVec_print_, solver::BitVec_compare_>;
	using Symbolic = ObjHolder<solver::Expr>;

	bool IsSymbolic(HolderPtr holder);
	bool IsUndef(HolderPtr holder);
	bool IsConcrete(HolderPtr holder);
}

#endif













