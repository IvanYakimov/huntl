#ifndef __HOLDER_HPP__
#define __HOLDER_HPP__

#include <cvc4/cvc4.h>
#include "instanceof.hpp"
#include "wrapper.hpp"

namespace memory {
	class Holder;

	using HolderPtr = std::shared_ptr<Holder>;

	template <typename B>
	using H = utils::Wrapper<Holder, B>;

	class Holder {
	public:
		virtual ~Holder(){}
	};

	template <typename T>
	class ObjHolder : public Holder {
	public:
		ObjHolder(T value) : value_(value) {}
		virtual ~ObjHolder() {}
		T Get() {return value_;}
		static HolderPtr Create(T arg) {
			return std::make_shared<ObjHolder<T>>(arg);
		}

	private:
		T value_;
	};

	class Undef : public Holder {
	public:
		Undef();
		static HolderPtr Create();
	};

	using Symbolic = ObjHolder<CVC4::Expr>;

	bool IsSymbolic(HolderPtr holder);
	bool IsUndef(HolderPtr holder);
	bool IsConcrete(HolderPtr holder);
}

#endif













