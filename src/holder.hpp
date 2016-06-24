#ifndef __HOLDER_HPP__
#define __HOLDER_HPP__

#include <cvc4/cvc4.h>
#include "instanceof.hpp"

namespace memory {
	class Holder;

	using HolderPtr = std::shared_ptr<Holder>;

	class Holder {
	public:
		virtual ~Holder(){}
	};

	template <typename T>
	class ObjectHolder : public Holder {
	public:
		ObjectHolder(T value) : value_(value) {}
		virtual ~ObjectHolder() {}
		T Get() {return value_;}
		static HolderPtr Create(T arg) {
			return std::make_shared<ObjectHolder<T>>(arg);
		}

	private:
		T value_;
	};

	class Undef : public Holder {
	public:
		Undef();
		static HolderPtr Create();
	};

	using Symbolic = ObjectHolder<CVC4::Expr>;

	bool IsSymbolic(HolderPtr holder);
	bool IsUndef(HolderPtr holder);
	bool IsConcrete(HolderPtr holder);
}

#endif











