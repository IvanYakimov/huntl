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
	class Wrapper : public Holder {
	public:
		Wrapper(T value) : value_(value) {}
		virtual ~Wrapper() {}
		T Get() {return value_;}
		static HolderPtr Create(T arg) {
			return std::make_shared<Wrapper<T>>(arg);
		}

	private:
		T value_;
	};

	class Undef : public Holder {
	public:
		Undef();
		static HolderPtr Create();
	};

	using Symbolic = Wrapper<CVC4::Expr>;

	bool IsSymbolic(HolderPtr holder);
	bool IsUndef(HolderPtr holder);
	bool IsConcrete(HolderPtr holder);
}

#endif













