# include "value.hpp"

namespace solver {
	template<typename T>
	Int<T>::~Int() {}

	template<typename T>
	Int<T>::Int(T val) : value_(val) {
	}

	template<typename T>
	Int<T>::Int() : value_(0) {
	}

	template<typename T>
	bool Int<T>::Equals (const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
				return lhs.GetVal() == rhs.GetVal();
			};
		return EqualsHelper<Int<T>>(*this, rhs, cmp);
	}

	template<typename T>
	std::string Int<T>::ToString() const {
		return (IsSigned()?"i":"u") + std::to_string(GetWidth()) + " " + std::to_string(GetVal());
	}

	template<typename T>
	T Int<T>::GetVal() const {
		return value_;
	}

	template<typename T>
	Width Int<T>::GetWidth() const {
		return sizeof(T)*8;
	}

	template<typename T>
	Alignment Int<T>::GetAlignment() const {
		return sizeof(T);
	}

	template<typename T>
	bool Int<T>::IsSigned() const {
		return std::numeric_limits<T>::is_signed;
	}

	template<typename T>
	uint64_t Int<T>::GetUInt64() const {
		return uint64_t(value_ bitand (compl T(0)));
	}

	template<typename T>
	void Int<T>::SetUInt64(const uint64_t& val) {
		const_cast<T&>(value_) = T(val bitand (compl uint64_t(0)));
	}
}











