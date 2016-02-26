# include "value.hpp"

namespace solver {
	template<typename T>
	Int<T>::~Int() {
	}

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
		return (IsSigned()?"i":"ui") + width::to_string(GetWidth()) + " " + std::to_string(GetVal());
	}

	template<typename T>
	T Int<T>::GetVal() const {
		return value_;
	}

	template<typename T>
	Width Int<T>::GetWidth() const {
		return width::from_size_t(sizeof(T));
	}

	template<typename T>
	bool Int<T>::IsSigned() const {
		return std::numeric_limits<T>::is_signed;
	}

	//TODO: project - try to verify it with Z3
	template<typename T>
	uint64_t Int<T>::GetUInt64() const {
		uint64_t mask = 0L;
		return uint64_t(mask bitor value_);
	}

	template<typename T>
	void Int<T>::SetUInt64(const uint64_t& val) {
		uint64_t mask = 0L;
		const_cast<T&>(value_) = T(val bitor mask);
	}
}











