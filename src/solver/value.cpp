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
		return (IsSigned()?"i":"ui") + to_string(GetWidth()) + " " + std::to_string(GetVal());
	}

	template<typename T>
	T Int<T>::GetVal() const {
		return value_;
	}

	template<typename T>
	Width Int<T>::GetWidth() const {
		return from_size_t(sizeof(T));
	}

	template<typename T>
	bool Int<T>::IsSigned() const {
		return std::numeric_limits<T>::is_signed;
	}

	//TODO: try to replace by fast bitwise operations
	template<typename T>
	uint64_t Int<T>::GetUInt64() const {
#if defined(_M_X64) || defined(__amd64__)
		uint64_t result = 0L;
		memcpy(&result, &value_, sizeof(T));
		return result;
#else
#error "on amd64 is supported"
#endif
	}

	template<typename T>
	void Int<T>::SetUInt64(const uint64_t& val) {
#if defined(_M_X64) || defined(__amd64__)
		memcpy(&value_, &val, sizeof(T));
#else
#error "on amd64 is supported"
#endif
	}
}











