# include "value.hpp"

namespace solver {
	template<typename T>
	IntVal<T>::~IntVal() {
	}

	template<typename T>
	IntVal<T>::IntVal(T val) : value_(val) {
	}

	template<typename T>
	IntVal<T>::IntVal() {
	}

	template<typename T>
	bool IntVal<T>::Equals (const Object& rhs) const {
		auto cmp = [] (const IntVal<T> &lhs, const IntVal<T> &rhs) -> bool {
				return lhs.GetVal() == rhs.GetVal();
			};
		return EqualsHelper<IntVal<T>>(*this, rhs, cmp);
	}

	template<typename T>
	std::string IntVal<T>::ToString() const {
		return (IsSigned()?"i":"ui") + to_string(GetWidth()) + " " + std::to_string(GetVal());
	}

	template<typename T>
	T IntVal<T>::GetVal() const {
		return value_;
	}

	template<typename T>
	Width IntVal<T>::GetWidth() const {
		return from_size_t(sizeof(T));
	}

	template<typename T>
	bool IntVal<T>::IsSigned() const {
		return std::numeric_limits<T>::is_signed;
	}

	template<typename T>
	uint64_t IntVal<T>::GetUInt64() const {
#if defined(_M_X64) || defined(__amd64__)
		uint64_t result = 0L;
		memcpy(&result, &value_, sizeof(T));
		return result;
#else
#error "on amd64 is supported"
#endif
	}

	template<typename T>
	void IntVal<T>::SetUInt64(const uint64_t& val) const {
		if (not initiated_) {
#if defined(_M_X64) || defined(__amd64__)
			memcpy(const_cast<T*>(&value_), &val, sizeof(T));
#else
#error "on amd64 is supported"
#endif
		const_cast<bool&>(initiated_) = true;
		}
		else {
			throw std::logic_error("value is immutable!");
		}
	}
}











