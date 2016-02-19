#include "type.hpp"

namespace solver {
	template<typename T>
	IntTy<T>::IntTy() {

	}

	template<typename T>
	IntTy<T>::~IntTy() {

	}

	template<typename T>
	bool IntTy<T>::Equals (const Object& rhs) const {
		auto f = [] (auto l, auto r) -> bool {return true;};
		return EqualsHelper<IntTy<T>>(*this, rhs, f);
	}

	template<typename T>
	std::string IntTy<T>::ToString() const {
		return (IsSigned()?"i":"ui") + width::to_string(GetWidth());
	}

	template<typename T>
	Width IntTy<T>::GetWidth() const {
		return width::from_size_t(sizeof(T));
	}

	template<typename T>
	bool IntTy<T>::IsSigned() const {
		return std::numeric_limits<T>::is_signed;
	}
}











