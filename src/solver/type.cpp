#include "type.hpp"

namespace solver {
	template<typename T>
	std::string IntTy<T>::ToString() const {
		return (IsSigned()?"i":"u") + solver::to_string(GetWidth()) + " ty";
	}

	template<typename T>
	bool IntTy<T>::Equals (const Object& rhs) const {
		auto f = [] (auto l, auto r) -> bool {return true;};
		return EqualsHelper<IntTy<T>>(*this, rhs, f);
	}

	template<typename T>
	Width IntTy<T>::GetWidth() const {
		return solver::from_size_t(sizeof(T));
	}

	template<typename T>
	Alignment IntTy<T>::GetAlignment() const {
		return sizeof(T);
	}

	template<typename T>
	bool IntTy<T>::IsSigned() const {
		return std::numeric_limits<T>::is_signed;
	}
}











