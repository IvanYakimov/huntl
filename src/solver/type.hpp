#ifndef __TYPE_HPP__
#define __TYPE_HPP__

//PROJECT
#include "../utils/object.hpp"
#include "width.hpp"

//STL
#include <limits>
#include <memory>

#include "../utils/singleton.hpp"

namespace solver {
	class Type;
	class BasicIntTy;
	template<typename T> class IntTy;

	using utils::virtual_singleton;

	using TypePtr = std::shared_ptr<Type>;

	/** Basic type.
	 * \note Every particular type should be inherited (by CRTP <T,B>) from this.
	 * \see BasicIntTy
	 * \see CRTP <T,B>*/
	class Type : public shared <Type, Immutable> {
	public:
		virtual ~Type() {}
	};

	/** Basic integer type. Is is useful to make (smart) pointer to particular IntTy.
	 * \see IntTy
	 * \see ExprManager::MkIntTy */
	class BasicIntTy : public shared <BasicIntTy, Type> {
	public:
		virtual ~BasicIntTy() {}
		/** Returns width (number of bites) of wrapped raw integer type */
		virtual Width GetWidth() const = 0;
		/** Returns true if wrapped raw integer type is signed, false if it's not */
		virtual bool IsSigned() const = 0;
	};

	/** Particular integer type.
	  * \tparam T is a fixed width integer (scalar) type from STL. It can be:
	 * int8_t, int16_t, int32_t, int64_t, uint8_t, uint16_t, uint32_t, uint64_t.
	 */
	template<typename T>
	class IntTy : public virtual_singleton <IntTy<T>, BasicIntTy> {
	public:
		/** Basic constructor.
		 * \attention Do NOT use int directly! Use ExprManager::MkIntTy instead */
		IntTy ();
		virtual ~IntTy();
		/** Structural equality of this instance of IntTy and instance of another Object.
		 * Returns true if rhs is instance of IntTy
		 * and if template parameters T are equivalent.
		 */
		virtual bool Equals (const Object& rhs) const final;
		/** String representation of integer type in format "i<width>", where width = number of bites of wrapped raw integer type. */
		virtual std::string ToString() const final;
		/** Number of bitest, \see BasicIntTy::GetWidth */
		virtual Width GetWidth() const final;
		/** Is it signed? \see BasicIntTy::IsSigned */
		virtual bool IsSigned() const final;
	};

	template class IntTy<std::int8_t>;
	template class IntTy<std::int16_t>;
	template class IntTy<std::int32_t>;
	template class IntTy<std::int64_t>;
	template class IntTy<std::uint8_t>;
	template class IntTy<std::uint16_t>;
	template class IntTy<std::uint32_t>;
	template class IntTy<std::uint64_t>;
}

#endif /* __TYPE_HPP__ */






















