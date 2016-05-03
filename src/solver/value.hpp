#ifndef __VALUE_HPP__
#define __VALUE_HPP__

// PROJECT
#include "../utils/object.hpp"
#include "width.hpp"

// SLT
#include <limits>
#include <memory>
#include <cstring>
#include <type_traits>

namespace solver {
	class Value;
	class BasicIntVal;
	template<typename T> class IntVal;

	using ValuePtr = std::shared_ptr<Value>;
	using BasicIntPtr = std::shared_ptr<BasicIntVal>;
	template<typename T> using IntPtr = std::shared_ptr<IntVal<T>>;

	/** Basic value.
	 * \note Every particular value class should be inherited (by CRTP <T,B>) from this.
	 * \see BasicInt
	 * \see CRTP <T,B> */
	class Value : public shared <Value, Immutable> {
	public:
		virtual ~Value() {}
	};

	/** Basic integer value. This is useful to make (smart) pointer for particular integer value
	 * \see Int
	 * \see ExprManager::MkIntVal
	 */
	class BasicIntVal : public shared <BasicIntVal, Value> {
	public:
		/** Returns width (number of bits) in the integer. */
		virtual Width GetWidth() const = 0;
		/** Returns true if this is signed integer, and false if it's not. */
		virtual bool IsSigned() const = 0;
		/** Returns 64-bit unsigned long representation of the stored integer value.
		 * This routine copies significant bytes from stored raw integer value to result (in machine dependent order),
		 * and fills insignificant bytes by zeros.
		 * \see SetUInt64 */
		virtual uint64_t GetUInt64() const = 0;
		/** Set up value from 64-bit unsigned long representation.
		 * This routine copies significant bytes from argument to stored raw integer value (in machine dependent order),
		 * and fills insignificant bytes by zeros.
		 * For example: if we have int8_t x = "FF", the val (representing x as uint64_t) should contain "00 00 00 00 00 00 00 FF";
		 * for int32_t y = "FF FF FF FF" val = "00 00 00 00 FF FF FF FF", etc.
		 * \see GetUInt64 */
		virtual void SetUInt64(const uint64_t& val) const = 0;
	};

	/** Particular integer value.
	 * \tparam T is a fixed width integer (scalar) type from STL. It can be:
	 * int8_t, int16_t, int32_t, int64_t, uint8_t, uint16_t, uint32_t, uint64_t.
	 */
	template<typename T>
	class IntVal : public shared <IntVal<T>, BasicIntVal> {
	public:
		/** Basic constructor, do NOT use it directly! Use ExprManager::MkIntVal instead */
		IntVal(T value);
		/** Creates "empty" integer value for further initialization, do NOT use it directly!
		 * \note Use ExprManager::MkIntVal(bool, Width, uint64_t) instead */
		IntVal();
		virtual ~IntVal();
		/** Structural equality of this Int<T> instance and another Object instance.
		 * Returns true if the rhs is instance of Int<T>,
		 * their types (template parameter T) must be equivalent, as well as
		 * their stored raw integer values must be equivalent too.
		 */
		virtual bool Equals (const Object& rhs) const final;
		/** String representation in format "i<width> <value>".
		 * Where width is number of bites of stored raw integer value
		 * and value is string representation of stored raw integer value.
		 */
		virtual std::string ToString() const final;
		T GetVal() const;
		/** Returns value's width. \see BasicInt::GetWidth */
		virtual Width GetWidth() const final;
		/** Whether it is signed or not. \see  BasicInt::IsSigned */
		virtual bool IsSigned() const final;
		/** Returns unsigned long representation. \see BasicInt::GetUInt64 */
		virtual uint64_t GetUInt64() const final;
		/** Initialize from unsigned long. \see BasicInt::SetUInt64*/
		virtual void SetUInt64(const uint64_t& val) const final;
	private:
		//TODO: value MUST be immutable!
		const T value_ = 0;
		const bool initiated_ = false;
	};

	template class IntVal<int8_t>;
	template class IntVal<int16_t>;
	template class IntVal<int32_t>;
	template class IntVal<int64_t>;
	template class IntVal<uint8_t>;
	template class IntVal<uint16_t>;
	template class IntVal<uint32_t>;
	template class IntVal<uint64_t>;
}

#endif /* __VALUE_HPP__ */













