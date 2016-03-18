#ifndef __VALUE_HPP__
#define __VALUE_HPP__

// PROJECT
#include "../utils/object.hpp"
#include "width.hpp"
#include "../utils/memory.hpp"

// SLT
#include <limits>
#include <memory>
#include <cstring>

namespace solver {
	class Value;
	class BasicInt;
	template<typename T> class Int;

	//TODO: REFACTORING - remove all logic_error usages!!!

	using ValuePtr = std::shared_ptr<Value>;
	using BasicIntPtr = std::shared_ptr<BasicInt>;
	template<typename T> using IntPtr = std::shared_ptr<Int<T>>;

	/** Basic value. Every particular value class should be inherited (by CRTP<T,B>) from this.
	 * \see BasicInt
	 */
	class Value : public CRTP <Value, Object> {
	public:
		virtual ~Value() {}
	};

	/** Basic integer value. This is useful to make (smart) pointer for particular integer value
	 * \see Int
	 * \see ExprManager::MkIntVal
	 */
	class BasicInt : public CRTP <BasicInt, Value> {
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
		virtual void SetUInt64(const uint64_t& val) = 0;
	};

	/** Particular integer value.
	 * \tparam T is a fixed width integer (scalar) type from STL. It can be:
	 * int8_t, int16_t, int32_t, int64_t, uint8_t, uint16_t, uint32_t, uint64_t.
	 */
	template<typename T>
	class Int : public CRTP <Int<T>, BasicInt> {
	public:
		/** Basic constructor, do NOT use it directly! Use ExprManager::MkIntVal instead */
		Int(T value);
		/** Creates "empty" integer value for further initialization, do NOT use it directly!
		 * Use ExprManager::MkIntVal(bool, Width, uint64_t) instead */
		Int();
		virtual ~Int();
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
		virtual void SetUInt64(const uint64_t& val) final;
	private:
		T value_;
	};

	template class Int<int8_t>;
	template class Int<int16_t>;
	template class Int<int32_t>;
	template class Int<int64_t>;
	template class Int<uint8_t>;
	template class Int<uint16_t>;
	template class Int<uint32_t>;
	template class Int<uint64_t>;
}

#endif /* __VALUE_HPP__ */













