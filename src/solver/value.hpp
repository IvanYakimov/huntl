#ifndef __VALUE_HPP__
#define __VALUE_HPP__

// PROJECT
#include "../utils/object.hpp"
#include "common-types.hpp"
#include "../utils/memory.hpp"

// SLT
#include <limits>
#include <memory>
#include <cstring>

namespace solver {
	class Value;
	class BasicInt;
	template<typename T> class Int;

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
	 */
	class BasicInt : public CRTP <BasicInt, Value> {
	public:
		/** Returns width (number of bits) in the integer. */
		virtual Width GetWidth() const = 0;
		/** Returns true if this is signed integer, and false if it's not. */
		virtual bool IsSigned() const = 0;
		/** Returns 64-bit-lenghted unsigned long representation of the stored integer value.
		 * This routine copies significant bytes from value to result (in machine dependent order),
		 * and fills insignificant bytes by zeros. */
		virtual uint64_t GetUInt64() const = 0;
		/** Set up value from 64-bit-lenghted unsigned long representation.
		 * This routine copies significant bytes from argument to value (in machine dependent order),
		 * and fills insignificant bytes by zeros. */
		virtual void SetUInt64(const uint64_t& val) = 0;
	};

	/** Particular integer value.
	 * \tparam T is a fixed width integer (scalar) type from STL. It can be:
	 * int8_t, int16_t, int32_t, int64_t, uint8_t, uint16_t, uint32_t, uint64_t.
	 */
	template<typename T>
	class Int : public CRTP <Int<T>, BasicInt> {
	public:
		Int(T value);
		Int();
		virtual ~Int();
		virtual bool Equals (const Object& rhs) const final;
		virtual std::string ToString() const final;
		//TODO: rename to GetInteger
		T GetVal() const;
		virtual Width GetWidth() const final;
		virtual bool IsSigned() const final;
		virtual uint64_t GetUInt64() const final;
		virtual void SetUInt64(const uint64_t& val) final;
	private:
		//TODO: replace by unique_ptr<const T> (to allow check initialization)
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













