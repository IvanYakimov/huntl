#ifndef __VALUE_HPP__
#define __VALUE_HPP__

// PROJECT
#include "../utils/object.hpp"
#include "../utils/common-types.hpp"

// SLT
#include <limits>

namespace solver {
	class Value;
	class BasicInt;
	template<typename T>
	class Int;

	using ValuePtr = std::shared_ptr<Value>;
	using BasicIntPtr = std::shared_ptr<BasicInt>;
	template<typename T>
	using IntPtr = std::shared_ptr<Int<T>>;

	class Value : public CRTP <Value, Object> {
	public:
		virtual ~Value() {}
	};

	class BasicInt : public CRTP <BasicInt, Value> {
	public:
		virtual Width GetWidth() const = 0;
		virtual Alignment GetAlignment() const = 0;
		virtual bool IsSigned() const = 0;
	};

	template<typename T>
	class Int : public CRTP <Int<T>, BasicInt> {
	public:
		virtual ~Int();
		Int(T value);
		virtual std::string ToString() const final;
		virtual bool Equals (const Object& rhs) const final;
		T GetValue() const;
		virtual Width GetWidth() const final;
		virtual Alignment GetAlignment() const final;
		virtual bool IsSigned() const final;
	private:
		T value_;
	};

	using SInt8 = Int<std::int8_t>;
	template class Int<std::int8_t>;

	using SInt16 = Int<std::int16_t>;
	template class Int<std::int16_t>;

	using SInt32 = Int<std::int32_t>;
	template class Int<std::int32_t>;

	using SInt64 = Int<std::int64_t>;
	template class Int<std::int64_t>;

	using UInt8 = Int<std::uint8_t>;
	template class Int<std::uint8_t>;

	using UInt16 = Int<std::uint16_t>;
	template class Int<std::uint16_t>;

	using UInt32 = Int<std::uint32_t>;
	template class Int<std::uint32_t>;

	using UInt64 = Int<std::uint64_t>;
	template class Int<std::uint64_t>;
}

#endif /* __VALUE_HPP__ */









