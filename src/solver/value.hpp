#ifndef __VALUE_HPP__
#define __VALUE_HPP__

// PROJECT
#include "../utils/object.hpp"

// SLT
#include <limits>

namespace solver {
	class Value;
	class BaseRawInt;
	template<typename T>
	class RawInt;

	using SharedValue = std::shared_ptr<Value>;
	using SharedBaseRawInt = std::shared_ptr<BaseRawInt>;
	template<typename T>
	using SharedRawInt = std::shared_ptr<RawInt<T>>;

	using Alignment = std::size_t;
	using Width = unsigned short;

	class Value : public CRTP <Value, Object> {
	public:
		virtual ~Value() {}
	};

	class BaseRawInt : public CRTP <BaseRawInt, Value> {
	public:
		virtual Width GetWidth() const = 0;
		virtual Alignment GetAlignment() const = 0;
		virtual bool IsSigned() const = 0;
	};

	template<typename T>
	class RawInt : public CRTP <RawInt<T>, BaseRawInt> {
	public:
		virtual ~RawInt();
		RawInt(T value);
		virtual std::string ToString() const final;
		virtual bool Equals (const Object& rhs) const final;
		T GetValue() const;
		virtual Width GetWidth() const final;
		virtual Alignment GetAlignment() const final;
		virtual bool IsSigned() const final;
	private:
		T value_;
	};

	using RawInt8 = RawInt<std::int8_t>;
	template class RawInt<std::int8_t>;

	using RawInt16 = RawInt<std::int16_t>;
	template class RawInt<std::int16_t>;

	using RawInt32 = RawInt<std::int32_t>;
	template class RawInt<std::int32_t>;

	using RawInt64 = RawInt<std::int64_t>;
	template class RawInt<std::int64_t>;

	using RawUInt8 = RawInt<std::uint8_t>;
	template class RawInt<std::uint8_t>;

	using RawUInt16 = RawInt<std::uint16_t>;
	template class RawInt<std::uint16_t>;

	using RawUInt32 = RawInt<std::uint32_t>;
	template class RawInt<std::uint32_t>;

	using RawUInt64 = RawInt<std::uint64_t>;
	template class RawInt<std::uint64_t>;
}

#endif /* __VALUE_HPP__ */









