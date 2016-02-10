#ifndef __TYPE_HPP__
#define __TYPE_HPP__

//PROJECT
#include "../utils/object.hpp"
#include "../utils/common-types.hpp"

//STL
#include <limits>
#include <memory>

namespace solver {
	class Type;
	class BaseRawIntType;
	template<typename T>
	class RawIntType;

	using SharedType = std::shared_ptr<Type>;

	class Type : public CRTP <Type, Object> {
	public:
		virtual ~Type() {}
	};

	class BaseRawIntType : public CRTP <BaseRawIntType, Type> {
	public:
		virtual ~BaseRawIntType() {}
		virtual Width GetWidth() const = 0;
		virtual Alignment GetAlignment() const = 0;
		virtual bool IsSigned() const = 0;
	};

	template<typename T>
	class RawIntType : public CRTP <RawIntType<T>, BaseRawIntType> {
	public:
		virtual ~RawIntType() {}
		RawIntType () {}
		virtual std::string ToString() const final;
		virtual bool Equals (const Object& rhs) const final;
		virtual Width GetWidth() const final;
		virtual Alignment GetAlignment() const final;
		virtual bool IsSigned() const final;
	};

	template class RawIntType<std::int8_t>;
	using RawInt8Ty = RawIntType<std::int8_t>;

	template class RawIntType<std::int16_t>;
	using RawInt16Ty = RawIntType<std::int16_t>;

	template class RawIntType<std::int32_t>;
	using RawInt32Ty = RawIntType<std::int32_t>;

	template class RawIntType<std::int64_t>;
	using RawInt64Ty = RawIntType<std::int64_t>;

	template class RawIntType<std::uint8_t>;
	using RawUInt8Ty = RawIntType<std::uint8_t>;

	template class RawIntType<std::uint16_t>;
	using RawUInt16Ty = RawIntType<std::uint16_t>;

	template class RawIntType<std::uint32_t>;
	using RawUInt32Ty = RawIntType<std::uint32_t>;

	template class RawIntType<std::uint64_t>;
	using RawUInt64Ty = RawIntType<std::uint64_t>;
}

#endif /* __TYPE_HPP__ */






















