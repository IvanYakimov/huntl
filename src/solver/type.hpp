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
	class BasicIntTy;
	template<typename T> class IntTy;

	using TypePtr = std::shared_ptr<Type>;

	/*
	using SInt8Ty = IntTy<std::int8_t>;
	using SInt16Ty = IntTy<std::int16_t>;
	using SInt32Ty = IntTy<std::int32_t>;
	using SInt64Ty = IntTy<std::int64_t>;
	using UInt8Ty = IntTy<std::uint8_t>;
	using UInt16Ty = IntTy<std::uint16_t>;
	using UInt32Ty = IntTy<std::uint32_t>;
	using UInt64Ty = IntTy<std::uint64_t>;
	*/

	class Type : public CRTP <Type, Object> {
	public:
		virtual ~Type() {}
	};

	class BasicIntTy : public CRTP <BasicIntTy, Type> {
	public:
		virtual ~BasicIntTy() {}
		virtual Width GetWidth() const = 0;
		virtual Alignment GetAlignment() const = 0;
		virtual bool IsSigned() const = 0;
	};

	template<typename T>
	class IntTy : public CRTP <IntTy<T>, BasicIntTy> {
	public:
		virtual ~IntTy() {}
		IntTy () {}
		virtual std::string ToString() const final;
		virtual bool Equals (const Object& rhs) const final;
		virtual Width GetWidth() const final;
		virtual Alignment GetAlignment() const final;
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






















