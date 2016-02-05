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
	private:
	};
}

#endif /* __TYPE_HPP__ */






















