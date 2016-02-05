#ifndef __TYPE_HPP__
#define __TYPE_HPP__

#include "../utils/object.hpp"

#include <limits>
#include <memory>

namespace solver {
	class Type : public CRTP <Type, Object> {
	public:
		virtual ~Type() {}
		virtual bool IsRawIntTy() { return false; }
	};

	class GenericRawIntType : public CRTP <GenericRawIntType, Type> {
	public:
		virtual ~GenericRawIntType() {}
		virtual unsigned int Width() = 0;
		virtual std::size_t Alignment() = 0;
		virtual bool IsRawIntTy() final { return true; }
	};

	template<typename T>
	class RawIntType : public CRTP <RawIntType<T>, GenericRawIntType> {
	public:
		virtual ~RawIntType() {}
		RawIntType ();
		virtual const std::string ToString() final;
		virtual bool Equals (const Object& rhs) final;
		virtual unsigned int Width() final;
		virtual std::size_t Alignment() final;
		virtual bool IsSigned() final;
	private:
	};
}

#endif /* __TYPE_HPP__ */













