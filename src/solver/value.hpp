#ifndef __VALUE_HPP__
#define __VALUE_HPP__

#include "../utils/object.hpp"
#include "type.hpp"

namespace solver {
	class Value;
	class BitVector;
	class Integer;

	using SharedBitVector = std::shared_ptr<BitVector>;

	class Value : public CRTP <Value, Object> {
	public:
		virtual ~Value() {}
		virtual const std::string ToString() = 0;
		virtual bool Equals (const Object& rhs) const = 0;
	};

	class BitVector : public CRTP <BitVector, Value> {
	public:
		virtual ~BitVector();
		BitVector(BTVWidth width, std::uint64_t Value);
		virtual const std::string ToString() final;
		virtual bool Equals (const Object& rhs) const final;
		std::uint64_t GetValue();
	private:
		BTVWidth width_;
		std::uint64_t value_;
	};

	class Integer {
	public:
		template<typename T>
		static T FromULong(std::uint64_t);
		template<typename T>
		static std::uint64_t ToULong(T);
	};
}

#endif /* __VALUE_HPP__ */









