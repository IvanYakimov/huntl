#ifndef __TYPE_HPP__
#define __TYPE_HPP__

#include "../utils/object.hpp"

#include <limits>
#include <memory>

namespace solver {
	class Type;
	class BtvType;

	using SharedType = std::shared_ptr<Type>;
	using SharedBtvType = std::shared_ptr<BtvType>;

	class Type : public CRTP <Type, Object> {
	public:
		virtual ~Type() {}
		virtual const std::string ToString() = 0;
		virtual bool Equals (const Object& rhs) const = 0;
	};

	using BTVWidth = std::uint16_t;
	class BtvType : public CRTP<BtvType, Type> {
		BtvType(BTVWidth width);
		BTVWidth GetBitWidth();
		std::size_t GetAlignment();
		const std::string ToString() final;
		bool Equals (const Object& rhs) const final;
	private:
		const BTVWidth width_;
	};
}

#endif /* __TYPE_HPP__ */
