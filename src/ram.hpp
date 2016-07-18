#ifndef __RAM_HPP__
#define __RAM_HPP__

#include "stack.hpp"
#include "object.hpp"
#include "ram-delc.hpp"

namespace memory {
	class Ram;
	using RamRef = Ram&;
	class Ram {
	public:
		NONCOPYABLE(Ram);
		Ram();
		~Ram();
		StackRef Stack();
	private:
		memory::Stack stack_;
	};
};

#endif
