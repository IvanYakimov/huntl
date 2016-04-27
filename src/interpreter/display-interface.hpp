#ifndef __DISPLAY_INTERFACE_HPP__
#define __DISPLAY_INTERFACE_HPP__

// PROJECT
#include "../utils/object.hpp"

// STL
#include <memory>

// LLVM
# include "llvm/IR/Instruction.h"

namespace interpreter {
	class DisplayInterface;
	using DisplayPtr = std::shared_ptr<DisplayInterface>;
	/**	Memory display for single symbolic state. */
	class DisplayInterface {
	public:
		virtual ~DisplayInterface() {}
		virtual ObjectPtr Read(const llvm::Instruction& ptr);
		virtual void Write(const llvm::Instruction& ptr, ObjectPtr val);
		virtual void Allocate(const llvm::Instruction& ptr);
	};
}

#endif /* __DISPLAY_INTERFACE_HPP__ */
