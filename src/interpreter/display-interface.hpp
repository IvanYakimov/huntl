#ifndef __DISPLAY_INTERFACE_HPP__
#define __DISPLAY_INTERFACE_HPP__

// PROJECT
#include "../utils/object.hpp"

// STL
#include <memory>

// LLVM
# include "llvm/IR/Instruction.h"
# include "llvm/Support/raw_ostream.h"

namespace interpreter {
	class DisplayInterface;
	using DisplayPtr = std::shared_ptr<DisplayInterface>;
	/**	Memory display for single symbolic state. */
	class DisplayInterface {
	public:
		virtual ~DisplayInterface() {}
		virtual ObjectPtr LookUp(const llvm::Value* ptr) = 0;
		virtual void Push(const llvm::Value* ptr, ObjectPtr val) = 0;
	};
}

#endif /* __DISPLAY_INTERFACE_HPP__ */
















