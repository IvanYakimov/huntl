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
		virtual ObjectPtr Load(const llvm::Value* ptr) = 0;
		virtual void Store(const llvm::Value* ptr, ObjectPtr val) = 0;
		virtual void Alloca(const llvm::Value* ptr, ObjectPtr val) = 0;
	};
}

#endif /* __DISPLAY_INTERFACE_HPP__ */
















