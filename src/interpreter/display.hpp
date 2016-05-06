#ifndef __DISPLAY_HPP__
#define __DISPLAY_HPP__

#include "display-interface.hpp"

namespace interpreter {
	class Display;

	/**	Memory display for single symbolic state. */
	class Display final : public DisplayInterface{
	public:
		virtual ~Display() {}
		virtual ObjectPtr Load(const llvm::Value* ptr);
		virtual void Store(const llvm::Value* ptr, ObjectPtr val);
		virtual void Alloca(const llvm::Value* ptr);
	};
}

#endif
