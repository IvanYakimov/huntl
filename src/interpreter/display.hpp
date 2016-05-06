#ifndef __DISPLAY_HPP__
#define __DISPLAY_HPP__

#include "display-interface.hpp"

// std
#include <map>
#include <stack>
#include <memory>
#include <cassert>

namespace interpreter {
	class Display;

	/**	Memory display for single symbolic state.
	 * const llvm::Instruction* => stack<ObjectPtr>
	 */
	class Display final : public DisplayInterface{
	public:
		virtual ~Display();
		virtual ObjectPtr Load(const llvm::Value* ptr);
		virtual void Store(const llvm::Value* ptr, ObjectPtr val);
		virtual void Alloca(const llvm::Value* ptr, ObjectPtr val);
	private:
		using ObjectStack = std::stack<ObjectPtr>;
		using StackPtr = std::shared_ptr<ObjectStack>;
		using Address = const llvm::Value*;
		using Pair = std::pair<Address, StackPtr>;
		using Map = std::map<Address, StackPtr>;

		StackPtr LookUp(Address addr);

		Map display_;
	};
}

#endif















