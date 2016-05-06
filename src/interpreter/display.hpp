#ifndef __DISPLAY_HPP__
#define __DISPLAY_HPP__

#include "display-interface.hpp"
#include "../utils/creatable.hpp"

// std
#include <map>
#include <stack>
#include <memory>
#include <cassert>

//llvm

namespace interpreter {
	class Display;
	using utils::creatable;

	/**	Memory display for single symbolic state.
	 * const llvm::Instruction* => stack<ObjectPtr>
	 */
	class Display : public creatable<Display, DisplayInterface> {
	public:
		Display();
		virtual ~Display();
		virtual bool Equals (const Object& rhs) const;
		virtual std::string ToString() const;
		virtual ObjectPtr& LookUp(const llvm::Value* ptr);
		virtual void Push(const llvm::Value* ptr, const ObjectPtr &val);
	private:
		using ObjectStack = std::stack<ObjectPtr>;
		using StackPtr = std::shared_ptr<ObjectStack>;
		using Address = const llvm::Value*;
		using Pair = std::pair<Address, StackPtr>;
		using Map = std::map<Address, StackPtr>;

		StackPtr Find(Address addr);

		Map display_;
	};
}

#endif















