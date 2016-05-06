#include "display.hpp"

namespace interpreter {
	Display::~Display() {

	}

	ObjectPtr Display::Load(const llvm::Value* ptr) {
		StackPtr stack = LookUp(ptr);
		assert (stack != nullptr && "memory with address 'ptr' must be allocated");
		return stack->top();
	}

	void Display::Store(const llvm::Value* ptr, ObjectPtr val) {
		StackPtr stack = LookUp(ptr);
		assert (stack != nullptr && "memory with address 'ptr' must be allocated");
		return stack->push(val);
	}

	void Display::Alloca(const llvm::Value* ptr, ObjectPtr val) {
		assert (LookUp(ptr) == nullptr && "memory with address 'ptr' can be allocated only once");
		StackPtr stack = std::make_shared<ObjectStack>();
		stack->push(val);
	}

	Display::StackPtr Display::LookUp(Address addr) {
		Map::iterator res = display_.find(addr);
		if (res == display_.end())
			return nullptr;
		else
			return res->second;
	}
}














