#include "display.hpp"

namespace interpreter {
	using std::cerr;
	using std::cout;
	using llvm::errs;

	Display::Display() {

	}

	Display::~Display() {

	}

	ObjectPtr Display::LookUp(const llvm::Value* ptr) {
		cerr << "lookup:\n";
		errs() << *ptr << "\n";

		StackPtr stack = Find(ptr);
		assert (stack != nullptr && "memory with address 'ptr' must be allocated");

		cerr << "  " << stack->top()->ToString() << "\n";

		return stack->top();
	}

	void Display::Push(const llvm::Value* ptr, ObjectPtr val) {
		cerr << "push:\n";
		errs() << *ptr << "\n";
		cerr << "  " << val->ToString() << "\n";

		StackPtr stack = Find(ptr);
		if (stack == nullptr) {
			stack = std::make_shared<ObjectStack>();
			display_.insert(std::make_pair(ptr, stack));
		}

		stack->push(val);
	}

	Display::StackPtr Display::Find(Address addr) {
		Map::iterator res = display_.find(addr);
		if (res == display_.end())
			return nullptr;
		else
			return res->second;
	}

	bool Display::Equals (const Object& rhs) const {
		assert(false && "not implemented");
		return false;
	}

	std::string Display::ToString() const {
		return "display && TODO";
	}
}














