#include "stack.hpp"

namespace memory {
	Stack::Stack() {
		segment_stack_.push(0);
	}

	Stack::~Stack() {
		assert (segment_stack_.top() == 0);
		segment_stack_.pop();
		assert (segment_stack_.size() == 0);
	}

	Stack::MemoryCell::MemoryCell(HolderPtr holder, Alignment align) {
		holder_ = holder;
		align_ = align;
	}

	Stack::MemoryCell::~MemoryCell() {

	}

	Address Stack::Alloca(HolderPtr holder, Alignment align) {
		auto addr = segment_stack_.top();
		segment_stack_.top() += align;
		MemoryCellPtr mcell = std::unique_ptr<MemoryCell>(new MemoryCell(holder, align));
		ram_.emplace(addr, std::move(mcell));
		return addr;
	}

	void Stack::Write(HolderPtr holder, Address addr, Alignment align) {
		assert (addr < segment_stack_.top());
		auto it = ram_.find(addr);
		assert (it != ram_.end());
		assert (it->first == align);
		it->second->holder_ = holder;
	}

	HolderPtr Stack::Read(Address addr, Alignment align) {
		assert (addr < segment_stack_.top());
		auto it = ram_.find(addr);
		assert (it != ram_.end());
		assert (it->first == align);
		auto res = it->second->holder_;
		assert (res != nullptr);
		return res;
	}

	void Stack::Push() {
		auto top_addr = segment_stack_.top();
		segment_stack_.push(top_addr);
	}

	void Stack::Pop() {
		segment_stack_.pop();
		auto top_addr = segment_stack_.top();
		for (auto it = ram_.begin(); it != ram_.end(); ) {
			if (it->first >= top_addr)
				it = ram_.erase(it);
			++it;
		}
	}
}






