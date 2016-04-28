#ifndef __DISPLAY_STUB_HPP__
#define __DISPLAY_STUB_HPP__

// PROJECT
#include "../../src/interpreter/display-interface.hpp"
#include "../../src/interpreter/memory.hpp"
#include "../../src/interpreter/memory-interface.hpp"

// STL
#include <map>
#include <cassert>

/** Displays instructions to addresses in bypass mode */
class DisplayStub : interpreter::DisplayInterface {
private:
	interpreter::StateId owner_;
	interpreter::MemoryPtr memory_;
	std::map <const llvm::Value*, interpreter::Address> memory_map_;
public:
	DisplayStub(interpreter::MemoryPtr memory, interpreter::StateId owner) : memory_(memory), owner_(owner) {}
	virtual ~DisplayStub();
	virtual ObjectPtr Load(const llvm::Value* ptr);
	virtual void Store(const llvm::Value* ptr, ObjectPtr val);
	virtual void Alloca(const llvm::Value* ptr);
private:
	bool LookUp(const llvm::Value* ptr);
};

#endif













