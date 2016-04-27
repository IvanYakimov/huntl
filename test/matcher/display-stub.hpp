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
	std::map <const llvm::Instruction*, interpreter::Address> memory_map_;
public:
	DisplayStub(interpreter::MemoryPtr memory, interpreter::StateId owner) : memory_(memory), owner_(owner) {}
	virtual ~DisplayStub();
	virtual ObjectPtr Read(const llvm::Instruction* ptr);
	virtual void Write(const llvm::Instruction* ptr, ObjectPtr val);
	virtual void Allocate(const llvm::Instruction* ptr);
private:
	bool LookUp(const llvm::Instruction* ptr);
};

#endif













