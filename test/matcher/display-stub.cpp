#include "display-stub.hpp"

DisplayStub::~DisplayStub() {
	for (auto it = memory_map_.begin(); it != memory_map_.end(); it++) {
		memory_->Free(it->second, owner_);
	}
}

ObjectPtr DisplayStub::Read(const llvm::Instruction* ptr) {
	assert(LookUp(ptr) && "a memory cell with the appropriate addres must exists");
	auto addr = memory_map_[ptr];
	return memory_->Read(addr, owner_);
}

void DisplayStub::Write(const llvm::Instruction* ptr, ObjectPtr val) {
	assert(LookUp(ptr) && "a memory cell with the appropriate addres must exists");
	auto addr = memory_map_[ptr];
	auto res_addr = memory_->Write(addr, owner_, val);
	assert(addr == res_addr && "bypass mode");
}

void DisplayStub::Allocate(const llvm::Instruction* ptr) {
	assert(not LookUp(ptr) && "a memory cell with the appropriate addres mustn't exists");
	auto addr = memory_map_[ptr];
}

bool DisplayStub::LookUp(const llvm::Instruction* ptr) {
	return memory_map_.find(ptr) != memory_map_.end();
}












