#include "memory.hpp"

namespace interpreter {
	Memory::Memory() {}

	ObjectPtr Memory::Read(Address address, StateId state_id) {
		MemoryMap::iterator mmap_iter;
		ObjectRecord record;
		OwnerList owner_list;
		OwnerList::iterator onwer_list_iter;
		Permission permission;

		auto init = [&] () {
			mmap_iter = memory_map_.find(address);
			if (mmap_iter != memory_map_.end())
				record = mmap_iter->second;
		};

		auto more_init = [&] () {
			if (mmap_iter != memory_map_.end()) {
				owner_list = record.owner_list_;
				permission = record.permission_;
				onwer_list_iter = std::find(owner_list.begin(), owner_list.end(), state_id);
			}
		};

		auto func = [&] () {
			return record.object_;
		};

		auto pre = [&] () {
			Assert<Exception>(mmap_iter != memory_map_.end(), Failure::BAD_ADDRESS);
			Assert<Exception>(onwer_list_iter != owner_list.end(), Failure::STATE_ID_NOT_FOUND);
			if (permission == Permission::READ_WRITE)
				Assert<Exception>(owner_list.size() == 1, Failure::BAD_OWNER_LIST_SIZE_ON_READ_WRITE);
			if (permission == Permission::READ_ONLY)
				Assert<Exception>(owner_list.size() > 1, Failure::BAD_OWNER_LIST_SIZE_ON_READ_ONLY);
			Assert<Exception>(record.object_ != nullptr, Failure::OBJECT_NOT_EXIST);
		};

		auto post = [&] () {};

		auto inv_in = [&] () {
			auto n = record.owner_list_.size();
			auto p = record.permission_;
			return std::make_tuple(n, p);
		};

		auto inv_out = [&] (auto x) {
			auto n = std::get<0>(x);
			auto p = std::get<1>(x);
			Assert<Exception>(n == record.owner_list_.size(), Failure::OWNER_LIST_CHANGED);
			Assert<Exception>(p == record.permission_, Failure::PERMISSION_CHANGED);
		};

		Contract(init, more_init, inv_in, pre, func, post, inv_out);
	}

	Address Memory::Write(Address address, StateId state_id, ObjectPtr object) {
		MemoryMap::iterator mmap_iter;

		mmap_iter = memory_map_.find(address);

	}

	Address Memory::Allocate(StateId state_id) {

	}

	void Memory::Detach(Address address, StateId state_id) {

	}

	void Memory::Share(Address address, StateId state_id) {

	}

	void Memory::AddOwner(Address address, StateId state_id) {

	}

	void Memory::RemoveOwner(Address address, StateId state_id) {

	}

	void Memory::TryDelete(Address address) {

	}
}















