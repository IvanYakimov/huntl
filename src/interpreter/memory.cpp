#include "memory.hpp"

namespace interpreter {
	Memory::Memory() {}

	ObjectPtr Memory::Read(Address address, StateId state_id) {
		MemoryMap::iterator mmap_it;
		ObjectRecord record;
		OwnerList owner_list;
		OwnerList::iterator o_state_id;
		Permission permission;

		mmap_it = memory_map_.find(address);

		// further initialization
		if (mmap_it != memory_map_.end()) {
			record = mmap_it->second;
			owner_list = record.owner_list_;
			permission = record.permission_;
			o_state_id = std::find(owner_list.begin(), owner_list.end(), state_id);
		}

		auto func = [&] () {
			/** Get appropriate object record. */
			record = mmap_it->second;
			/** Return apropriate object. */
			return record.object_;
		};

		/** \pre
		 * - object record with the passed addess exists
		 * - owner list contains the passed state id
		 * - if permission is READ-WRITE, than owner list size = 1
		 * - if permission is READ-ONLY, than owner list size >= 1
		 * - object contains data (not null)
		 */
		auto pre = [&] () {
			Assert<Memory::Exception>(mmap_it != memory_map_.end(), Memory::Failure::BAD_ADDRESS);
			Assert<Memory::Exception>(o_state_id != owner_list.end(), Memory::Failure::STATE_ID_NOT_FOUND);
			if (permission == Permission::READ_WRITE)
				Assert<Memory::Exception>(owner_list.size() == 1, Memory::Failure::BAD_OWNER_LIST_SIZE_ON_READ_WRITE);
			if (permission == Permission::READ_ONLY)
				Assert<Memory::Exception>(owner_list.size() > 1, Memory::Failure::BAD_OWNER_LIST_SIZE_ON_READ_ONLY);
			Assert<Memory::Exception>(record.object_ != nullptr, Memory::Failure::OBJECT_NOT_EXIST);
		};

		auto post = [&] () {};

		/** \invariant
		 * - owner list size cannot be changed
		 * - permission cannot be changed */
		auto inv_in = [&] () {
			auto n = record.owner_list_.size();
			auto p = record.permission_;
			return std::make_tuple(n, p);
		};

		auto inv_out = [&] (auto x) {
			//auto n = std::get<0>(n);
		};

		Contract(func, pre, post, inv_in, inv_out);

#ifdef NODEF
		/** Get appropriate object record. */
		auto mmap_it = memory_map_.find(address);
		Assert<Memory::Exception>(mmap_it != memory_map_.end(), Memory::Failure::BAD_ADDRESS);
		ObjectRecord record = mmap_it->second;
		auto owner_list = record.owner_list_;
		auto n = owner_list.size();
		auto o_state_id = std::find(owner_list.begin(), owner_list.end(), state_id);
		Assert<Memory::Exception>(o_state_id != owner_list.end(), Memory::Failure::STATE_ID_NOT_FOUND);
		Permission permission = record.permission_;
		if (permission == Permission::READ_WRITE)
			Assert<Memory::Exception>(owner_list.size() == 1, Memory::Failure::BAD_OWNER_LIST_SIZE_ON_READ_WRITE);
		if (permission == Permission::READ_ONLY)
			Assert<Memory::Exception>(owner_list.size() > 1, Memory::Failure::BAD_OWNER_LIST_SIZE_ON_READ_ONLY);
		Assert<Memory::Exception>(record.object_ != nullptr, Memory::Failure::OBJECT_NOT_EXIST);

		/** Return apropriate object. */
		return record.object_;

		/** \invariant
		 * - owner list size cannot be changed
		 * - permission cannot be changed */
		Assert<Memory::Exception>(owner_list.size() == n, Memory::Failure::OWNER_LIST_CHANGED);
		Assert<Memory::Exception>(record.permission_ == permission, Memory::Failure::PERMISSION_CHANGED);
#endif
	}

	Address Memory::Write(Address address, StateId state_id, ObjectPtr object) {

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















