#include "memory.hpp"

namespace interpreter {
	Memory::Memory() {}

	ObjectPtr Memory::Read(Address address, StateId state_id) {
		MemoryMap::iterator mmap_iter;
		ObjectRecord record;

#ifdef CONTRACT
		OwnerList owner_list;
		size_t owner_list_size;
		OwnerList::iterator onwer_list_iter;
		Permission permission;
#endif

		mmap_iter = memory_map_.find(address);	/** Find object record. */

#ifdef CONTRACT
		Assert<Exception>(mmap_iter != memory_map_.end(), Failure::BAD_ADDRESS);
#endif

		record = mmap_iter->second; /** Obtain if from iterator. */

#ifdef CONTRACT
		owner_list = record.owner_list_;
		permission = record.permission_;
		owner_list_size = owner_list.size();
		onwer_list_iter = std::find(owner_list.begin(), owner_list.end(), state_id);

		Assert<Exception>(onwer_list_iter != owner_list.end(), Failure::STATE_ID_NOT_FOUND);
		if (permission == Permission::READ_WRITE)
			Assert<Exception>(owner_list.size() == 1, Failure::BAD_OWNER_LIST_SIZE_ON_READ_WRITE);
		if (permission == Permission::READ_ONLY)
			Assert<Exception>(owner_list.size() > 1, Failure::BAD_OWNER_LIST_SIZE_ON_READ_ONLY);
		Assert<Exception>(record.object_ != nullptr, Failure::OBJECT_NOT_EXIST);
#endif

		return record.object_; /** Return appropriate object pointer. */

#ifdef CONTRACT
		Assert<Exception>(owner_list_size == record.owner_list_.size(), Failure::OWNER_LIST_CHANGED);
		Assert<Exception>(permission == record.permission_, Failure::PERMISSION_CHANGED);
#endif
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















