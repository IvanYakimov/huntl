#include "memory.hpp"

namespace interpreter {
	Memory::Memory() {}

	ObjectPtr Memory::Read(Address address, StateId state_id) {
		MemoryMap::iterator mmap_iter;
		ObjectRecord record;
		ObjectPtr result;

//#ifdef CONTRACT
		OwnerList owner_list;
		size_t owner_list_size;
		OwnerList::iterator onwer_list_iter;
		Permission permission;
//#endif

		mmap_iter = memory_map_.find(address);	// Find object record.

//#ifdef CONTRACT
		Assert<Exception>(mmap_iter != memory_map_.end(), Failure::RECORD_NOT_FOUND);
//#endif

		record = mmap_iter->second; // Obtain if from iterator.

//#ifdef CONTRACT
		owner_list = record.owner_list_;
		permission = record.permission_;
		owner_list_size = owner_list.size();
		onwer_list_iter = std::find(owner_list.begin(), owner_list.end(), state_id);

		Assert<Exception>(onwer_list_iter != owner_list.end(), Failure::OWNER_NOT_FOUND);
		if (permission == Permission::READ_WRITE)
			Assert<Exception>(owner_list.size() == 1, Failure::INVALID_OWNER_LIST);
		if (permission == Permission::READ_ONLY)
			Assert<Exception>(owner_list.size() > 1, Failure::INVALID_OWNER_LIST);
		Assert<Exception>(record.object_ != nullptr, Failure::OBJECT_NOT_EXIST);
//#endif

		result = record.object_; // Return appropriate object pointer.

//#ifdef CONTRACT
		Assert<Exception>(owner_list_size == record.owner_list_.size(), Failure::OWNER_LIST_CRASH);
		Assert<Exception>(permission == record.permission_, Failure::PERMISSION_CRASH);
//#endif

		return result;
	}

	Address Memory::Write(Address address, StateId state_id, ObjectPtr object) {
		MemoryMap::iterator mmap_iter;
		ObjectRecord record;
		Permission permission;
		Address allocated_address;
		Address written_address;
		Address result;

		OwnerList owner_list;
		size_t owner_list_size;
		OwnerList::iterator owner_list_iter;

		mmap_iter = memory_map_.find(address); // Find object record

		// precondition
		Assert<Exception>(mmap_iter != memory_map_.end(), Failure::OBJECT_NOT_EXIST);

		record = mmap_iter->second;	// Get object record
		permission = record.permission_; // Get permission

		owner_list = record.owner_list_;
		owner_list_size = owner_list.size();
		owner_list_iter = std::find(owner_list.begin(), owner_list.end(), state_id);

		// precondition
		Assert<Exception>(owner_list_iter != owner_list.end(), Failure::OWNER_NOT_FOUND);
		if (owner_list_size == 0) {
			Assert<Exception>(permission == Permission::READ_WRITE, Failure::INVALID_PERMISSION);
		}
		else if (owner_list_size == 1) {
			// Permission can be  be either READ-ONLY or READ-WRITE - no assertion needed
		}
		else if (owner_list_size > 1) {
			Assert<Exception>(permission == Permission::READ_ONLY, Failure::INVALID_PERMISSION);
		}


		if (permission == Permission::READ_ONLY) { // if READ-ONLY
			allocated_address = Allocate(state_id); // Allocate memory for new object record
			written_address = Write(allocated_address, state_id, object); // Write new object to allocated memory
			RemoveOwner(address, state_id); // Remove owner from current object record
			result = allocated_address; // Return new address

			// postconditions
			Assert<Exception>(result != address, Failure::RETURN_CRASH);
			Assert<Exception>(allocated_address == written_address, Failure::RETURN_CRASH);
			Assert<Exception>(owner_list.size() == owner_list_size - 1, Failure::OWNER_LIST_CRASH);
		}
		else if (permission == Permission::READ_WRITE) { // else if READ-WRITE
			record.object_ = object;
			result = allocated_address;

			// postconditions
			Assert<Exception>(result == address, Failure::ADDRESS_CRASH);
			Assert<Exception>(owner_list.size() == 1, Failure::OWNER_LIST_CRASH);
		}

		// invariants
		Assert<Exception>(permission == record.permission_, Failure::PERMISSION_CRASH);

		return result;
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















