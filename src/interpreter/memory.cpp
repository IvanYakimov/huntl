#include "memory.hpp"

namespace interpreter {
	void Memory::ObjectRecord::AddOwner(StateId state_id) {
		owner_list_.push_back(state_id);
	}

	void Memory::ObjectRecord::RemoveOwner(StateId state_id) {
		OwnerList::iterator owner_pos;
		owner_pos = std::find(owner_list_.begin(), owner_list_.end(), state_id);
		owner_list_.erase(owner_pos);
	}

	bool Memory::ObjectRecord::IsReadOnly() {
		return permission_ == Permission::READ_ONLY;
	}

	void Memory::ObjectRecord::SetReadOnly() {
		permission_ = Permission::READ_ONLY;
	}

	Memory::Memory() {}

	ObjectPtr Memory::Read(Address address, StateId state_id) {
		ObjectRecord record;
		ObjectPtr result;

		record = GetRecord(address, state_id);
		result = record.object_; // Return appropriate object pointer.

		return result;
	}

	Address Memory::Write(Address address, StateId state_id, ObjectPtr object) {

		ObjectRecord record;
		Address allocated_address;
		Address result;

		record = GetRecord(address, state_id);	// Get object record

		if (record.IsReadOnly()) { // if READ-ONLY
			allocated_address = Allocate(state_id, object); // Allocate memory for new object record
			record.RemoveOwner(state_id); // Remove owner from current object record
			result = allocated_address; // Return new address
		}
		else if (not record.IsReadOnly()) { // else if READ-WRITE
			record.object_ = object;
			result = address;
		}

		return result;
	}

	Address Memory::Allocate(StateId state_id) {
		Address address = address_cache_.Get();
		ObjectRecord record;
		record.AddOwner(state_id);
		memory_map_.insert(std::make_pair(address, record));
		return address;
	}

	Address Memory::Allocate(StateId state_id, ObjectPtr object) {
		Address allocated = Allocate(state_id);
		Address written = Write(allocated, state_id, object);
		return written;
	}

	void Memory::Free(Address address, StateId state_id) {
		ObjectRecord record = GetRecord(address, state_id);
		record.RemoveOwner(state_id);
		TryDelete(address);
	}

	void Memory::Share(Address address, StateId state_id) {
		MemoryMap::iterator record_pos;
		ObjectRecord record;
		OwnerList owner_list;
		OwnerList::iterator owner_pos;

		record = GetRecord(address, state_id);
		record.SetReadOnly();
		record.AddOwner(state_id);
	}

	void Memory::TryDelete(Address address) {

	}

	Memory::ObjectRecord Memory::GetRecord(Address address, StateId state_id) {
		MemoryMap::iterator mmap_iter;
		ObjectRecord record;
		/** \pre
		 * - object record with the passed addess exists
		 * - state with the passed state id has access the record
		 */

		mmap_iter = memory_map_.find(address);	// Find object record.
		record = mmap_iter->second; // Obtain if from iterator.
		return record;
	}
}















