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

	void Memory::ObjectRecord::WriteObject(StateId state_id, ObjectPtr object_ptr) {

	}

	ObjectPtr Memory::ObjectRecord::ReadObject(StateId state_id) {
		if (instanceof<Immutable>(object_))
			return object_;
		else if (instanceof<Mutable>(object_))
			return std::dynamic_pointer_cast<Mutable>(object_)->Clone();
		else
			throw std::logic_error("not implemented");
	}

	bool Memory::ObjectRecord::IsReadOnly() {
		return permission_ == Permission::READ_ONLY;
	}

	void Memory::ObjectRecord::SetReadOnly() {
		permission_ = Permission::READ_ONLY;
	}

	Memory::Memory() {}
	Memory::~Memory() {
		/** \pre
		 * Memory map size = 0
		 */
	}

	ObjectPtr Memory::Read(Address address, StateId state_id) {
		ObjectRecord record;
		ObjectPtr result;

		record = GetRecord(address, state_id);
		result = record.ReadObject(state_id); // Return appropriate object pointer.

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
			record.WriteObject(state_id, object);
			result = address;
		}

		return result;
	}

	Address Memory::Allocate(StateId state_id) {
		Address address = addr_cache_.Get();
		ObjectRecord record;
		record.AddOwner(state_id);
		mmap_.insert(std::make_pair(address, record));
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
		throw std::logic_error("not implemented");
	}

	Memory::ObjectRecord Memory::GetRecord(Address address, StateId state_id) {
		MemoryMap::iterator mmap_iter;
		ObjectRecord record;

		/** \pre
		 * - object record with the passed addess exists
		 * - state with the passed state id has access the record
		 */

		mmap_iter = mmap_.find(address);	// Find object record.
		record = mmap_iter->second; // Obtain if from iterator.
		return record;
	}
}















