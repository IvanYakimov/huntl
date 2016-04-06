#include "memory.hpp"

namespace interpreter {
	void Memory::ObjectRecord::AddOwner(StateId state_id) {
#ifdef PRE
		auto old_size = OwnerCount();
		/** \pre
		 * - Owner list doesn't contain passed state id
		 */
		Assert<Exception>(not IsOwner(state_id), Failure::OWNER_LIST_CRASH);
#endif

		owner_list_.push_back(state_id);

#ifdef POST
		/**	\post
		 * - Owner list contains passed state id
		 * - Owner list size += 1
		 */
		Assert<Exception>(IsOwner(state_id), Failure::OWNER_LIST_CRASH);
		Assert<Exception>(OwnerCount() == old_size + 1, Failure::OWNER_LIST_CRASH);
#endif
	}

	void Memory::ObjectRecord::RemoveOwner(StateId state_id) {
#ifdef PRE
		auto old_size = OwnerCount();
		/** \pre
		 * - Owner list contains passed state id
		 */
		Assert<Exception>(IsOwner(state_id), Failure::OWNER_LIST_CRASH);
#endif

		OwnerList::iterator owner_pos;
		owner_pos = std::find(owner_list_.begin(), owner_list_.end(), state_id);
		owner_list_.erase(owner_pos);

#ifdef POST
		/** \post
		 * - Owner list doesn't contain passed state id
		 * - Owner list size -= 1
		 */
		Assert<Exception>(not IsOwner(state_id), Failure::OWNER_LIST_CRASH);
		Assert<Exception>(OwnerCount() == old_size - 1, Failure::OWNER_LIST_CRASH);
#endif
	}

	void Memory::ObjectRecord::WriteObject(StateId state_id, ObjectPtr object_ptr) {
#ifdef PRE
		/** \pre
		 * - permission is NOT READ-ONLY
		 */
		Assert<Exception>(not IsReadOnly(), Failure::PERMISSION_CRASH);
#endif

		object_ = object_ptr;

#ifdef POST
		/** \post
		 * - contained object pointer == passed one
		 */
		Assert<Exception>(object_ == object_ptr, Failure::OBJECT_PTR_CRASH);
#endif
	}

	ObjectPtr Memory::ObjectRecord::ReadObject(StateId state_id) {
#ifdef PRE
		/** \pre
		 * - state with the passed id is owner of this object record
		 * (if not - the operation make no sense)
		 * - owner count > 0 [implied from previous]
		 * - permission is READ_WRITE	==>		owner count = 1
		 * (record with read-write permission can be accessed only by the single state)
		 * - permission is READ_ONLY	==>		owner count >= 1
		 * (record with read-only permission can be accessed by multiple states)
		 */
		Assert<Exception>(IsOwner(state_id), Failure::OWNER_LIST_CRASH);
		if (IsReadWrite())
			Assert<Exception>(OwnerCount() == 1, Failure::PERMISSION_CRASH);
		if (IsReadOnly())
			Assert<Exception>(OwnerCount() >= 1, Failure::PERMISSION_CRASH);
#endif

		ObjectPtr result;
		if (instanceof<Immutable>(object_))
			result = object_;
		if (instanceof<Mutable>(object_))
			result = std::dynamic_pointer_cast<Mutable>(object_)->Clone();

#ifdef POST
		/** \post
		 * - if contained object is mutable: returned pointer != holded one
		 */
		if (instanceof<Mutable>(object_))
			Assert<Exception>(result != object_, Failure::OBJECT_PTR_CRASH);
#endif

		return result;
	}

	bool Memory::ObjectRecord::IsReadOnly() {
		return permission_ == Permission::READ_ONLY;
	}

	bool Memory::ObjectRecord::IsReadWrite() {
		return permission_ == Permission::READ_WRITE;
	}

	void Memory::ObjectRecord::SetReadOnly() {
		permission_ = Permission::READ_ONLY;
	}

	size_t Memory::ObjectRecord::OwnerCount() {
		return owner_list_.size();
	}

	bool Memory::ObjectRecord::IsOwner(StateId state_id) {
		return std::find(owner_list_.begin(), owner_list_.end(), state_id) != owner_list_.end();
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

#ifdef PRE
		/** \pre
		 * - object record with the passed addess exists
		 * - state with the passed state id has access the record
		 */
#endif

		mmap_iter = mmap_.find(address);	// Find object record.
		record = mmap_iter->second; // Obtain if from iterator.

#ifdef POST
		/**
		 *
		 */
#endif

		return record;
	}
}















