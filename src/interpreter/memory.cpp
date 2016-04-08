#include "memory.hpp"

namespace interpreter {
	const char* Memory::Exception::what() const noexcept {
		static std::map<Failure, std::string> failure_map_ = {
				{Failure::RECORD_NOT_FOUND, "record not found"},
				{Failure::ACCESS_FAILURE, "access failure"},
				{Failure::OWNERSHIP_CRASH, "ownership crash"},
				{Failure::ADDRESS_CRASH, "address crash"},
				{Failure::PERMISSION_CRASH, "permission crash"},
				{Failure::MEMORY_MAP_CRASH, "memory map crash"},
				{Failure::OBJECT_PTR_CRASH, "object ptr crash"}
		};
		return ("[memory failure]: " + failure_map_[failure_]).c_str();
	}

	Memory::Record::Record() : permission_(Permission::READ_WRITE), object_(nullptr) {
		/** \post
		 * - permission is READ-WRITE by default (as state crates object record only the state owns the record)
		 * - object ptr points to nullptr (it holds hothing)
		 */
#ifdef POST
		Assert<Exception>(ReadWrite(), Failure::PERMISSION_CRASH);
		Assert<Exception>(object_ == nullptr, Failure::OBJECT_PTR_CRASH);
#endif
	}

	Memory::Record::~Record() {

	}


	void Memory::Record::AddOwner(StateId state_id) {
#ifdef PRE
		auto old_size = OwnerCount();
		/** \pre
		 * - Owner list doesn't contain passed state id
		 */
		Assert<Exception>(not OwnedBy(state_id), Failure::OWNERSHIP_CRASH);
#endif

		owner_list_.push_back(state_id);

#ifdef POST
		/**	\post
		 * - Owner list contains passed state id
		 * - Owner list size += 1
		 */
		Assert<Exception>(OwnedBy(state_id), Failure::OWNERSHIP_CRASH);
		Assert<Exception>(OwnerCount() == old_size + 1, Failure::OWNERSHIP_CRASH);
#endif
	}

	void Memory::Record::RemoveOwner(StateId state_id) {
#ifdef PRE
		auto old_size = OwnerCount();
		/** \pre
		 * - Owner list contains passed state id
		 */
		Assert<Exception>(OwnedBy(state_id), Failure::OWNERSHIP_CRASH);
#endif

		OwnerList::iterator owner_pos;
		owner_pos = std::find(owner_list_.begin(), owner_list_.end(), state_id);
		owner_list_.erase(owner_pos);

#ifdef POST
		/** \post
		 * - Owner list doesn't contain passed state id
		 * - Owner list size -= 1
		 */
		Assert<Exception>(not OwnedBy(state_id), Failure::OWNERSHIP_CRASH);
		Assert<Exception>(OwnerCount() == old_size - 1, Failure::OWNERSHIP_CRASH);
#endif
	}

	void Memory::Record::WriteObject(StateId state_id, ObjectPtr object_ptr) {
#ifdef PRE
		/** \pre
		 * - permission is NOT READ-ONLY
		 */
		Assert<Exception>(not ReadOnly(), Failure::PERMISSION_CRASH);
#endif

		object_ = object_ptr;

#ifdef POST
		/** \post
		 * - contained object pointer == passed one
		 */
		Assert<Exception>(object_ == object_ptr, Failure::OBJECT_PTR_CRASH);
#endif
	}

	ObjectPtr Memory::Record::ReadObject(StateId state_id) {
#ifdef PRE
		/** \pre
		 * - state with the passed id is owner of this object record
		 * (if not - the operation make no sense)
		 * - owner count > 0 [implied from previous]
		 * - permission is READ_WRITE	==>		owner count = 1
		 * (record with read-write permission can be accessed only by single state)
		 * - permission is READ_ONLY	==>		owner count >= 1
		 * (record with read-only permission can be accessed by multiple states)
		 */
		Assert<Exception>(OwnedBy(state_id), Failure::OWNERSHIP_CRASH);
		if (ReadWrite())
			Assert<Exception>(OwnerCount() == 1, Failure::PERMISSION_CRASH);
		if (ReadOnly())
			Assert<Exception>(OwnerCount() >= 1, Failure::PERMISSION_CRASH);
#endif

		ObjectPtr result;
		if (instanceof<Immutable>(object_))
			result = object_;
		if (instanceof<Mutable>(object_))
			result = std::dynamic_pointer_cast<Mutable>(object_)->Clone();

#ifdef POST
		/** \post
		 * - contained object is mutable 	==> 	returned pointer != holded one
		 * (mutable objects must be cloned)
		 */
		if (instanceof<Mutable>(object_))
			Assert<Exception>(result != object_, Failure::OBJECT_PTR_CRASH);
#endif

		return result;
	}

	bool Memory::Record::ReadOnly() {
		return permission_ == Permission::READ_ONLY;
	}

	bool Memory::Record::ReadWrite() {
		return permission_ == Permission::READ_WRITE;
	}

	Memory::Record::Permission Memory::Record::GetPermission() {
		return permission_;
	}

	void Memory::Record::Block() {
		permission_ = Permission::READ_ONLY;
	}

	size_t Memory::Record::OwnerCount() {
		return owner_list_.size();
	}

	bool Memory::Record::OwnedBy(StateId state_id) {
		return state_id == MASTER_ID or
				std::find(owner_list_.begin(), owner_list_.end(), state_id) not_eq owner_list_.end();
	}

	Memory::Memory() : address_cache_(INITIAL_ID), mmap_() {

	}

	Memory::~Memory() {
#ifdef PRE
		/** \pre
		 * Memory map size = 0
		 * (if memory map contains any item there are some states which use it)
		 */
		Assert<Exception>(mmap_.size() == 0, Failure::MEMORY_MAP_CRASH);
#endif
	}

	ObjectPtr Memory::Read(Address address, StateId state_id) {
		RecordPtr record;
		ObjectPtr result;

		record = GetRecord(address, state_id);
		result = record->ReadObject(state_id); // Return appropriate object pointer.

		return result;
	}

	Address Memory::Write(Address address, StateId state_id, ObjectPtr object) {
		RecordPtr record;
		Address allocated_address;
		Address result;

		record = GetRecord(address, state_id);	// Get object record

#ifdef PRE
		size_t owner_count = record->OwnerCount();
		Record::Permission permission = record->GetPermission();
		size_t mmap_size = mmap_.size();
#endif

		if (record->ReadOnly()) { // if READ-ONLY
			allocated_address = Allocate(state_id, object); // Allocate memory for new object record
			record->RemoveOwner(state_id); // Remove owner from current object record
			TryDelete(address); // Try to remove record from memory map
			result = allocated_address; // Return new address
		}
		else if (not record->ReadOnly()) { // else if READ-WRITE
			record->WriteObject(state_id, object);
			result = address;
		}

#ifdef POST
		/** \post
		 * \post permission not changed
		 * if permission is READ-ONLY (copy-on-write):
		 * - returned address != passed one (if state tries to write to a record with the READ-ONLY permission, a new record creates and its address returns as a result)
		 * - owner list size = old size - 1 (writing state obtains new record and removed from the old record's owner list)
		 * - owner list doesn't contain passed state id (writing state obtains new record and removed from the old record's owner list)
		 * - memory map size increased
		 * \post
		 * if permission is READ-WRITE (just write):
		 * - returned address = passed one (record doesn't changed, so its original address returned)
		 * - owner list size = 1 (only single state can be owner for the record with READ-WRITE permission)
		 * - owner list contain (only) passed state id (only single state can be owner for the record with READ-WRITE permission)
		 * - [skipped - see ReadObject] object record holds written object
		 */
		Assert<Exception>(record->GetPermission() == permission, Failure::PERMISSION_CRASH);
		if (record->ReadOnly()) {
			Assert<Exception>(result != address, Failure::ADDRESS_CRASH);
			Assert<Exception>(record->OwnerCount() == owner_count - 1, Failure::OWNERSHIP_CRASH);
			Assert<Exception>(not record->OwnedBy(state_id), Failure::OWNERSHIP_CRASH);
			Assert<Exception>(mmap_.size() == mmap_size + 1, Failure::MEMORY_MAP_CRASH);
		}
		else if (record->ReadWrite()) {
			Assert<Exception>(result == address, Failure::ADDRESS_CRASH);
			Assert<Exception>(record->OwnerCount() == 1, Failure::OWNERSHIP_CRASH);
			Assert<Exception>(record->OwnedBy(state_id), Failure::OWNERSHIP_CRASH);
		}
#endif

		return result;
	}

	Address Memory::Allocate(StateId state_id) {
		Address address;
		RecordPtr record;

#ifdef PRE
		size_t old_size = mmap_.size();
#endif

		address = address_cache_.Get();
		record = std::make_shared<Record>();
		record->AddOwner(state_id);
		mmap_.insert(std::make_pair(address, record));

#ifdef POST
		/** \post
		 * - memory map size > old size
		 * - permission is READ-WRITE
		 * - owner count = 1
		 * - state with the passed state id owns the record
		 */
		Assert<Exception>(mmap_.size() == old_size + 1, Failure::MEMORY_MAP_CRASH);
		Assert<Exception>(record->ReadWrite(), Failure::PERMISSION_CRASH);
		Assert<Exception>(record->OwnerCount() == 1, Failure::OWNERSHIP_CRASH);
		Assert<Exception>(record->OwnedBy(state_id), Failure::OWNERSHIP_CRASH);
#endif

		return address;
	}

	Address Memory::Allocate(StateId state_id, ObjectPtr object) {
		Address allocated = Allocate(state_id);
		Address written = Write(allocated, state_id, object);

#ifdef POST
		/** \post
		 * - allocated address = written one
		 */
		Assert<Exception>(allocated == written, Failure::ADDRESS_CRASH);
#endif

		return written;
	}

	void Memory::Free(Address address, StateId state_id) {
		RecordPtr record;
		record = GetRecord(address, state_id);
		record->RemoveOwner(state_id);
		TryDelete(address);

#ifdef POST
		/** \post
		 * - the record isn't owned by the state	(the state doens't use it)
		 */
		Assert<Exception>(not record->OwnedBy(state_id), Failure::OWNERSHIP_CRASH);
#endif
	}

	void Memory::Share(Address address, StateId owner, StateId follower) {
		MemoryMap::iterator record_pos;
		RecordPtr record;

		record = GetRecord(address, owner);

#ifdef PRE
		auto owner_count = record->OwnerCount();
		/** \pre
		 * - permission = READ-WRITE ==> owner count = 1	(record with read-write permission can be owned only by one state)
		 * - permission = READ-ONLY	==> owner count >= 1	(record with read-only permission can be owned by many states)
		 */
		if (record->ReadWrite())
			Assert<Exception>(owner_count == 1, Failure::OWNERSHIP_CRASH);
		if (record->ReadOnly())
			Assert<Exception>(owner_count >= 1, Failure::OWNERSHIP_CRASH);
#endif

		record->Block();
		record->AddOwner(follower);

#ifdef POST
		/** \post
		 * - permission is READ-ONLY				(shared record must be read-only)
		 * - owner counter increased				(new owner added to the record owner list)
		 * - the record is owned by the follower	(new owner added to the record owner list)
		 */
		Assert<Exception>(record->ReadOnly(), Failure::PERMISSION_CRASH);
		Assert<Exception>(record->OwnerCount() == owner_count + 1, Failure::OWNERSHIP_CRASH);
		Assert<Exception>(record->OwnedBy(follower), Failure::OWNERSHIP_CRASH);
#endif
	}

	void Memory::TryDelete(Address address) {
		/** If owner list size = 0
		 * - Remove object, add return the address back to the address cache
		 * Else
		 * - Do nothing
		 */

		RecordPtr record = GetRecord(address, MASTER_ID);

#ifdef PRE
		size_t owner_count = record->OwnerCount();
		size_t mmap_size = mmap_.size();
#endif

		if (record->OwnerCount() == 0) {
			mmap_.erase(address);
			address_cache_.PushBack(address);
		}

#ifdef POST
		/** \post owner count == 0	==>
		 * - mmap size -= 1
		 * - mmap doesn't contain record with the passed address
		 * \post owner count > 0 ==>
		 * - mmap size hasn't been changed
		 * - mmap contains record with the passed address
		 */
		if (owner_count == 0) {
			Assert<Exception>(mmap_.size() == mmap_size - 1, Failure::MEMORY_MAP_CRASH);
			Assert<Exception>(mmap_.find(address) == mmap_.end(), Failure::MEMORY_MAP_CRASH);
		}
		else {
			Assert<Exception>(mmap_.size() == mmap_size, Failure::MEMORY_MAP_CRASH);
			Assert<Exception>(mmap_.find(address) != mmap_.end(), Failure::MEMORY_MAP_CRASH);
		}
#endif
	}

	Memory::RecordPtr Memory::GetRecord(Address address, StateId state_id) {
		MemoryMap::iterator mmap_iter;
		RecordPtr record;

		mmap_iter = mmap_.find(address);	// Find object record.
		record = mmap_iter->second; // Obtain if from iterator.

#ifdef CONTRACT
		/** \pre
		 * - object record with the passed addess exists
		 * (if not - there is no appropriate record available)
		 * - state id != master ==> state with the passed state id has access the record
		 * (otherwise - access error)
		 */
		Assert<Exception>(mmap_iter != mmap_.end(), Failure::RECORD_NOT_FOUND);
		Assert<Exception>(record->OwnedBy(state_id), Failure::ACCESS_FAILURE);
#endif

		return record;
	}
}















