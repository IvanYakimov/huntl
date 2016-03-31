#include "memory.hpp"

namespace interpreter {
	Memory::Memory() {}

	ObjectPtr Memory::Read(Address address, StateId state_id) {
		/** \pre
		 * - object record with the passed addess exists
		 * - owner list contains the passed state id
		 * - if permission is READ-WRITE, than owner list size = 1
		 * - if permission is READ-ONLY, than owner list size >= 1
		 * - object contains data (not null)
		 */

		/** Get appropriate object record. */
		auto it = memory_map_.find(address);
		Assert<Memory::Exception>(it != memory_map_.end(), Memory::Failure::BAD_ADDRESS);
		ObjectRecord record = it->second;
		auto olist = record.owner_list_;
		auto n = olist.size();
		auto olist_it = std::find(olist.begin(), olist.end(), state_id);
		Assert<Memory::Exception>(olist_it != olist.end(), Memory::Failure::STATE_ID_NOT_FOUND);
		Permission permission = record.permission_;
		if (permission == Permission::READ_WRITE)
			Assert<Memory::Exception>(olist.size() == 1, Memory::Failure::BAD_OWNER_LIST_SIZE_ON_READ_WRITE);
		if (permission == Permission::READ_ONLY)
			Assert<Memory::Exception>(olist.size() > 1, Memory::Failure::BAD_OWNER_LIST_SIZE_ON_READ_ONLY);
		Assert<Memory::Exception>(record.object_ != nullptr, Memory::Failure::OBJECT_NOT_EXIST);

		/** Return apropriate object. */
		return record.object_;

		/** \invariant
		 * - owner list size cannot be changed
		 * - permission cannot be changed */
		Assert<Memory::Exception>(olist.size() == n, Memory::Failure::OWNER_LIST_CHANGED);
		Assert<Memory::Exception>(record.permission_ == permission, Memory::Failure::PERMISSION_CHANGED);
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















