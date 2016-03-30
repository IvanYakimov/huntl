#include "memory.hpp"

namespace interpreter {
	Memory::Memory() {}

	ObjectPtr Memory::Read(Address address, StateId state_id) {
		auto n = owner_list_.size();
		/** \invariant
		 * - owner size doesn't change */
		assert (owner_list_.size() == n);
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















