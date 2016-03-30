#ifndef __MEMORY_HPP__
#define __MEMORY_HPP__

#include <map>
#include <vector>
#include "../utils/object.hpp"

namespace interpreter {
	class ObjectPtr;
	using Address = uint64_t;
	using StateId = uint64_t;

	class Memory {
		enum class Permission {
				READ_ONLY,
				READ_WRITE
			};

		class ObjectRecord {
			std::vector<StateId> owner_list_;
		};

	public:

		/** Obtain an appropriate object.
		 * Check that the object's owner list contains state_id, if not - throw an exception.
		 * Return an appropriate object.
		 * \invariant
		 * - owner list size doesn't change
		 * \pre
		 * - object record with the passed addess exists
		 * - owner list contains the passed state id
		 * - if permission is READ-WRITE, than owner list size = 1
		 * - if permission is READ-ONLY, than owner list size >= 1
		 * \param address - address of the object
		 * \param state_id - state id, the state must be in object's owner list
		 */
		ObjectPtr Read(Address address, StateId state_id);

		/** Try to write object to address.
		 * \remark if permission is READ-ONLY:
		 * - Allocate memory (by Allocate ()) for new object
		 * - Write new copy of the object to the allocated object record.
		 * - Remove owner with passed state id from the owner list of old object record (it is a case if no one owns the object).
		 * - Return new address (returned by the Allocate).
		 * \remark if permission is READ-WRITE:
		 * - Replace an old object by the new one.
		 * - Return (old) address (passed as a parameter).
		 * \pre
		 * - object record with the passed addess exists
		 * - owner list contains the passed state id
		 * - if owner list size = 0, when permission must be READ-WRITE
		 * (the object record's just allocated )
		 * - if owner list size = 1, when permission can be either READ-ONLY or READ-WRITE
		 * (single owner can be able either only to read or to read and write)
		 * - if owner list size > 1, when permission must be READ-ONLY
		 * (mulptiple ownership allows only to read)
		 * \post
		 * - if permission is READ-ONLY, when owner list size = n - 1, where n - old size
		 * - if permission is READ-ONLY, wher owner list doesn't contain the passed state id
		 * - if permission is READ-WRITE when owner list size = 1
		 * - if permission is READ-WRITE, when owner list contains(only) the passed state id
		 * \param address - object's address
		 * \param state_id - state id, the state must be in object's owner list
		 * \param object - target object
		 */
		Address Write(Address address, StateId state_id, ObjectPtr object);

		/** Allocate memory for new object.
		 * Try to obtain free address from address cache
		 * If there is a free address, than
		 * - Get this address (it should be removed from the address cache)
		 * Else
		 * - Generate new address.
		 * After that:
		 * - Allocate memory for new object.
		 * - Add the passed state to the owner list of new object record (by AddOwner)
		 * - Set the object field to the nullptr.
		 * \return address of allocated object
		 */
		Address Allocate(StateId state_id);

		/** Detach memory which not used by state with the passed state id.
		 * Remove state from the object's owner list (by RemoveOwner).
		 * \pre
		 * - object record with the passed address exists
		 * - owner list contains the passed state id
		 */
		void Detach(Address address, StateId state_id);

		/** Try to share object.
		 * Set permission to READ-ONLY.
		 * Add passed state_id to the objects owner list (by AddOwner).
		 * \note As well as this operation applied, no one can write to the address until memory is free.
		 * \pre
		 * - object record with the passed address exists
		 * - if owner list size = 1 (the only one state owns this object record) than
		 * permission can be either READ-ONLY or READ-WRITE
		 * - if owner list size > 2 (two or move states own this object record) than
		 * permission must be READ-ONLY
		 * \post
		 * - owner list size = n + 1, where n - old owner list size
		 * - permission is READ-ONLY
		 * \param address - target object address
		 * \state_id - new owners id
		 */
		void Share(Address address, StateId state_id);

	private:

		/** Add owner to the object record with an appropriate address.
		 * \invariant
		 * - object record permission is READ-ONLY
		 * - object record with passed address exists
		 * \pre
		 * - owner list doesn't contain passed state id
		 * - owner list size > 0
		 * \post
		 * - owner list contains passed state id
		 * - owner list size = n + 1, where n - old size of the owner list
		 * \param address - address of the object record
		 * \param state_id - id of new object's owner
		 */
		void AddOwner(Address address, StateId state_id);

		/** Remove owner from object's owner list.
		 * Remove state id from the object's owner list.
		 * Try to remove the object record (by TryRemove).
		 * \pre
		 * - object record with the passed address exists
		 * - owner list contains the passed state id
		 * - owner list size > 1
		 * \post
		 * - owner list size = n - 1, where n - old size of the owner list
		 * \param address - address of the object
		 * \param state_id - id of removed object's owner
		 */
		void RemoveOwner(Address address, StateId state_id);

		/** Try to delete object record with an appropriate address.
		 * If owner list size = 0
		 * - Remove object, add address to the address cache
		 * Else
		 * - Do nothing
		 * \pre
		 * - object record with the passed address exists
		 * \param - address of the target object record
		 */
		void TryDelete(Address address);
	};
}

#endif /* __MEMORY_HPP__ */
