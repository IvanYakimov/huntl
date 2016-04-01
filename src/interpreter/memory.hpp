#ifndef __MEMORY_HPP__
#define __MEMORY_HPP__

#include <map>
#include <vector>
#include <algorithm>
#include <tuple>
#include "../utils/object.hpp"

namespace interpreter {
	using Address = uint64_t;
	using StateId = uint64_t;

	/** Implementation of copy-on-write idiom for memory management on object-level.
	 * It is similar to the UNIX copy-on-write algorithm for managing memory pages among several processes.
	 * It uses mechanism similar to C++ std::shared_ptr for garbage collection.
	 * \see Modern Operating Systems (4th Edition) 4th Edition by Andrew S. Tanenbaum (Author), Herbert Bos  (Author)
	 * \see 2014. Effective Modern C++: 42 Specific Ways to Improve Your Use of C++11 and C++14. ISBN 1-491-90399-6
	 */
	class Memory {
	public:
		enum class Failure {
					BAD_ADDRESS,
					STATE_ID_NOT_FOUND,
					OWNER_LIST_CHANGED,
					OWNER_LIST_NOT_CHANGED,
					BAD_OWNER_LIST_SIZE,
					PERMISSION_CHANGED,
					OBJECT_NOT_EXIST,
					BAD_OWNER_LIST_SIZE_ON_READ_ONLY,
					BAD_OWNER_LIST_SIZE_ON_READ_WRITE,
					BAD_RETURN_ADDRESS_ON_READ_ONLY,
					ADDRESS_CHANGED_ON_INITIALIZATION,
					ADDRESS_CHANGED_ON_WRITING
				};

		class Exception : public std::exception {
		public: Exception (Failure failure) : failure_(failure) {}
		private: Failure failure_;
		};

	private:
		struct ObjectRecord;
		enum class Permission;

		using OwnerList = std::vector<StateId>;
		using MemoryMap = std::map<Address, ObjectRecord>;

		enum class Permission {
				READ_ONLY,
				READ_WRITE
			};

		struct ObjectRecord {
			std::vector<StateId> owner_list_;
			Permission permission_;
			ObjectPtr object_;
		};

	public:

		Memory();

		/** Obtain an appropriate object.
		 * Return the object pointer.
		 * \invariant
		 * - owner list size cannot be changed
		 * - permission cannot be changed
		 * \pre
		 * - object record with the passed addess exists
		 * - owner list contains the passed state id
		 * - if permission is READ-WRITE, than owner list size = 1
		 * - if permission is READ-ONLY, than owner list size >= 1
		 * - object contains data (not null)
		 * \post
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
		 * - if owner list size = 0, than permission must be READ-WRITE
		 * (the object record's just allocated )
		 * - if owner list size = 1, than permission can be either READ-ONLY or READ-WRITE
		 * (single owner can be able either only to read or to read and write)
		 * - if owner list size > 1, than permission must be READ-ONLY
		 * (mulptiple ownership allows only to read)
		 * \post
		 * if permission is READ-ONLY, than:
		 * - returned address != passed one
		 * - allocated address = written address
		 * - list size = n - 1, where n - old size
		 * - [skipped] owner list doesn't contain the passed state id
		 * \post
		 * else, if permission is READ-WRITE, than:
		 * - returned address = passed one
		 * - owner list size = 1
		 * - [skipped] owner list contains(only) the passed state id
		 * \invariant
		 * - object record, if exists, holds not null pointer
		 * - permission cannot be changed
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

	private:
		std::map <Address, ObjectRecord> memory_map_;
	};
}

#endif /* __MEMORY_HPP__ */














