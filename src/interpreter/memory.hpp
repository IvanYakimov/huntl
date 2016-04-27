#ifndef __MEMORY_HPP__
#define __MEMORY_HPP__

#include <map>
#include <vector>
#include <algorithm>
#include <stack>
#include "../utils/object.hpp"
#include "../utils/index-cache.hpp"
#include "memory-interface.hpp"
#include "state.hpp"

//TODO: move all memory (and display) classes to memory namespace
namespace interpreter {
	/** Implementation of copy-on-write idiom for memory management on object-level.
	 * It is similar to the UNIX copy-on-write algorithm for managing memory among several processes.
	 * It uses mechanism similar to C++ std::shared_ptr for garbage collection.
	 * \see Modern Operating Systems (4th Edition) 4th Edition by Andrew S. Tanenbaum (Author), Herbert Bos  (Author)
	 * \see 2014. Effective Modern C++: 42 Specific Ways to Improve Your Use of C++11 and C++14. ISBN 1-491-90399-6
	 */
	class Memory final : public MemoryInterface {
		static const int MASTER_ID = 0;
		static const int INITIAL_ID = 1;
	public:
		enum class Failure {
					RECORD_NOT_FOUND,
					ACCESS_FAILURE,
					OWNERSHIP_CRASH,
					ADDRESS_CRASH,
					PERMISSION_CRASH,
					MEMORY_MAP_CRASH,
					OBJECT_PTR_CRASH
				};

		class Exception : public std::exception {
		public:
			Exception (Failure failure) : failure_(failure) {}
			virtual const char* what() const noexcept;
		private:
			Failure failure_;
		};

	private:
		class Record;
		using RecordPtr = std::shared_ptr<Record>;

		using OwnerList = std::vector<StateId>;
		using MemoryMap = std::map<Address, RecordPtr>;

		class Record {
		public:
			enum class Permission {
				READ_ONLY,
				READ_WRITE
			};

			Record();
			~Record();
			ObjectPtr ReadObject(StateId state_id);
			void WriteObject(StateId state_id, ObjectPtr object_ptr);
			void AddOwner(StateId state_id);
			void RemoveOwner(StateId state_id);
			bool ReadOnly();
			bool ReadWrite();
			Permission GetPermission();
			void Block();
			size_t OwnerCount();
			bool OwnedBy(StateId state_id);

		private:
			std::vector<StateId> owner_list_;
			Permission permission_;
			ObjectPtr object_;
		};

	public:

		Memory();
		virtual ~Memory();

		/** read.
		 * Return the object pointer.
		 * \param address - address of the object
		 * \param state_id - state id, the state must be in object's owner list
		 */
		virtual ObjectPtr Read(Address address, StateId state_id);

		/** copy-on-write.
		 * \param address - object's address
		 * \param state_id - state id, the state must be in object's owner list
		 * \param object - target object
		 */
		virtual Address Write(Address address, StateId state_id, ObjectPtr object);

		/** Allocate memory for new object.
		 * \param state_id - owner of a new record
		 * \return address of allocated object
		 */
		virtual Address Allocate(StateId state_id);

		/** Allocate memory for new object record and write it.
		 * \param state_id - owner of a new record
		 * \param object - object, which should be written to the new record
		 * \return - address of allocated object
		 */
		virtual Address Allocate(StateId state_id, ObjectPtr object);

		/** Free memory which not used by a state with the passed state id.
		 * \remarks
		 * - Remove state from the object's owner list (by RemoveOwner).
		 * - Try to delete object record (by TryDelete)
		 */
		virtual void Free(Address address, StateId state_id);

		/** Try to share object.
		 * \remarks
		 * - Set permission to READ-ONLY.
		 * - Add passed state_id to the objects owner list (by AddOwner).
		 * \note As well as this operation applied, no one can write to the address until memory is free.
		 * \param address - target object address
		 * \state_id - new owners id
		 */
		virtual void Share(Address address, StateId owner, StateId follower);

	private:
		Record GetRecord(Address address);

		/** Try to delete object record with an appropriate address.
		 * \param - address of the target object record
		 */
		void TryDelete(Address address);

		/** Get appropriate object record.
		 */
		RecordPtr GetRecord(Address address, StateId state_id);

	private:
		//TODO: extract MemoryMap class
		MemoryMap mmap_;
		IndexCache<Address> address_cache_;
	};
}

#endif /* __MEMORY_HPP__ */














