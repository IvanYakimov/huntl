#include "state.hpp"
#include "../utils/singleton.hpp"

namespace interpreter {
	using Address = uint32_t;
	using utils::Singleton;

	using MemoryPtr = std::shared_ptr<MemoryInterface>;

	class MemoryInterface : public Singleton<MemoryInterface> {
	public:
		virtual ~MemoryInterface() {}

		/** read.
		 * Return the object pointer.
		 * \param address - address of the object
		 * \param state_id - state id, the state must be in object's owner list
		 */
		virtual ObjectPtr Read(Address address, StateId state_id) = 0;

		/** copy-on-write.
		 * \param address - object's address
		 * \param state_id - state id, the state must be in object's owner list
		 * \param object - target object
		 */
		virtual Address Write(Address address, StateId state_id, ObjectPtr object) = 0;

		/** Allocate memory for new object.
		 * \param state_id - owner of a new record
		 * \return address of allocated object
		 */
		virtual Address Allocate(StateId state_id) = 0;

		/** Allocate memory for new object record and write it.
		 * \param state_id - owner of a new record
		 * \param object - object, which should be written to the new record
		 * \return - address of allocated object
		 */
		virtual Address Allocate(StateId state_id, ObjectPtr object) = 0;

		/** Free memory which not used by a state with the passed state id.
		 * \remarks
		 * - Remove state from the object's owner list (by RemoveOwner).
		 * - Try to delete object record (by TryDelete)
		 */
		virtual void Free(Address address, StateId state_id) = 0;

	};
}













