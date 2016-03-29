#ifndef __MEMORY_HPP__
#define __MEMORY_HPP__

#include <map>

namespace interpreter {
	class ObjectPtr;
	class Address;
	class Type;
	class Memory {
		/** Obtain an appropriate object.
		 * \param adr - address of the object
		 */
		ObjectPtr Read(Address adr);
		/** Try to write object to address.
		 * If the field with address adr is READ-ONLY, than
		 * - Allocate memory for new object, clone object and write new copy to address of the allocated memory.
		 * - Decrease owners counter for the original object.
		 * - Try to free memory from original object's address (it is a case when no one uses this READ-ONLY object).
		 * - Return new address.
		 * Else
		 * - Replace an old object to the new one (obj).
		 * - Return old address.
		 * 	\prarm adr - object's address
		 * 	\param obj - target object
		 */
		Address Write(Address adr, ObjectPtr obj);
		/** Try to free memory with adr address.
		 * Checks owners counter.
		 * If it contains 0, than
		 * - Remove object, add adr to the address cache
		 * Else
		 * - Do nothing
		 */
		void TryFree(Address adr);
		/** Allocate memory for new object.
		 * Try to obtain free address from address cache
		 * If there is a free address, than
		 * - Get this address (it should be removed from the address cache)
		 * Else
		 * - Generate new free address.
		 * After that:
		 * - Allocate memory for new object.
		 * - Set permission to READ-WRITE.
		 * - Set object field to nullptr.
		 * \return address of allocated object
		 */
		Address Allocate();
		/** Set permission to READ-ONLY.
		 * After this operation is applied, no one can write to the address until memory is free.
		 * \param adr - target memory cell address
		 */
		void Block(Address adr);
	};
}

#endif /* __MEMORY_HPP__ */
