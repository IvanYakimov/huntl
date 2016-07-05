#ifndef __INSTANCE_OF_HPP__
#define __INSTANCE_OF_HPP__

#include <memory>

namespace utils {
	/** Check whether its param is instance of T.
	 * It is something like Java instanceof keyword.
	 * \note In most cases it should be applied only for instances of (smart pointers to) classes,
	 * derived (transitively) from Object
	 * \param obj - target object
	 * \tparam T - target type
	 * \tparam U - type of obj (can be skipped)
	 * \attention it works only for std::shared_pointer-s!
	 * \see Object
	 */
	template<class T, class U>
	bool instanceof( const std::shared_ptr<U>& obj ) noexcept {
		if (std::dynamic_pointer_cast<T>(obj) != nullptr)
			return true;
		else
			return false;
	}
}

#endif
