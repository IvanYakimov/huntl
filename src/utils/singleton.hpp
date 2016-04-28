#ifndef __SINGLETON_HPP__
#define __SINGLETON_HPP__

#include <memory>
#include <cassert>

#include "../utils/object.hpp"

namespace utils {
	/** Singleton pattern implementation. There is only one instance of T in run-time,
	 * to get (smart pointer to) it use Get () method.
	 * \tparam T class to be "singletoned"
	 */
	template <class T>
	class Singleton {
	public:
		virtual ~Singleton(){}
		/**	Returns (smart pointer to) instance T. At the first time it creates new instance,
		 * and always returns it in futher function calls. */
		static std::shared_ptr<T> Get() {
			static std::shared_ptr<T> singleton_ (nullptr);
			if (singleton_ == nullptr)
				return singleton_ = std::make_shared<T>();
			else
				return singleton_;
		}
	};

	template <class T, class B>
	class VirtualSingleton : public B {
	public:
		virtual ~VirtualSingleton(){}
		/**	Returns (smart pointer to) instance T. At the first time it creates new instance,
		 * and always returns it in futher function calls. */
		static std::shared_ptr<B> Get() {
			static std::shared_ptr<B> singleton_ (nullptr);
			if (singleton_ == nullptr) {
				singleton_ = std::make_shared<T>();
				assert (instanceof<B>(singleton_));
				return singleton_;
			}
			else
				return singleton_;
		}
	};
}

#endif /* __SINGLETON_HPP__ */
