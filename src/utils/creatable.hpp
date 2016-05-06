#ifndef __CREATABLE_HPP__
#define __CREATABLE_HPP__

namespace utils {
	//TODO: rename to virtual_singleton
	template <class T, class B>
	class creatable : public shared<T, B> {
	public:
		virtual ~creatable() {}
		/**	Returns (smart pointer to) instance T. At the first time it creates new instance,
		 * and always returns it in futher function calls. */
		static std::shared_ptr<B> Create() {
			return std::make_shared<T>();
		}
	};
}

#endif
