#ifndef __NUMBER_CACHE_HPP__
#define __NUMBER_CACHE_HPP__

#include "../utils/object.hpp"
#include <limits>

//TODO: testing!!!
template <typename T>
class IndexCache {
public:
	class Exception : public std::exception {
		public: virtual ~Exception () {}
	};

	class Contract : public Exception {
		public:
			Contract() {}
			virtual const char* what() const noexcept {
				return "contract failure";
			}
	};

	class Overflow : public Exception {
		public:
			Overflow() {}
			virtual const char* what() const noexcept {
				return "index cache overflow";
			}
	};

	IndexCache(T initial) : counter_(initial){}
	/** Obtain free index.
	 * \remarks
	 * if the cache contains not empty, than:
	 * - pop and return index from the cache
	 * \remarks
	 * if the cache doesn't contain any element
	 * - increment index counter
	 * - return appropriate index
	 */
	T Get() throw (Overflow) {
		T result;

#ifdef PRE
		auto cache_size = cache_.size();
#endif

		if (not cache_.empty()) {
			result = cache_.top();
			cache_.pop();
		}
		else {
			result = counter_++;
		}

		/** \throws Overflow - if index counter overflows the max<T> */
		Assert<Overflow>(counter_ < std::numeric_limits<T>::max());

#ifdef POST
		/** \post
		 * - let n = cache size before call, if n > 0, than after call n' = n - 1
		 */
		if (cache_size > 0)
			Assert<Contract>(cache_.size() == cache_size - 1);
#endif

		return result;
	}

	/** Push free index to the cache
	 * \remark
	 * - just push index to the cache
	 */
	void PushBack(T number) {
		cache_.push(number);
	}

private:
	T counter_;
	std::stack<T> cache_;
};

#endif
