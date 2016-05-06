#ifndef __NUMBER_CACHE_HPP__
#define __NUMBER_CACHE_HPP__

// project
#include "../utils/object.hpp"

// std
#include <limits>
#include <stack>
#include <cassert>
#include <vector>

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

	IndexCache(T initial) : counter_(initial), def_counter_(initial){}
	~IndexCache() {}

	std::string ToString() {
		std::string res;
		for (auto it = cache_.begin(); it != cache_.end(); it++)
			res += std::to_string(*it) + " ";
		return res;
	}

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
			result = cache_.back();
			cache_.pop_back();
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
			assert(cache_.size() == cache_size - 1);
#endif

		return result;
	}

	void Reset () {
		counter_ = def_counter_;
		cache_.erase(cache_.begin(), cache_.end());
	}

	/** Push free index to the cache
	 * \remark
	 * - just push index to the cache
	 */
	void PushBack(T number) {
#ifdef PRE
		auto cache_size = cache_.size();
#endif

		cache_.push_back(number);

#ifdef POST
		/** \post
		 * - let n = cache size before call, if n > 0, than after call n' = n - 1
		 */
		assert(cache_.size() == cache_size + 1);
#endif
	}

private:
	T counter_;
	T def_counter_;
	std::vector<T> cache_;
};

#endif
