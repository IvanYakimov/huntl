#ifndef __NUMBER_CACHE_HPP__
#define __NUMBER_CACHE_HPP__

template <typename T>
class IndexCache {
public:
	IndexCache(T initial) : counter_(initial){}
	/** Obtain free index.
	 * \remarks
	 * if the cache contains not empty, than:
	 * - pop and return index from the cache
	 * \remarks
	 * if the cache doesn't contain any element
	 * - increment index counter
	 * - return appropriate index
	 * \pre
	 * \post
	 * - index counter != max<T>
	 * - let n = cache size before call, if n > 0, than after call n' = n - 1
	 * \invariant
	 */
	T Get() {
		T result;

		if (not cache_.empty()) {
			result = cache_.top();
			cache_.pop();
		}
		else {
			result = counter_++;
		}

		return result;
	}

	/** Push free index to the cache
	 * \remark
	 * - just push index to the cache
	 * \pre
	 * \post
	 * \invariant
	 */
	void PushBack(T number) {
		cache_.push(number);
	}

private:
	T counter_;
	std::stack<T> cache_;
};

#endif
