#ifndef __NUMBER_CACHE_HPP__
#define __NUMBER_CACHE_HPP__

// project
#include "../utils/object.hpp"

// std
#include <limits>
#include <cassert>
#include <exception>

//TODO: testing!!!
template <typename T>
class IndexCache {
public:
	class Overflow : public std::exception {
		public:
			Overflow() {}
			virtual const char* what() const noexcept {
				return "index cache overflow";
			}
	};

	IndexCache(T initial) : counter_(initial), def_counter_(initial){}
	~IndexCache() {}

	std::string ToString() {
		return "current position at: " + std::to_string(counter_) +
				" | default value is: " + std::to_string(def_counter_);
	}

	/** Get free index.
	 */
	T Get() throw (Overflow) {
		T result;

		/** \throws Overflow - if index counter overflows the max<T> */
		Assert<Overflow>(counter_ + 1 < std::numeric_limits<T>::max());

		return counter_++;
	}

	void Reset () {
		counter_ = def_counter_;
	}

private:
	T counter_;
	T def_counter_;
};

#endif
