#ifndef __SINGLETON_HPP__
#define __SINGLETON_HPP__

#include <memory>
#include <cassert>

namespace utils {
	///TODO: testing
	template <class T, typename... Args>
	static std::shared_ptr<T> GetInstance(Args&&... args) {
		static std::shared_ptr<T> instance_ = nullptr;
		if (instance_ == nullptr)
			instance_ = std::make_shared<T>(std::forward<Args>(args)...);
		assert (instance_ != nullptr);
		return instance_;
	}
}

#endif
