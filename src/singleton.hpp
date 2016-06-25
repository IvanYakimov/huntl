#ifndef __SINGLETON_HPP__
#define __SINGLETON_HPP__

#include <memory>

namespace utils {
	template<class T, typename... Args>
	std::shared_ptr<T> GetInstance(Args&&... args) {
		static std::shared_ptr<T> instance_ = nullptr;
		if (instance_ == nullptr)
			return std::make_shared<T>(std::forward<Args>(args)...);
		else
			return instance_;
	}
}

#endif
