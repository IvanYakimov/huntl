#ifndef __CREATABLE_HPP__
#define __CREATABLE_HPP__

#include <memory>

namespace utils {
	template<typename B, typename T = B, typename... Args>
	std::shared_ptr<B> Create(Args&&... args) {
		return std::make_shared<T>(std::forward<Args>(args)...);
	}
}

#endif
