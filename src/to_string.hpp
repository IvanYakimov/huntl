#ifndef __TO_STRING_HPP__
#define __TO_STRING_HPP__

namespace utils {
	template <typename T>
	std::string to_string(const T& arg) {
		std::stringstream ss;
		ss << arg;
		return ss.str();
	}
}

#endif










