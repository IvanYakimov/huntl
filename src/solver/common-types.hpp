#ifndef __COMMON_TYPES_HPP__
#define __COMMON_TYPES_HPP__
#pragma once

#include <memory>
#include <string>

//TODO: move to /src/solver directory
namespace solver {
	//-------------------------------------------
	// Basic
	enum class Width {
			w8 = 8,
			w16 = 16,
			w32 = 32,
			w64 = 64
		};

	namespace width {
		using namespace solver;
		Width from_size_t(size_t s);
		std::string to_string(Width w);
	}
};

#endif /* __COMMON_TYPES_HPP__ */
















