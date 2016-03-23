#ifndef __COMMON_TYPES_HPP__
#define __COMMON_TYPES_HPP__
#pragma once

#include <memory>
#include <string>

namespace solver {

	/**	Width of a raw integer (bitvector) */
	enum class Width {
			/** 8 bits */
			w8 = 8,
			/** 16 bits */
			w16 = 16,
			/** 32 bits */
			w32 = 32,
			/** 64 bits */
			w64 = 64
		};

	/** Converts size_t param to an appropriate width
	 * \param s - size to convert */
	Width from_size_t(size_t s);
	/** Convertis width to an apropriate int representation
	 * \param w - width to convert */
	int to_int(Width w);
	/** Maps width w to an appropriate string representation.
	 * \param w - width to map */
	std::string to_string(Width w);
};

#endif /* __COMMON_TYPES_HPP__ */
















