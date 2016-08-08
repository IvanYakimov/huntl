#ifndef __RAM_ADDRESS_HPP__
#define __RAM_ADDRESS_HPP__

namespace memory {
	using RamAddress = std::uint64_t;
	using Alignment = std::uint16_t;
	const unsigned kDefAlign = 4;
	const unsigned kWordSize = 64;
};

#endif
