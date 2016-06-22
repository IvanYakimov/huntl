#ifndef __SORT_HPP__
#define __SORT_HPP__

#include "../utils/object.hpp"

namespace solver {
	class Sort : public Immutable {
	public:
		COMPARABLE(Sort);
		PRINTABLE(Sort);
	};
};

#endif
