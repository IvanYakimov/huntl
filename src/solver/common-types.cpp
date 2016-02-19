#include "common-types.hpp"

namespace solver {
	namespace width {
		using namespace solver;

		Width from_size_t(size_t s) {
			switch (s) {
			case 1: return Width::w8;
			case 2: return Width::w16;
			case 4: return Width::w32;
			case 8: return Width::w64;
			}
		}

		std::string to_string(Width w) {
			switch (w) {
			case Width::w8: return "8";
			case Width::w16: return "16";
			case Width::w32: return "32";
			case Width::w64: return "64";
			}
		}
	}
}
