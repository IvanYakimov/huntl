#ifndef __BIGRAM_MODEL_HPP__
#define __BIGRAM_MODEL_HPP__

#include <cassert>

namespace interpreter {
	class BigramModel {
	public:
		BigramModel();
		static char UpperByUpper(char symbol);
		static char LowerByLower(char symbol);
		static char UpperByLower(char symbol);
		static char LowerByUpper(char symbol);
		float lower_by_lower[26][26];
	};
}

#endif
