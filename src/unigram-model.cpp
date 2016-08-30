#include "unigram-model.hpp"

namespace interpreter {
	char UnigramModel::GetLower() {
		std::random_device rd;
		std::mt19937 gen(rd());
		std::uniform_int_distribution<char> dis('a', 'z');
		char result = dis(gen);
		assert(std::islower(result));
		return result;
	}
}
