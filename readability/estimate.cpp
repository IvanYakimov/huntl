#include "estimate.hpp"

using namespace interpreter;

std::smatch GetMatch(std::string line) {
	std::regex r("\"[a-zA-Z]*\"");
	std::smatch match;
	regex_search(line, match, r);
	return match;
}

int main() {
	for (std::string line; std::getline(std::cin, line); line.length() != 0) {
		//std::cout << "for: " << line << " -- ";
		for (auto match = GetMatch(line); match.size() > 0; match = GetMatch(match.suffix())) {
			//std::cout << "matched: " << match.str() << ", ";
		}
		//std::cout << std::endl;
	}
}
