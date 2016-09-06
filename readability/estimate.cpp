#include "estimate.hpp"

using namespace interpreter;

std::smatch GetMatch(std::string line, std::regex r) {
	std::smatch match;
	regex_search(line, match, r);
	return match;
}

double Score(std::string src) {
	const std::regex r("[a-zA-Z]+");
	static interpreter::BigramModel model;
	auto match = GetMatch(src, r);
	auto str = match.str();
	//std::cerr << "[" << match.size() << "] ";
	//std::cerr << "{" << match.str() << "} ";
	double total_prob = 1.0;
	for (auto it = str.begin(); it != str.end(); it++) {
		auto n = std::next(it);
		if (n != str.end()) {
			//std::cerr << "(" << *it << "," << *n << ")";
			auto curr_prob = model.BigramProbability(*it, *n);
			total_prob *= curr_prob;
			//std::cerr << ": " << curr_prob << " ";
		}
	}
	return std::pow(total_prob, 1.0/src.length());
}

int main() {
	const std::regex r ("\"[a-zA-Z]*\"");
	for (std::string line; std::getline(std::cin, line); line.length() != 0) {
		std::cout << line << "; ";
		std::string cur = line;
		auto match = GetMatch(cur, r);
		while (match.size() > 0) {
			std::cout << Score(match.str()) << "; ";
			//std::cout << " +'" << match.suffix() << "' ";
			cur = match.suffix();
			match = GetMatch(cur, r);
		}
		std::cout << std::endl;
	}
}
