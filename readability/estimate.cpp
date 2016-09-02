#include "estimate.hpp"

using namespace interpreter;

int main() {
	std::string line;
	for (std::string line; std::getline(std::cin, line); line.length() != 0) {
		std::cout << line << std::endl;
	}
}
