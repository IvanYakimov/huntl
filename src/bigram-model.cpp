#include "bigram-model.hpp"

namespace interpreter {
	char BigramModel::UpperByUpper(char symbol) {
		assert ((symbol >= 'A') and (symbol <= 'Z'));
		switch (symbol) {
		case 'A':
		case 'B':
		case 'C':
		case 'D':
		case 'E':
		case 'F':
		case 'G':
		case 'H':
		case 'I':
		case 'J':
		case 'K':
		case 'L':
		case 'M':
		case 'N':
		case 'O':
		case 'P':
		case 'Q':
		case 'R':
		case 'S':
		case 'T':
		case 'U':
		case 'V':
		case 'W':
		case 'X':
		case 'Y':
		case 'Z':
		default:
			assert (false and "missed symbol");
		};
	}

	char BigramModel::LowerByLower(char symbol) {
		assert ((symbol >= 'a') and (symbol <= 'z'));
		switch (symbol) {
		case 'a':	return 'n';		// 13.8
		case 'b':	return 'a';		// 11.4
		case 'c':	return 'a';		// 12.4
		case 'd':	return 'e';		// 12.8
		case 'e':	return 'a';		// 12.8
		case 'f':	return 'o';		// 12.4
		case 'g':	return 'e';		// 12.2
		case 'h':	return 'a';		// 13.1
		case 'i':	return 's';		// 13.1 (also t)
		case 'j':	return 'u';		// 10.1
		case 'k':	return 'e';		// 11.9
		case 'l':	return 'e';		// 12.9
		case 'm':	return 'e';		// 12.9
		case 'n':	return 'g';		// 13.2
		case 'o':	return 'n';		// 13.6
		case 'p':	return 'e';		// 12.3
		case 'q':	return 'i';		// 6.64
		case 'r':	return 'e';		// 13.7
		case 's':	return 't';		// 13.2
		case 't':	return 'h';		// 14.2
		case 'u':	return 't';		// 12.4
		case 'v':	return 'e';		// 12.9
		case 'w':	return 'i';		// 12.1 (also a)
		case 'x':	return 't'; 	// 9.75
		case 'y':	return 'e';		// 11.4
		case 'z':	return 'e';		// 10.1
		default:
			assert (false and "missed symbol");
		};
	}

	char BigramModel::UpperByLower(char symbol) {
		assert ((symbol >= 'A') and (symbol <= 'Z'));
		switch (symbol) {
		case 'A':
		case 'B':
		case 'C':
		case 'D':
		case 'E':
		case 'F':
		case 'G':
		case 'H':
		case 'I':
		case 'J':
		case 'K':
		case 'L':
		case 'M':
		case 'N':
		case 'O':
		case 'P':
		case 'Q':
		case 'R':
		case 'S':
		case 'T':
		case 'U':
		case 'V':
		case 'W':
		case 'X':
		case 'Y':
		case 'Z':
		default:
			assert (false and "missed symbol");
		};
	}

	char BigramModel::LowerByUpper(char symbol) {
		assert ((symbol >= 'a') and (symbol <= 'z'));
		switch (symbol) {
		case 'a':
		case 'b':
		case 'c':
		case 'd':
		case 'e':
		case 'f':
		case 'g':
		case 'h':
		case 'i':
		case 'j':
		case 'k':
		case 'l':
		case 'm':
		case 'n':
		case 'o':
		case 'p':
		case 'q':
		case 'r':
		case 's':
		case 't':
		case 'u':
		case 'v':
		case 'w':
		case 'x':
		case 'y':
		case 'z':
		default:
			assert (false and "missed symbol");
		};
	}
}













