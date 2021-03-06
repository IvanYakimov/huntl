#include "bigram-model.hpp"

namespace interpreter {
	BigramModel::BigramModel() :
						//		a		b		c		d		e		f		g		h		i		j		k		l		m		n		o		p		q		r		s		t		u		v		w		x		y		z
		lbl_bigram_ {/*a*/ {7.38, 	11.5,	12.2, 	12.1, 	9.25, 	10.6, 	11.6, 	9.03, 	12.4, 	9.03, 	11.0, 	13.1, 	11.9, 	13.8, 	7.79, 	11.4, 	7.95, 	13.3, 	13.0, 	13.5, 	11.1, 	11.6, 	10.5, 	9.64, 	12.0,	9.23},
						/*b*/ {11.4, 	9.00,	6.57, 	6.50, 	12.4, 	3.85, 	3.56, 	5.33, 	10.9,	8.14,	3.56,	11.5,	6.93,	5.6,	11.5,	5.25,	.0,		10.6,	10.2,	8.52,	11.3,	7.05,	6.57,	0,		11.4,	2.71},
						/*c*/ {12.4,	4.08,	10.4,	5.76,	12.7,	3.00,	0.69,	12.5,	11.7,	1.10,	11.4,	11.1,	4.89,	4.90,	12.8,	3.76,	7.87,	11.2,	9.47,	12.1,	11.2,	1.95,	3.00,	0.69,	9.93,	5.82},
						/*d*/ {11.6,	7.33,	7.73,	10.1,	12.8,	7.46,	9.83,	7.55,	12.2,	7.54,	5.46,	9.76,	9.44,	9.16,	11.4,	6.09,	6.83,	10.7,	11.0,	7.30,	11.0,	9.31,	8.73,	0.00,	9.98,	5.09},
						/*e*/ {12.8,	10.2,	12.4,	13.3,	12.2,	11.2,	11.0,	9.36,	11.3,	7.58,	9.97,	12.4,	12.0,	13.4,	10.6,	11.4,	9.52,	13.9,	13.4,	12.3,	9.23,	11.6,	11.5,	11.3,	11.4,	8.43},
						/*f*/ {11.1,	4.32,	4.78,	3.50,	11.5,	11.3,	6.02,	3.64,	11.9,	4.23,	5.42,	10.1,	6.27,	5.31,	12.4,	3.26,	.0,		11.5,	8.16,	10.8,	10.5,	3.81,	4.91,	1.39,	8.18,	2.56},
						/*g*/ {11.4,	5.36,	3.58,	6.81,	12.2,	6.20,	9.57,	11.7,	11.0,	3.09,	4.68,	9.99,	7.66,	10.4,	11.0,	5.28,	1.95,	11.3,	10.3,	9.35,	10.6,	2.94,	5.96,	2.08,	9.12,	3.64},
						/*h*/ {13.1,	8.20,	6.35,	7.84,	14.1,	6.60,	5.24,	6.21,	12.6,	3.50,	5.91,	9.00,	8.58,	9.71,	12.4,	5.91,	5.12,	10.6,	9.32,	11.2,	10.2,	5.18,	8.07,	.0,		9.54,	2.64},
						/*i*/ {11.9,	10.4,	12.8,	12.4,	12.1,	11.1,	11.8,	6.54,	7.10,	7.21,	10.4,	12.5,	11.8,	14.0,	12.7,	10.5,	8.09,	11.9,	13.1,	13.1,	8.71,	11.7,	6.71,	9.25,	6.69,	10.2},
						/*j*/ {8.52,	1.61,	3.43,	3.56,	9.39,	2.08,	.0,		1.10,	7.24,	2.30,	3.76,	2.40,	3.93,	3.37,	10.0,	1.61,	.0,		1.39,	2.30,	2.56,	10.1,	.69,	.0,		.0,		1.39,	1.79},
						/*k*/ {9.21,	6.78,	4.55,	6.64,	11.9,	6.73,	6.35,	7.68,	11.0,	3.85,	6.42,	9.22,	6.53,	9.80,	8.42,	6.30,	.0,		8.04,	10.5,	6.95,	7.46,	5.42,	7.05,	.0,		8.70,	2.56},
						/*l*/ {12.5,	8.60,	8.44,	11.9,	12.0,	10.0,	7.95,	7.18,	12.8,	4.22,	9.54,	12.7,	9.68,	7.78,	12.0,	9.50,	3.43,	8.53,	11.3,	10.9,	10.9,	9.58,	8.49,	3.40,	12.1,	6.25},
						/*m*/ {12.3,	10.7,	5.82,	5.65,	12.8,	7.59,	4.80,	5.64,	12.0,	3.56,	4.30,	7.21,	10.8,	7.95,	12.0,	11.8,	1.39,	5.81,	10.6,	5.84,	10.7,	4.43,	4.88,	.0,		9.84,	2.89},
						/*n*/ {12.0, 	8.42,	12.2,	13.3,	12.8,	10.2,	13.2,	9.07,	12.1,	8.40,	10.5,	10.1,	9.81,	10.9,	12.1,	7.93,	7.36,	8.38,	12.4,	13.1,	10.7,	10.3,	8.30,	7.55,	11.1,	7.75},
						/*o*/ {10.5,	10.6,	11.2,	11.3,	9.82,	13.0,	10.6,	9.43,	10.8,	8.47,	10.6,	12.1,	12.6,	13.6,	11.7,	11.7,	6.27,	13.4,	11.9,	12.2,	12.9,	11.5,	12.0,	8.62,	9.85, 	8.30},
						/*p*/ {12.0,	6.81,	5.74,	5.81,	12.3,	6.47,	7.80,	10.4,	11.0,	4.91,	6.47,	11.8,	8.67,	5.60,	12.0,	11.1,	2.08,	12.2,	10.2,	10.4,	10.9,	1.10,	5.85,	.0,		8.97,	3.58},
						/*q*/ {3.30,	1.95,	.0,		.00,	.69,	.69,	.00,	.0,		6.64,	.0,		.0,		1.10,	.0,		.00,	.00,	.0,		1.10,	.0,		1.10,	1.95,	10.9,	1.79,	0.69,	.0,		.0,		.0	},
						/*r*/ {12.8,	9.63,	11.2,	11.6,	13.7,	9.61,	11.0,	8.83,	12.7,	5.58,	11.4,	10.8,	11.3,	11.5,	12.8,	10.1,	6.18,	11.0,	12.5,	12.2,	11.0,	12.5,	8.79,	5.47,	11.6,	6.92},
						/*s*/ {12.1,	8.59,	11.1,	9.10,	12.9,	8.62,	6.66,	12.0,	12.5,	4.16,	10.2,	10.4,	10.1,	9.18,	12.0,	11.3,	8.25,	8.72,	12.2,	13.2,	11.7,	6.44,	9.15,	.00,	9.75,	5.97},
						/*t*/ {12.5,	8.43,	9.81,	7.32,	13.3,	8.08,	7.71,	14.2,	13.2,	4.17,	6.14,	10.7,	9.83,	8.95,	13.2,	7.33,	1.95,	12.2,	12.2,	11.4,	11.4,	6.49,	10.5,	2.83,	11.5,	8.49},
						/*u*/ {10.9,	10.8,	11.3,	10.9,	11.2,	9.19,	11.1,	6.29,	10.8,	5.98,	8.08,	11.9,	11.0,	12.1,	8.53,	11.2,	5.73,	12.3,	12.3,	12.4,	5.42,	7.31,	6.43,	7.56,	8.93,	7.43},
						/*v*/ {10.8,	.00,	6.05,	4.20,	12.9,	.00,	4.52,	1.39,	12.0,	.69,	3.18,	5.15,	2.40,	5.34,	10.4,	.0,		.0,		6.23,	6.43,	3.71,	6.76,	4.74,	.0,		.0,		8.11,	1.10},
						/*w*/ {12.1,	6.89,	6.09,	7.88,	11.8,	6.22,	3.71,	12.0,	12.1,	.0,		7.07,	8.85,	7.31,	10.7,	11.7,	5.53,	1.95,	9.53,	10.0,	7.87,	4.69,	.69,	2.94,	.00,	8.43,	2.20},
						/*x*/ {9.11,	3.78,	9.11,	.00,	9.61,	5.59,	1.10,	7.76,	9.11,	.0,		.0,		5.06,	4.39,	2.94,	7.47,	10.3,	4.76,	1.39,	4.55,	9.75,	7.96,	4.62,	6.11,	5.06,	6.00,	.00	},
						/*y*/ {9.16,	8.22,	8.48,	7.77,	11.4,	6.35,	6.34,	6.32,	9.92,	3.09,	5.96,	9.07,	9.49,	9.11,	10.6,	8.63,	1.61,	8.97,	10.7,	8.86,	6.57,	5.64,	8.04,	4.42,	3.43,	6.56},
						/*z*/ {9.41,	5.86,	3.69,	4.73,	10.1,	2.56,	5.00,	6.32,	8.93,	.69,	5.29,	6.95,	6.00,	4.67,	8.13,	4.98,	3.14,	4.75,	4.98,	4.84,	6.85,	4.84,	5.21,	.0,		7.23,	8.10}
		},
		lbl_gen_(lbl_bigram_, BigramModel::Case::kLower),
		lbl_prob_(lbl_bigram_, Case::kLower, Case::kLower)
		{

		}

		BigramModel::~BigramModel() {

		}

		BigramModel::BestNextGenerator::BestNextGenerator(const BigramModel::BigramSquare& bigram, BigramModel::Case kind) :
				kind_(kind) {
			for (int n = 0; n < BigramModel::kAlphabetSize; ++n) {
				unsigned sum = 0;
				for (int m = 0; m < BigramModel::kAlphabetSize; ++m) {
					distribution_[n][m] = sum;
					sum += bigram[n][m] * BigramModel::kPrecision;
				}
				upper_limits_[n] = sum;
			}
		}

		BigramModel::BestNextGenerator::~BestNextGenerator() {

		}

		unsigned BigramModel::CharToIdx(char symbol) {
			if (std::islower(symbol))
				return BigramModel::CharToIdx(symbol, BigramModel::Case::kLower);
			else if (std::isupper(symbol))
				return BigramModel::CharToIdx(symbol, BigramModel::Case::kUpper);
			else
				assert (false and "not alphabet symbol!");
		}

		unsigned BigramModel::CharToIdx(char symbol, BigramModel::Case kind) {
			unsigned idx = 0;
			if (kind == BigramModel::Case::kUpper) {
				assert (std::isupper(symbol));
				idx = symbol - 'A';
			} else if (kind == BigramModel::Case::kLower) {
				assert (std::islower(symbol));
				idx = symbol - 'a';
			} else
				assert (false and "unexpected");
			assert (idx >= 0 and idx <= BigramModel::kUltimateItemIdx);
			return idx;
		}

		char BigramModel::IdxToChar(unsigned idx, BigramModel::Case kind) {
			char result;
			assert (idx >= 0 and idx <= BigramModel::kUltimateItemIdx);
			if (kind == BigramModel::Case::kUpper) {
				result = idx + 'A';
				assert (std::isupper(result));
				return result;
			} else if (kind == BigramModel::Case::kLower) {
				result = idx + 'a';
				assert (std::islower(result));
				return result;
			}
			assert (false and "unexpected");
		}

		char BigramModel::BestNextGenerator::TurnRoulette(unsigned row, unsigned shout) {
			char result = 0;
			assert(shout >= 0 and shout <= upper_limits_[row]);
			int m = 0;
			int idx = 0;
			while(m <= BigramModel::kPenultimateItemIdx) {
				auto current = distribution_[row][m];
				auto next = distribution_[row][m + 1];
				assert(next >= current);
				if (shout >= current && shout <= next) {
					idx = m;//result = BigramModel::IdxToChar(m, kind_);
					break;
				}
				++m;
			}
			result = BigramModel::IdxToChar(idx, kind_);
			assert (std::isalpha(result) and "bad roulette turn");
			return result;
		}

		unsigned BigramModel::BestNextGenerator::MakeShout(unsigned row) {
			std::random_device rd;
			std::mt19937 gen(rd());
			std::uniform_int_distribution<unsigned> dis(0, upper_limits_[row]);
			unsigned shout = dis(gen);
			assert(shout >= 0 and shout <= upper_limits_[row]);
			return shout;
		}

		char BigramModel::BestNextGenerator::Successor(char symbol) {
			char result;
			unsigned row = 0;
			row = BigramModel::CharToIdx(symbol, kind_);
			unsigned shout = MakeShout(row);
			result = TurnRoulette(row, shout);
			assert (std::isalpha(result));
			return result;
		}

	char BigramModel::UpperByUpper(char symbol) {
		assert (std::isupper(symbol));
		assert (false and "not implemented");
	}

#include "options.hpp"
  
	char BigramModel::LowerByLower(char symbol) {
		assert (std::islower(symbol));
		char res;
#ifdef ROULETTE_NEXT
		res = lbl_gen_.Successor(symbol);
#elif defined PURE_NEXT
		//TODO: refactoring - best fit generation
		auto raw = CharToIdx(symbol, Case::kLower);
		int max = lbl_bigram_[raw][0],
		  col = 0;
		for (int i = 0; i < kAlphabetSize; i++) {
		  if (max < lbl_bigram_[raw][i]) {
		    max = lbl_bigram_[raw][i];
		    col = i; }}
		res = IdxToChar(col, Case::kLower);
#elif defined RANDOM_NEXT
		std::random_device rd;
		std::mt19937 gen(rd());
		std::uniform_int_distribution<char> dis('a', 'z');
		res = dis(gen);
#else
		assert (fasle and "not implemented");
#endif
		assert (std::islower(res));
		return res;
	}

	double BigramModel::BigramProbability(char pre, char post) {
		assert (std::isalpha(pre) and std::isalpha(post));
		if (std::islower(pre) and std::islower(post)) {
			 return lbl_prob_.GetBigramProbability(pre, post);
		} else {
			std::cerr << "not implemented, sorry";
			return 0;
		}
	}

	char BigramModel::UpperByLower(char symbol) {
		assert (std::isupper(symbol));
		assert (false and "not implemented");
	}

	char BigramModel::LowerByUpper(char symbol) {
		assert (std::islower(symbol));
		assert (false and "not implemented");
	}

	BigramModel::ProbabilityGenerator::ProbabilityGenerator(const BigramSquare& bigram, Case fst_case, Case snd_case) :
		fst_case_(fst_case),
		snd_case_(snd_case){
		//TODO: refactoring
		double amounts[kAlphabetSize];
		double total = 0.0;
		for (auto row = 0; row < kAlphabetSize; ++row) {
			double current_amount = 0;
			for (auto col = 0; col < kAlphabetSize; ++col) {
				current_amount += bigram[row][col];
				total += bigram[row][col];
			}
			amounts[row] = current_amount;
		}
		for (auto row = 0; row < kAlphabetSize; ++row) {
			for (auto col = 0; col < kAlphabetSize; ++col) {
				//probabilities_[row][col] = bigram[row][col] / amounts[row];
				probabilities_[row][col] = bigram[row][col] / total;
			}
		}
	}

	BigramModel::ProbabilityGenerator::~ProbabilityGenerator() {

	}

	double BigramModel::ProbabilityGenerator::GetBigramProbability(char first, char second) {
		auto fst_idx = BigramModel::CharToIdx(first, fst_case_);
		auto snd_idx = BigramModel::CharToIdx(second, snd_case_);
		return probabilities_[fst_idx][snd_idx];
	}
}













