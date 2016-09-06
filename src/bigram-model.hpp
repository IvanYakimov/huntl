#ifndef __BIGRAM_MODEL_HPP__
#define __BIGRAM_MODEL_HPP__

#include <cassert>
#include <random>
#include <iostream>

namespace interpreter {
	class BigramModel {
		enum class Case {
			kUpper,
			kLower
		};
		static unsigned CharToIdx(char symbol, BigramModel::Case c);
		static unsigned CharToIdx(char symbol);
		static char IdxToChar(unsigned idx, BigramModel::Case kind);
		const static unsigned kAlphabetSize = 26;
		const static unsigned kPrecision = 100;
		constexpr const static double kNorm = 0.01;
		const static unsigned kUltimateItemIdx = BigramModel::kAlphabetSize - 1;
		const static unsigned kPenultimateItemIdx = BigramModel::kAlphabetSize - 2;
		using BigramSquare = double[kAlphabetSize][kAlphabetSize];
		char Alphabet[kAlphabetSize];
		class BestNextGenerator {
		public:
			BestNextGenerator(const BigramSquare& bigram, Case kind);
			~BestNextGenerator();
			char Successor(char symbol);
		private:
			unsigned distribution_ [kAlphabetSize][kAlphabetSize];
			unsigned upper_limits_ [kAlphabetSize];
			Case kind_;

			char TurnRoulette(unsigned row, unsigned shout);
			unsigned MakeShout(unsigned row);
		};
		class ProbabilityGenerator {
		public:
			ProbabilityGenerator(const BigramSquare& bigram, Case fst_case, Case snd_case);
			~ProbabilityGenerator();
			double GetBigramProbability(char first, char second);
		private:
			double probabilities_[kAlphabetSize][kAlphabetSize];
			Case fst_case_;
			Case snd_case_;
		};
	public:
		BigramModel();
		~BigramModel();
		char UpperByUpper(char symbol);
		double BigramProbability(char pre, char post);
		char LowerByLower(char symbol);
		char UpperByLower(char symbol);
		char LowerByUpper(char symbol);
	private:
		BigramSquare lbl_bigram_;
		BestNextGenerator lbl_gen_;
		ProbabilityGenerator lbl_prob_;
	};
}

#endif
