#ifndef __BIGRAM_MODEL_HPP__
#define __BIGRAM_MODEL_HPP__

#include <cassert>
#include <random>
#include <iostream>

namespace interpreter {
	class BigramModel {
	//public:
		enum class Case {
			kUpper,
			kLower
		};
		static unsigned CharToIdx(char symbol, BigramModel::Case c);
		static char IdxToChar(unsigned idx, BigramModel::Case kind);
		const static unsigned kAlphabetSize = 26;
		const static unsigned kPrecision = 100;
		const static unsigned kUltimateItemIdx = BigramModel::kAlphabetSize - 1;
		const static unsigned kPenultimateItemIdx = BigramModel::kAlphabetSize - 2;
		using BigramSquare = float[kAlphabetSize][kAlphabetSize];
		char Alphabet[kAlphabetSize];
		//using UniformSquare = unsigned[kAlphabetSize][kAlphabetSize];
		class Generator {
		public:
			Generator(const BigramSquare& bigram, Case kind);
			~Generator();
			char Successor(char symbol);
		private:
			unsigned distribution_ [kAlphabetSize][kAlphabetSize];
			unsigned upper_limits_ [kAlphabetSize];
			Case kind_;

			char TurnRoulette(unsigned row, unsigned shout);
			unsigned MakeShout(unsigned row);
	};
	public:
		BigramModel();
		~BigramModel();
		char UpperByUpper(char symbol);
		char LowerByLower(char symbol);
		char UpperByLower(char symbol);
		char LowerByUpper(char symbol);
		//float lower_by_lower[26][26];
		BigramSquare lbl_bigram_;
		Generator lbl_gen_;
	//protected:
	//protected:

	};
}

#endif
