#include "kind.hpp"

namespace solver{
/* arithmetical */
    	  const std::string add_str = "add";
    	  const std::string sub_str = "sub";
    	  const std::string mul_str = "mul";
    	  const std::string sign_dev_str = "sdev";
    	  const std::string sign_rem_str = "srem";

    	  /* vector */
    	  const std::string shift_left_str = "shl";
    	  const std::string logic_shift_right_str = "lshr";
    	  const std::string arith_shift_right_str = "ashr";

    	  /* logical */
    	  const std::string and_str = "and";
    	  const std::string or_str = "or";
    	  const std::string xor_str = "xor";

    	  /* comparisons */
    	  const std::string equal_str = "eq";
    	  const std::string unsigned_greater_than_str = "ugt";
		  const std::string unsigned_greater_or_equal_str = "uge";
		  const std::string unsigned_less_than_str = "ult";
		  const std::string unsigned_less_or_equal_str = "ule";
    	  const std::string signed_greater_than_str = "sgt";
    	  const std::string signed_greater_or_equal_str = "sge";
    	  const std::string signed_less_than_str = "slt";
    	  const std::string signed_less_or_equal_str = "sle";

	std::map <Kind, std::string> op_code_map_ = {
			/* arithmetical */
			{Kind::ADD, add_str},
			{Kind::SUB, sub_str},
			{Kind::MUL, mul_str},
			{Kind::SDIV, sign_dev_str},
			{Kind::SREM, sign_rem_str},

			/* vector */
			{Kind::SHL, shift_left_str},
			{Kind::LSHR, logic_shift_right_str},
			{Kind::ASHR, arith_shift_right_str},

			/* logical */
			{Kind::AND, and_str},
			{Kind::OR, or_str},
			{Kind::XOR, xor_str},

			/* comparisons */
			{Kind::EQ, equal_str},
			{Kind::UGE, unsigned_greater_or_equal_str},
			{Kind::UGT, unsigned_greater_than_str},
			{Kind::ULE, unsigned_less_or_equal_str},
			{Kind::ULT, unsigned_less_than_str},
			{Kind::SGT, signed_greater_than_str},
			{Kind::SGE, signed_greater_or_equal_str},
			{Kind::SLT, signed_less_than_str},
			{Kind::SLE,  signed_less_or_equal_str}
	  };

	std::string KindToString(Kind kind) {
		return op_code_map_[kind];
	}
}












