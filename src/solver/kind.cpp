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
    	  const std::string logical_shift_right_str = "lshr";
    	  const std::string arith_shift_right_str = "ashr";

    	  /* logical */
    	  const std::string and_str = "and";
    	  const std::string or_str = "or";
    	  const std::string xor_str = "xor";

    	  /* comparisons */
    	  const std::string equal_str = "eq";
    	  const std::string not_equal_str = "ne";
    	  const std::string unsigned_greater_than_str = "ugt";
		  const std::string unsigned_greater_or_equal_str = "uge";
		  const std::string unsigned_less_than_str = "ult";
		  const std::string unsigned_less_or_equal_str = "ule";
    	  const std::string signed_greater_than_str = "sgt";
    	  const std::string signed_greater_or_equal_str = "sge";
    	  const std::string signed_less_than_str = "slt";
    	  const std::string signed_less_or_equal_str = "sle";

	  // TODO check map type
	std::map <Kind, std::string> op_code_map_ = {
			/* arithmetical */
			{Kind::ADD, add_str},
			{Kind::SUB, sub_str},
			{Kind::MUL, mul_str},
			{Kind::SIGN_DEV, sign_dev_str},
			{Kind::SING_REM, sign_rem_str},

			/* vector */
			{Kind::SHIFT_LEFT, shift_left_str},
			{Kind::LOGICAL_SHIFT_RIGHT, logical_shift_right_str},
			{Kind::ARIRH_SHIFT_RIGHT, arith_shift_right_str},

			/* logical */
			{Kind::AND, and_str},
			{Kind::OR, or_str},
			{Kind::XOR, xor_str},

			/* comparisons */
			{Kind::EQUAL, equal_str},
			{Kind::NOT_EQUAL, not_equal_str},
			{Kind::SIGNED_GREATER_THAN, signed_greater_than_str},
			{Kind::SIGNED_GREATER_OR_EQUAL, signed_greater_or_equal_str},
			{Kind::SIGNED_LESS_THAN, signed_less_than_str},
			{Kind::SIGNED_LESS_OR_EQUAL,  signed_less_or_equal_str}
	  };

	std::string KindToString(Kind kind) {
		return op_code_map_[kind];
	}
}












