#include "expr-manager.hpp"

namespace solver {

	ExprManager::ExprManager() : type_table_ {
		std::make_shared<IntTy<int8_t>>(),
		std::make_shared<IntTy<int16_t>>(),
		std::make_shared<IntTy<int32_t>>(),
		std::make_shared<IntTy<int64_t>>(),
		std::make_shared<IntTy<int8_t>>(),
		std::make_shared<IntTy<int16_t>>(),
		std::make_shared<IntTy<int32_t>>(),
		std::make_shared<IntTy<int64_t>>()} {
	}

	ExprManager::~ExprManager() {

	}

	ExprPtr ExprManager::MkVar(std::string name, TypePtr type) {
		return std::make_shared<Var>(name, type);
	}

	ExprPtr ExprManager::MkConst (ValuePtr val) {
		return std::make_shared<Const>(val);
	}

	ExprPtr ExprManager::MkBinOp (ExprPtr a, ExprPtr b, Kind op_code) {
		return std::make_shared <BinOp>(a, b, op_code);
	}

}
