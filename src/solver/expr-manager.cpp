#include "expr-manager.hpp"

namespace solver {

	ExprManager::ExprManager() : type_table_ {
		std::make_shared<SInt8Ty>(),
		std::make_shared<SInt16Ty>(),
		std::make_shared<SInt32Ty>(),
		std::make_shared<SInt64Ty>(),
		std::make_shared<UInt8Ty>(),
		std::make_shared<UInt16Ty>(),
		std::make_shared<UInt32Ty>(),
		std::make_shared<UInt64Ty>()} {
	}

	ExprManager::~ExprManager() {

	}

	ExprPtr ExprManager::MkVar(std::string name, TypePtr type) {
		return std::make_shared<Var>(name, type);
	}

	ExprPtr ExprManager::MkConst (ValuePtr val) {
		return std::make_shared<Const>(val);
	}

	ExprPtr ExprManager :: MkBinOp (ExprPtr a, ExprPtr b, Kind op_code) {
		return std::make_shared <BinOp>(a, b, op_code);
	}
}
