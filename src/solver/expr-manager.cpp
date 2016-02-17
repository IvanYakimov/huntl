#include "expr-manager.hpp"

namespace solver {

	ExprManagerPtr GetExprManager() {
		static ExprManagerPtr em_ (nullptr);
		if (em_ == nullptr)
			return em_ = std::make_shared<ExprManager>();
		else
			return em_;
	}

	ExprManager::ExprManager() : type_table_ {
		std::make_shared<IntTy<int8_t>>(),
		std::make_shared<IntTy<int16_t>>(),
		std::make_shared<IntTy<int32_t>>(),
		std::make_shared<IntTy<int64_t>>(),
		std::make_shared<IntTy<uint8_t>>(),
		std::make_shared<IntTy<uint16_t>>(),
		std::make_shared<IntTy<uint32_t>>(),
		std::make_shared<IntTy<uint64_t>>()} {
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

	ValuePtr ExprManager::MkIntVal(bool is_signed, Width width, uint64_t val) {
		switch (width) {
		case 8:
		case 16:
		case 32:
		case 64:
			break;
		};
		throw std::logic_error("not implemented");
	}
}













