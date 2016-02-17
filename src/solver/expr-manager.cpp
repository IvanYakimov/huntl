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

	ValuePtr ExprManager::MkIntVal(bool is_signed, Width width, uint64_t ulval) {
		//TODO: refactroing of Width (make an enum)
		using std::make_shared;
		auto setval = [&] (BasicIntPtr int_obj) {
			int_obj->SetUInt64(ulval);
			return int_obj;
		};

		switch (width) {
		case 8:
			return is_signed ?
					setval(make_shared<Int<int8_t>>()) :
					setval(make_shared<Int<uint8_t>>());
		case 16:
			return is_signed ?
					setval(make_shared<Int<int16_t>>())	:
					setval(make_shared<Int<uint16_t>>());
		case 32:
			return is_signed ?
					setval(make_shared<Int<int32_t>>())	:
					setval(make_shared<Int<uint32_t>>());
		case 64:
			return is_signed ?
					setval(make_shared<Int<int64_t>>()):
					setval(make_shared<Int<uint64_t>>());
		};

		throw std::logic_error("not implemented");
	}
}













