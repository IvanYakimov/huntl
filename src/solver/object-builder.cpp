#include "object-builder.hpp"

namespace solver {

	ObjectBuilder::ObjectBuilder() {

	}

	ObjectBuilder::~ObjectBuilder() {

	}

	ExprPtr ObjectBuilder::MkVar(std::string name, TypePtr type) {
		return std::make_shared<Var>(name, type);
	}

	ExprPtr ObjectBuilder::MkConst (ValuePtr val) {
		return std::make_shared<Const>(val);
	}

	ExprPtr ObjectBuilder::MkBinOp (ExprPtr a, ExprPtr b, Kind op_code) {
		return std::make_shared <BinOp>(a, b, op_code);
	}

	ValuePtr ObjectBuilder::MkIntVal(bool is_signed, Width width, uint64_t ulval) {
		using std::make_shared;
		auto setval = [&] (BasicIntPtr int_obj) {
			int_obj->SetUInt64(ulval);
			return int_obj;
		};

		switch (width) {
		case Width::w8:
			return is_signed ?
					setval(make_shared<Int<int8_t>>()) :
					setval(make_shared<Int<uint8_t>>());
		case Width::w16:
			return is_signed ?
					setval(make_shared<Int<int16_t>>())	:
					setval(make_shared<Int<uint16_t>>());
		case Width::w32:
			return is_signed ?
					setval(make_shared<Int<int32_t>>())	:
					setval(make_shared<Int<uint32_t>>());
		case Width::w64:
			return is_signed ?
					setval(make_shared<Int<int64_t>>()):
					setval(make_shared<Int<uint64_t>>());
		};

		throw std::logic_error("not implemented");
	}
}













