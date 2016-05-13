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

	ExprPtr ObjectBuilder::MkDoubleNode (ExprPtr a, ExprPtr b, Kind op_code) {
		assert(false && "not implemented");
		auto l = std::dynamic_pointer_cast<BitVec>(a);
		auto r = std::dynamic_pointer_cast<BitVec>(b);
		return std::make_shared <BinOp>(BinOpKind::BVADD, l, r);

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
					setval(make_shared<IntVal<int8_t>>()) :
					setval(make_shared<IntVal<uint8_t>>());
		case Width::w16:
			return is_signed ?
					setval(make_shared<IntVal<int16_t>>())	:
					setval(make_shared<IntVal<uint16_t>>());
		case Width::w32:
			return is_signed ?
					setval(make_shared<IntVal<int32_t>>())	:
					setval(make_shared<IntVal<uint32_t>>());
		case Width::w64:
			return is_signed ?
					setval(make_shared<IntVal<int64_t>>()):
					setval(make_shared<IntVal<uint64_t>>());
		};

		throw std::logic_error("not implemented");
	}
}













