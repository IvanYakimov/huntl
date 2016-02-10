# include "expr.hpp"

using std::function;

namespace solver
{//-------------------------------------------------------------------
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

	template<typename T> ValuePtr ProduceInt(T val) {
		return std::make_shared<Int<T>>(val);
	}

	//TODO: testing
	template<typename T> TypePtr ExprManager::GetIntTy() {
		auto check_ty = [] (TypePtr ty) -> bool {
			if (instanceof<BasicIntTy>(ty)) {
				auto int_ty = std::dynamic_pointer_cast<BasicIntTy>(ty);
				if (int_ty->IsSigned == std::numeric_limits<T>::is_signed
						and int_ty->GetWidth() == sizeof(T)*8
						and int_ty->GetAlignment() == sizeof(T))
					return true;
			}
		};

		for (auto i = type_table_.begin(); i != type_table_.end(); i++) {
			if (check_ty(*i) == true)
				return *i;
		}
		/* type not found */
		return nullptr;
	}

	//-------------------------------------------------------------------
	// Variable
	//TODO: solver compilation problem

	Var::Var (std::string name, TypePtr type) {
		if (not name.empty() and type != nullptr) {
			name_ = name;
			type_ = type;
		}
		else
			throw std::logic_error("invalid arguments");
	}

	Var::~Var() {}

	std::string Var::ToString() const {return GetName();}

	bool Var::Equals(const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
			return lhs.name_ == rhs.name_;
		};
		return EqualsHelper<Var>(*this, rhs, cmp);
	}

	std::string Var::GetName() const {return name_;}
	TypePtr Var::GetType() const {return type_;}

	//-------------------------------------------------------------------
	// Constant

	Const::Const(ValuePtr val) : value_(val) {}
	Const::~Const() {}

	std::string Const::ToString() const {
		return GetValue()->ToString();
	}

	bool Const::Equals(const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
			return lhs.GetValue() == rhs.GetValue();
		};
		return EqualsHelper<Const>(*this, rhs, cmp);
	}

	ValuePtr Const::GetValue() const {
		return value_;
	}

	//-------------------------------------------------------------------
	// BinaryOperation
	BinOp::BinOp(ExprPtr l, ExprPtr r, Kind k){
		if (l == nullptr or r == nullptr)
			throw std::logic_error("null not valid");
		kind_ = k;
		left_child_ = l;
		right_child_ = r;
	}

	BinOp::~BinOp() {}

	std::string BinOp::ToString() const {
		return GetKindName() + " " + GetLeftChild()->ToString() + " " + GetRightChild()->ToString();
	}

	bool BinOp::Equals(const Object& rhs) const {
		auto cmp = [] (auto lhs, auto rhs) -> bool {
			return lhs.kind_ == rhs.kind_ &&
					lhs.left_child_ == rhs.left_child_ &&
					lhs.right_child_ == rhs.right_child_;
		};
		return EqualsHelper<BinOp>(*this, rhs, cmp);
	}

	ExprPtr BinOp::GetLeftChild() const {return left_child_;}
	ExprPtr BinOp::GetRightChild() const {return right_child_;}

	Kind BinOp::GetKind() const {return kind_;}
	std::string BinOp::GetKindName() const {return KindToString(kind_);}

}













