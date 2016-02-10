#ifndef __EXPR_MANAGER_HPP__
#define __EXPR_MANAGER_HPP__

#include "expr.hpp"

namespace solver {
	class ExprManager
	{
	public:
		ExprManager();
		~ExprManager();
		ExprPtr MkVar(std::string name, TypePtr type);
		ExprPtr MkBinOp (ExprPtr a, ExprPtr b, Kind kind);
		ExprPtr MkConst(ValuePtr val);

		template<typename T> ValuePtr ProduceInt(T val) {
			return std::make_shared<Int<T>>(val);
		}

		//TODO: testing
		template<typename T> TypePtr GetIntTy(){
			auto check_ty = [] (TypePtr ty) -> bool {
				if (instanceof<BasicIntTy>(ty)) {
					auto int_ty = std::dynamic_pointer_cast<BasicIntTy>(ty);
					if (int_ty->IsSigned() == std::numeric_limits<T>::is_signed
							and int_ty->GetWidth() == sizeof(T)*8
							and int_ty->GetAlignment() == sizeof(T))
						return true;
				}
			};

			for (auto i = type_table_.begin(); i != type_table_.end(); i++) {
				if (check_ty(*i) == true)
					return *i;
			}
			// type not found
			return nullptr;
		}

	private:
		std::list<TypePtr> type_table_;
	};
}

#endif
