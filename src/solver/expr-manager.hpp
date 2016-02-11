#ifndef __EXPR_MANAGER_HPP__
#define __EXPR_MANAGER_HPP__

#pragma once

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

		template<typename T> TypePtr GetIntTy() {
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

	//TODO: explicit template class member function specialization
	/*
	template ValuePtr ExprManager::ProduceInt<int8_t>(int8_t val);
	template ValuePtr ExprManager::ProduceInt<int16_t>(int16_t val);
	template ValuePtr ExprManager::ProduceInt<int32_t>(int32_t val);
	template ValuePtr ExprManager::ProduceInt<int64_t>(int64_t val);
	template ValuePtr ExprManager::ProduceInt<uint8_t>(uint8_t val);
	template ValuePtr ExprManager::ProduceInt<uint16_t>(uint16_t val);
	template ValuePtr ExprManager::ProduceInt<uint32_t>(uint32_t val);
	template ValuePtr ExprManager::ProduceInt<uint64_t>(uint64_t val);

	template TypePtr ExprManager::GetIntTy<int8_t>();
	template TypePtr ExprManager::GetIntTy<int16_t>();
	template TypePtr ExprManager::GetIntTy<int32_t>();
	template TypePtr ExprManager::GetIntTy<int64_t>();
	template TypePtr ExprManager::GetIntTy<uint8_t>();
	template TypePtr ExprManager::GetIntTy<uint16_t>();
	template TypePtr ExprManager::GetIntTy<uint32_t>();
	template TypePtr ExprManager::GetIntTy<uint64_t>();
	*/
}

#endif














