#ifndef __EXPR_MANAGER_HPP__
#define __EXPR_MANAGER_HPP__

#pragma once

#include "expr.hpp"
#include <algorithm>
#include <memory>

namespace solver {
	class ExprManager;
	using ExprManagerPtr = std::shared_ptr<ExprManager>;

	// Singleton implementation
	ExprManagerPtr GetExprManager();

	class ExprManager
	{
	public:
		ExprManager();
		~ExprManager();
		ExprPtr MkVar(std::string name, TypePtr type);
		ExprPtr MkBinOp (ExprPtr a, ExprPtr b, Kind kind);
		ExprPtr MkConst(ValuePtr val);

		template<typename T, typename... Args>
		ValuePtr MkIntVal(Args... args) {
			return std::make_shared<Int<T>>(std::forward<Args>(args)...);
		}

		//TODO: testing
		template<class T, typename... Args>
		TypePtr MkIntTy(Args... args) {
			const IntTy<T> tmp(std::forward<Args>(args)...);
			auto it = std::find_if(type_table_.begin(), type_table_.end(), [&tmp] (const TypePtr &item) {return *item == tmp;});
			if (it != type_table_.end())
				return *it;
			else
				throw std::logic_error("type not found");
		}

		ValuePtr MkIntVal(bool is_signed, Width width, uint64_t val);

	private:
		std::list<TypePtr> type_table_;
	};

	//TODO: explicit template class member specialization
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














