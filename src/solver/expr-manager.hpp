#ifndef __EXPR_MANAGER_HPP__
#define __EXPR_MANAGER_HPP__

#pragma once

#include "expr.hpp"
#include <algorithm>
#include <memory>

namespace solver {
	class ExprManager;

	/** Smart pointer to ExprManager, used in a singleton pattern implementation.
	 * \see ExprManager
	 * \see GetExprManager
	 */
	using ExprManagerPtr = std::shared_ptr<ExprManager>;

	/** Singleton pattern implementation. There is only one instance of ExprManager in run-time,
	 * to get (smart pointer to) it use this method.
	 * \see ExprManager
	 */
	ExprManagerPtr GetExprManager();

	/**
	 * Helps to create smt expressions. Use it to create any run-time instances of any smt expressions,
	 * (never use corresponding expression's constructors directly!).
	 * \see ExprManagerHelper
	 */
	class ExprManager
	{
	public:
		/** Basic constructor, do NOT use it directly! Use GetExprManager to obtain (smart pointer to instance of) expr manager.
		 * \see GetExprManager
		 */
		ExprManager();
		~ExprManager();
		/**
		 * Creates (smart pointer to) a binary operation.
		 * @param a, b - (smart pointers to) left and right children, which are arbitrary SMT expressions
		 * @param kind - kind of the binary operation (e.g. SUM, MULT etc.)
		 * \see BinOp
		 * \see Kind
		 */
		ExprPtr MkBinOp (ExprPtr a, ExprPtr b, Kind kind);
		/** Creates (smart pointer to) a variable.
		 * @param name - name of variable, standard string.
		 * @param type - type of variable, always use ExprManager to obtain (smart pointer to) an appropriate type.
		 * \see MkIntTy
		 */
		ExprPtr MkVar(std::string name, TypePtr type);
		/** Creates (smart pointer to) a constant.
		 * @param val - value of the constant, always use ExprManager to create (smart pointer to) an appropiate value
		 * \see MkIntVal
		 */
		ExprPtr MkConst(ValuePtr val);

		/** Crates (smart pointer to) integer value. Use it if you want to transform value, obtained from particular SMT-solver.
		 * @param is_signed - true if it is signed, false - if it's not.
		 * @param width - number of bites (e.g. 8, 16, 32, 64) of creating integer.
		 * @param val - unsigned long representation, all insignificant bytes are filled by zeros.
		 * For example: if we have int8_t x = "FF", the val (representing x as uint64_t) should contain "00 00 00 00 00 00 00 FF";
		 * for int32_t y = "FF FF FF FF" val = "00 00 00 00 FF FF FF FF", etc.
		 * \see Int
		 */
		ValuePtr MkIntVal(bool is_signed, Width width, uint64_t val);

		/** Creates (smart pointer to) integer value. Use it if you want transform scalar C++ integer (e.g. int32_t etc.).
		 * @tparam T - scalar integer type from STL (e.g. int32_t etc.).
		 * \see Int
		 */
		template<typename T>
		ValuePtr MkIntVal(T val) {
			return std::make_shared<Int<T>>(val);
		}

		/** Returns (smart pointer to) integer type.
		 * @param T - scalar integer type from STL (e.g. int32_t etc.).
		 * \see IntTy
		 */
		template<class T>
		TypePtr MkIntTy() {
			TypePtr tmp = std::make_shared<IntTy<T>>();
			auto it = std::find_if(type_table_.begin(), type_table_.end(), [&tmp] (const TypePtr &item) {return *item == *tmp;});
			if (it != type_table_.end())
				return *it;
			else
				throw std::logic_error("type not found");
		}

	private:
		std::list<TypePtr> type_table_;
	};

	//TODO: explicit template class member specialization (if possible)
}

#endif














