#include "context.hpp"

namespace solver {
	Context::Context() : expr_manager_(), smt_engine_(&expr_manager_), symbol_table_() {

	}

	Context::~Context() {

	}

	CVC4::ExprManager& Context::ExprManger() {
		return expr_manager_;
	}

	CVC4::SmtEngine& Context::SmtEngine() {
		return smt_engine_;
	}

	CVC4::SymbolTable& Context::SymbolTable() {
		return symbol_table_;
	}
}
