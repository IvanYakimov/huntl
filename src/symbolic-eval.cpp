#include "symbolic-eval.hpp"

namespace interpreter {
	using solver::SharedExpr;
	using solver::Kind;
	using interpreter::MetaIntRef;
	using llvm::Instruction;

	SymbolicEval::SymbolicEval(ContextRef context) :
			context_(context){

	}

	Kind SymbolicEval::ExtractKindFromInst(const Instruction* inst) {
		switch (inst->getOpcode()) {
		case Instruction::Add:
			return Kind::BITVECTOR_PLUS;
		case Instruction::Sub:
			return Kind::BITVECTOR_SUB;
		case Instruction::And:
			return Kind::BITVECTOR_AND;
		case Instruction::LShr:
			return Kind::BITVECTOR_LSHR;
		default:
			assert (false and "not implemented");
		}
	}

	void SymbolicEval::BinOp (const Instruction* inst, SharedExpr left, SharedExpr right) {
		auto kind = ExtractKindFromInst(inst);
		auto constraint = context_.Solver().MkExpr(kind, left, right);
		Assign(inst, constraint);
	}

	void SymbolicEval::Assign (const llvm::Value *destination, solver::SharedExpr e) {
		auto e_type = e.getType();
		auto v = context_.Solver().MkVar(e_type);
		auto v_holder = memory::Symbolic::Create(v);
		auto v_eq_e = context_.Solver().MkExpr(solver::Kind::EQUAL, v, e);
		auto v_eq_e_holder = memory::Symbolic::Create(v_eq_e);
		context_.Solver().Constraint(v_eq_e_holder);
		context_.Top()->Store(destination, v_holder);
	}
}














