#include "symbolic-eval.hpp"

namespace interpreter {
	using solver::SharedExpr;
	using solver::Kind;
	using interpreter::MetaIntRef;
	using llvm::Instruction;
	using llvm::ICmpInst;

	SymbolicEval::SymbolicEval(ContextRef context) :
			context_(context){

	}

	Kind SymbolicEval::ExtractKindFromInst(const Instruction* inst) {
		switch (inst->getOpcode()) {
		case Instruction::Add:
			return Kind::BITVECTOR_PLUS;
		case Instruction::Sub:
			return Kind::BITVECTOR_SUB;
		case Instruction::Mul:
			return Kind::BITVECTOR_MULT;
		case Instruction::SDiv:
			return Kind::BITVECTOR_SDIV;
		case Instruction::SRem:
			return Kind::BITVECTOR_SREM;
		case Instruction::UDiv:
			return Kind::BITVECTOR_UDIV;
		case Instruction::URem:
			return Kind::BITVECTOR_UREM;
		case Instruction::And:
			return Kind::BITVECTOR_AND;
		case Instruction::Or:
			return Kind::BITVECTOR_OR;
		case Instruction::Xor:
			return Kind::BITVECTOR_XOR;
		case Instruction::Shl:
			return Kind::BITVECTOR_SHL;
		case Instruction::AShr:
			return Kind::BITVECTOR_ASHR;
		case Instruction::LShr:
			return Kind::BITVECTOR_LSHR;
		default:
			assert (false and "not implemented");
		}
	}

	solver::Kind SymbolicEval::ExtractKindFromICmpInst(const llvm::ICmpInst* inst) {
		switch(inst->getOpcode()) {
		case ICmpInst::ICMP_EQ:
			return Kind::EQUAL;
		case ICmpInst::ICMP_NE:
			return Kind::DISTINCT;
		case ICmpInst::ICMP_SGE:
			return Kind::BITVECTOR_SGE;
		case ICmpInst::ICMP_SGT:
			return Kind::BITVECTOR_SGT;
		case ICmpInst::ICMP_SLE:
			return Kind::BITVECTOR_SLE;
		case ICmpInst::ICMP_SLT:
			return Kind::BITVECTOR_SLT;
		case ICmpInst::ICMP_UGE:
			return Kind::BITVECTOR_UGE;
		case ICmpInst::ICMP_UGT:
			return Kind::BITVECTOR_UGT;
		case ICmpInst::ICMP_ULE:
			return Kind::BITVECTOR_ULE;
		case ICmpInst::ICMP_ULT:
			return Kind::BITVECTOR_ULT;
		default:
			assert (false and "not implemented");
		}
	}

	void SymbolicEval::BinOp (const Instruction* inst, SharedExpr left, SharedExpr right) {
		auto kind = ExtractKindFromInst(inst);
		auto constraint = context_.Solver().MkExpr(kind, left, right);
		Assign(inst, constraint);
	}

	void SymbolicEval::ICmpInst (const llvm::Instruction* inst, solver::SharedExpr left, solver::SharedExpr right) {
		assert (llvm::isa<ICmpInst*>(inst));
		auto icmp_inst = llvm::dyn_cast<ICmpInst>(inst);
		auto kind = ExtractKindFromICmpInst(icmp_inst);
		auto constraint = context_.Solver().MkExpr(kind, left, right);
		Assign(inst, constraint);
	}

	void SymbolicEval::Assign (const llvm::Value *destination, solver::SharedExpr e) {
		auto e_type = e.getType();
		auto v = context_.Solver().MkVar(e_type);
		auto v_eq_e = context_.Solver().MkExpr(solver::Kind::EQUAL, v, e);
		// Add constraint to PC
		context_.Solver().Constraint(v_eq_e);
		auto v_holder = memory::Symbolic::Create(v);
		// Store fresh constrained variable v to the memory
		context_.Top()->Store(destination, v_holder);
	}
}














