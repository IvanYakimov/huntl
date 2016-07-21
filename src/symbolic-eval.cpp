#include "symbolic-eval.hpp"

namespace interpreter {
	using solver::SharedExpr;
	using solver::Kind;
	using interpreter::MetaIntRef;
	using llvm::Instruction;
	using llvm::ICmpInst;
	using solver::BitVec;
	using solver::InfiniteInt;
	using utils::MetaKind;

	SymbolicEval::SymbolicEval(ContextRef context) :
			context_(context) {
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
		switch(inst->getPredicate()) {
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

	void SymbolicEval::IntComparison (const llvm::Instruction* inst, solver::SharedExpr left, solver::SharedExpr right) {
		assert (llvm::isa<llvm::ICmpInst>(inst));
		const llvm::ICmpInst *icmp_inst = llvm::dyn_cast<llvm::ICmpInst>(inst);
		auto kind = ExtractKindFromICmpInst(icmp_inst);
		auto bool_res = context_.Solver().MkExpr(kind, left, right);
		auto bit_true = context_.Solver().MkConst(BitVec(1, InfiniteInt(1)));
		auto bit_false = context_.Solver().MkConst(BitVec(1, InfiniteInt(0)));
		auto e = context_.Solver().MkExpr(Kind::ITE, bool_res, bit_true, bit_false);

		Assign(inst, e);
	}

	void SymbolicEval::Conversion (const llvm::Instruction* lhs, solver::SharedExpr rhs, MetaKind kind, unsigned width) {
		auto conversion = context_.Solver().MkConversion(kind, width, rhs);

		Assign(lhs, conversion);
	}

	void SymbolicEval::Assign (const llvm::Value *destination, solver::SharedExpr e) {
		auto e_type = e.getType();
		auto v = context_.Solver().MkVar(e_type);
		solver::Kind kind;
		if (e_type.isBitVector())
			kind = solver::Kind::EQUAL;
		else if (e_type.isBoolean())
			kind = solver::Kind::IFF;
		auto constraint = context_.Solver().MkExpr(kind, v, e);
		// Add constraint to PC
		context_.Solver().Constraint(constraint);
		auto v_holder = memory::Symbolic::Create(v);
		// Store fresh constrained variable v to the memory
		context_.Top()->Store(destination, v_holder);
	}

	const llvm::BasicBlock* SymbolicEval::MakeDecision(const solver::SharedExpr& condition, const llvm::BasicBlock* branch_ptr, bool branch_marker) {
		auto bit_true = context_.Solver().MkConst(BitVec(1, InfiniteInt(1)));
		auto bit_false = context_.Solver().MkConst(BitVec(1, InfiniteInt(0)));
		auto bool_true = context_.Solver().MkConst(true);
		auto bool_false = context_.Solver().MkConst(false);


		auto cond_eq_true = context_.Solver().MkExpr(Kind::EQUAL, condition, bit_true);
		auto converted_condition = context_.Solver().MkExpr(Kind::ITE, cond_eq_true, bool_true, bool_false);


		auto direction = context_.Solver().MkConst(branch_marker);
		auto final_constraint = context_.Solver().MkExpr(Kind::IFF, converted_condition, direction);

		context_.Solver().Constraint(final_constraint);
		if (!context_.Solver().IsSat())
			exit(EXIT_SUCCESS);
		else
			return branch_ptr;
	}

	const llvm::BasicBlock* SymbolicEval::Branch (const llvm::Instruction *inst, solver::SharedExpr condition,
			const llvm::BasicBlock *iftrue, const llvm::BasicBlock *iffalse) {
		pid_t child_pid = 0;
		int ch_status;
		const llvm::BasicBlock* next_branch;


		std::cerr << ".";

		llvm::errs().flush();
		std::flush(std::cerr);

		child_pid = fork();
		if (child_pid > 0) {
			wait(&ch_status);
			next_branch = MakeDecision(condition, iftrue, true);
		}
		else {
			next_branch = MakeDecision(condition, iffalse, false);
		}
		return next_branch;
	}
}














