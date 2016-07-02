#include "meta-evaluator.hpp"

namespace interpreter {
	using memory::Concrete;
	using memory::Symbolic;
	using memory::HolderPtr;
	using memory::IsConcrete;
	using memory::IsSymbolic;

	MetaEvaluator::MetaEvaluator(memory::DisplayPtr display, solver::SolverPtr solver) :
			display_(display), solver_(solver) {
	}

	MetaEvaluator::~MetaEvaluator() {
	}

	MetaEvaluatorPtr MetaEvaluator::Create(memory::DisplayPtr display, solver::SolverPtr solver) {
		return utils::Create<MetaEvaluator>(display, solver);
	}

	solver::SharedExpr MetaEvaluator::Concrete_To_Symbolic(interpreter::MetaInt concrete_val) {
		auto bv_val = interpreter::MetaInt_To_BitVec(concrete_val);
		auto c_sym = solver_->ExprManager().mkConst(bv_val);
		return c_sym;
	}

	solver::Kind MetaEvaluator::ExtractKindFromInst(const llvm::Instruction* inst) {
		switch (inst->getOpcode()) {
		case llvm::Instruction::Add:
			return solver::Kind::BITVECTOR_PLUS;
		}
		assert (false and "not implemented");
	}

	MetaInt MetaEvaluator::PerformConcreteBinOp(const llvm::Instruction* inst, MetaInt left_val, MetaInt right_val) {
		switch (inst->getOpcode()) {
		case llvm::Instruction::Add:
			return left_val.operator +(right_val);
		}
		assert (false && "not implemented");
	}

	void MetaEvaluator::BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right) {
		auto process_sym_binop = [&] (const llvm::Instruction* inst, solver::SharedExpr a, solver::SharedExpr b) {
			auto kind = ExtractKindFromInst(inst);
			auto constraint = solver_->ExprManager().mkExpr(kind, a, b);
			auto constraint_holder = memory::Symbolic::Create(constraint);
			Assign(inst, constraint_holder);
		};

		if (IsConcrete(left) and IsConcrete(right)) {
			auto left_val = Object::UpCast<Concrete>(left)->Get();
			auto right_val = Object::UpCast<Concrete>(right)->Get();
			auto result = PerformConcreteBinOp(inst, left_val, right_val);
			auto result_holder = Concrete::Create(result);
			display_->Store(inst, result_holder);
		}
		else if (IsConcrete(left) and IsSymbolic(right)) {
			auto left_sym = Concrete_To_Symbolic(memory::GetValue(left));
			auto right_sym = memory::GetExpr(right);
			process_sym_binop(inst, left_sym, right_sym);
		}
		else if (IsSymbolic(left) and IsConcrete(right)) {
			auto left_sym = memory::GetExpr(left);
			auto right_sym = Concrete_To_Symbolic(memory::GetValue(right));
			process_sym_binop(inst, left_sym, right_sym);
		}
		else if (IsSymbolic(left) and IsSymbolic(right)) {
			auto left_sym = memory::GetExpr(left);
			auto right_sym = memory::GetExpr(right);
			process_sym_binop(inst, left_sym, right_sym);
		}
		else
			assert (false and "unexpected behavior");
	}

	void MetaEvaluator::Assign (const llvm::Value *destination, memory::HolderPtr target) {
		if (memory::IsConcrete(target)) {
			display_->Store(destination, target);
		}
		else if (memory::IsSymbolic(target)) {
			//TODO: refactoring:
			assert (solver_ != nullptr);
			auto e = memory::GetExpr(target);
			auto e_type = e.getType();
			auto v = solver_->ExprManager().mkVar(e_type);
			auto v_holder = memory::Symbolic::Create(v);
			auto v_eq_e = solver_->ExprManager().mkExpr(solver::Kind::EQUAL, v, e);
			auto v_eq_e_holder = memory::Symbolic::Create(v_eq_e);
			solver_->Constraint(v_eq_e_holder);
			display_->Store(destination, v_holder);
		}
		else
			assert (false and "unexpected behavior");
	}
}











