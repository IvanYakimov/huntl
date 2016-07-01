#include "meta-evaluator.hpp"

namespace interpreter {
	using memory::Concrete;
	using memory::Symbolic;
	using memory::HolderPtr;

	MetaEvaluator::MetaEvaluator(memory::DisplayPtr display, solver::SolverPtr solver) :
			display_(display), solver_(solver) {
	}

	MetaEvaluator::~MetaEvaluator() {
	}

	MetaEvaluatorPtr MetaEvaluator::Create(memory::DisplayPtr display, solver::SolverPtr solver) {
		return utils::Create<MetaEvaluator>(display, solver);
	}

	void MetaEvaluator::BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right) {
		if (memory::IsConcrete(left) and memory::IsConcrete(right)) {
			interpreter::MetaInt left_val = Object::UpCast<Concrete>(left)->Get();
			interpreter::MetaInt right_val = Object::UpCast<Concrete>(right)->Get();
			interpreter::MetaInt result;
			switch (inst->getOpcode()) {
			case llvm::Instruction::Add:
				result = left_val.operator +(right_val);
				break;
			default: assert (false && "this binary operator not implemented");
			}
			auto result_holder = Concrete::Create(result);
			display_->Store(inst, result_holder);
		}
		else {
			assert (false && "symbolic operation");
		}
	}

	void MetaEvaluator::Assign (const llvm::Value *destination, memory::HolderPtr target) {
		if (memory::IsConcrete(target)) {
			//interpreter::BitVec rhs_val = Object::UpCast<memory::Concrete>(loaded_rhs)->Get();
			//auto updated_lhs = memory::Concrete::Create(rhs_val);
			display_->Store(destination, target);
		}
		else if (memory::IsSymbolic(target)) {
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
			assert (false and "not implemented behavior");
	}
}











