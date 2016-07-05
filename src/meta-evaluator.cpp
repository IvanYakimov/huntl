#include "meta-evaluator.hpp"

namespace interpreter {
	using memory::Concrete;
	using memory::Symbolic;
	using memory::HolderPtr;
	using memory::IsConcrete;
	using memory::IsSymbolic;

	MetaEvaluator::MetaEvaluator(interpreter::ContextRef context) :
			context_(context),
			concrete_eval_(context),
			symbolic_eval_(context){
	}

	MetaEvaluator::~MetaEvaluator() {
	}

	MetaEvaluatorPtr MetaEvaluator::Create(interpreter::ContextRef context) {
		return utils::Create<MetaEvaluator>(context);
	}

	solver::SharedExpr MetaEvaluator::Concrete_To_Symbolic(interpreter::MetaInt concrete_val) {
		auto bv_val = interpreter::MetaInt_To_BitVec(concrete_val);
		auto c_sym = context_.Solver().MkConst(bv_val);
		return c_sym;
	}

	solver::Kind MetaEvaluator::ExtractKindFromInst(const llvm::Instruction* inst) {
		using llvm::Instruction;
		using solver::Kind;
		switch (inst->getOpcode()) {
		case Instruction::Add:
			return Kind::BITVECTOR_PLUS;
		case Instruction::Sub:
			return Kind::BITVECTOR_SUB;
		case Instruction::And:
			return Kind::BITVECTOR_AND;
		case Instruction::LShr:
			return Kind::BITVECTOR_LSHR;
		}
		assert (false and "not implemented");
	}

	void MetaEvaluator::BinOp (const llvm::Instruction* inst, memory::HolderPtr left, memory::HolderPtr right) {
		auto process_sym_binop = [&] (const llvm::Instruction* inst, solver::SharedExpr a, solver::SharedExpr b) {
			auto kind = ExtractKindFromInst(inst);
			auto constraint = context_.Solver().MkExpr(kind, a, b);
			auto constraint_holder = memory::Symbolic::Create(constraint);
			Assign(inst, constraint_holder);
		};

		if (IsConcrete(left) and IsConcrete(right)) {
			auto left_val = Object::UpCast<Concrete>(left)->Get();
			auto right_val = Object::UpCast<Concrete>(right)->Get();
			concrete_eval_.BinOp(inst, left_val, right_val);
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
			concrete_eval_.Assign(destination, memory::GetValue(target));
		}
		else if (memory::IsSymbolic(target)) {
			auto e = memory::GetExpr(target);
			auto e_type = e.getType();
			auto v = context_.Solver().MkVar(e_type);
			auto v_holder = memory::Symbolic::Create(v);
			auto v_eq_e = context_.Solver().MkExpr(solver::Kind::EQUAL, v, e);
			auto v_eq_e_holder = memory::Symbolic::Create(v_eq_e);
			context_.Solver().Constraint(v_eq_e_holder);
			context_.Top()->Store(destination, v_holder);
		}
		else
			assert (false and "unexpected behavior");
	}
}











