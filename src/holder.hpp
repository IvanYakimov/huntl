#ifndef __HOLDER_HPP__
#define __HOLDER_HPP__

#include "expr.hpp"
#include "instanceof.hpp"
#include "wrapper.hpp"
#include "creatable.hpp"
#include "meta-int.hpp"
#include "creatable.hpp"
#include "converter.hpp"
#include "ram-delc.hpp"
#include "solver.hpp"

#include "llvm/IR/InstVisitor.h"

namespace memory {
	class Holder;

	using HolderPtr = std::shared_ptr<Holder>;

	using Concrete = utils::Wrapper<Holder, interpreter::MetaInt, interpreter::MetaInt_print_, interpreter::MetaInt_compare_>;
	using Symbolic = utils::Wrapper<Holder, solver::SharedExpr>;

	using ConcretePtr = std::shared_ptr<Concrete>;
	using SymbolicPtr = std::shared_ptr<Symbolic>;

	bool IsSymbolic(HolderPtr holder);
	bool IsConcrete(HolderPtr holder);
	bool IsUndef(HolderPtr holder);

	class Holder : public Object {
	public:
		COMPARABLE(Holder);
		PRINTABLE(Holder);
		virtual ~Holder(){}
	};

	class Undef : public Holder {
	public:
		COMPARABLE(Undef);
		PRINTABLE(Undef);
		virtual ~Undef(){}
		virtual bool Equals (const Object& rhs) const;
		virtual std::ostream& ToStream(std::ostream &os, const Object& obj) const;
		static HolderPtr Create();
	};

	const solver::SharedExpr& GetExpr(memory::HolderPtr holder);
	const interpreter::MetaInt& GetValue(memory::HolderPtr holder);
	interpreter::MetaInt Concretize(solver::SolverRef solver, memory::HolderPtr holder);
}

#endif













