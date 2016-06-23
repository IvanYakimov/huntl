#ifndef __MEMORY_HPP__
#define __MEMORY_HPP__

#include "llvm/IR/Instruction.h"
#include "object.hpp"
#include <cvc4/cvc4.h>

namespace interpreter {

	class Object;

	using ObjectPtr = std::shared_ptr<Object>;

	class Object {
	public:
		virtual ~Object(){}
	};

	template <typename T>
	class ObjectHolder : public Object {
	public:
		ObjectHolder(T value) : value_(value) {}
		virtual ~ObjectHolder() {}
		T Get() {return value_;}
		static ObjectPtr Create(T arg) {
		    return std::make_shared<ObjectHolder<T>>(arg);
		}

	private:
		T value_;
	};

	using SymbolicObject = ObjectHolder<CVC4::Expr>;

	class Display {
	public:
		void Alloca(const llvm::Value* address);
		ObjectPtr Read(const llvm::Value* address);
		void Write(const llvm::Value* address, ObjectPtr object);
	};
}

#endif











