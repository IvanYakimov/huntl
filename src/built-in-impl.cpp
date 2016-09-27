#include "built-in-impl.hpp"

namespace interpreter {
	using memory::HolderPtr;
	MkSym::MkSym(ContextRef context, unsigned size) : context_(context), size_(size) {}
	memory::HolderPtr MkSym::operator()(llvm::Function* f, memory::ArgMapPtr args) {
		//assert (args->empty() == true);
		return memory::Symbolic::Create(context_.Solver().MkVar(context_.Solver().MkBitVectorType(size_)));
	}

	Gen::Gen(ContextRef context, llvm::Function* target, llvm::Module* module) :
			context_(context), target_(target), module_(module) {}
	memory::HolderPtr Gen::operator()(llvm::Function* f, memory::ArgMapPtr args) {
		interpreter::TestGenerator generator(module_, target_, args, context_, std::cerr);
		//std::flush(std::cerr);
		//std::flush(std::cout);
		generator.Do();
		//TODO: fix
		//exit(0);
		return memory::Undef::Create();
	}
}
