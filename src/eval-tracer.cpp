#include "eval-tracer.hpp"

namespace interpreter {
	using memory::HolderPtr;

	EvalTracer::EvalTracer(ContextRef context) : context_(context) {
	}

	EvalTracer::~EvalTracer() {

	}

	void EvalTracer::Call(const llvm::Function* target, bool status) {
		if (status == true) {
			std::clog << TraceLevel() << "call " << target->getName().str() << std::endl;
			level_++;
		}
		else {
			level_--;
			std::clog << TraceLevel() << "back from " << target->getName().str() << std::endl;
		}
	}

	void EvalTracer::Func(const llvm::Function* target) {
		std::clog << utils::ToString(*target) << std::endl;
	}

	std::string EvalTracer::TraceLevel() {
		std::string res;
		for (int i = 0; i < level_; i++)
			res += "-";
		res += " ";
		return res;
	}

#define TRACE_BR

	void EvalTracer::Block(const llvm::BasicBlock* next) {
#ifdef TRACE_BR
		if (next != nullptr)
			std::clog << utils::ToString(*next) << std::endl;
		else
			std::clog << "--end--" << std::endl;
#endif
	}

//#define TRACE_INST_NAMES
#define TRACE_TARGET_VAL

	void EvalTracer::Assign(const llvm::Instruction& inst, const llvm::Value* target) {
#ifdef TRACE_INST_NAMES
		std::clog << utils::ToString(inst) << std::endl;
#endif
#ifdef TRACE_TARGET_VAL
		if (llvm::isa<llvm::StoreInst>(inst))
			assert (target != nullptr);
		else
			(target = &inst);
		std::string target_full_name = utils::ToString(*target);
		HolderPtr holder = context_.Top()->Load(target);
		std::regex r(" = ");
		std::smatch r_match;
		if (std::regex_search(target_full_name, r_match, r)) {
			std::clog << TraceLevel() << r_match.prefix() << " <- " << *holder << std::endl;
		}
		else
			assert (false and "regex failed");
#endif
		//llvm::errs() << inst << "\n";
		//context_.Top()->Print();
		//context_.Solver().Print();
	}
}
















