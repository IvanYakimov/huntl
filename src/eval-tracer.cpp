#include "eval-tracer.hpp"

namespace interpreter {
	using memory::HolderPtr;

	EvalTracer::EvalTracer(ContextRef context) : context_(context) {
	}

	EvalTracer::~EvalTracer() {

	}

//#define TRACE_CALLS
	void EvalTracer::Call(const llvm::Function* target, bool status) {
#ifdef TRACE_CALLS
		if (status == true) {
			std::clog << TraceLevel() << "call " << target->getName().str() << std::endl;
			level_++;
		}
		else {
			level_--;
			std::clog << TraceLevel() << "back from " << target->getName().str() << std::endl;
		}
#endif
	}

//#define TRACE_FUNC_BODIES

	void EvalTracer::Func(const llvm::Function* target) {
#ifdef TRACE_FUNC_BODIES
		std::clog << utils::ToString(*target) << std::endl;
#endif
	}

	std::string EvalTracer::TraceLevel() {
		std::string res;
		for (int i = 0; i < level_; i++)
			res += "-";
		res += " ";
		return res;
	}

//#define TRACE_BR

	void EvalTracer::Block(const llvm::BasicBlock* next) {
#ifdef TRACE_BR
		if (next != nullptr)
			std::clog << utils::ToString(*next) << std::endl;
		else
			std::clog << "--end--" << std::endl;
#endif
	}

//#define TRACE_INST_NAMES
//#define TRACE_INST

	void EvalTracer::Assign(const llvm::Value& target) {
#ifdef TRACE_INST_NAMES
		std::clog << utils::ToString(inst) << std::endl;
#endif
#ifdef TRACE_INST
		std::string inst_str = utils::ToString(target);
		HolderPtr holder = context_.Top()->Load(&target);
		std::regex r(" = ");
		std::smatch r_match;
		if (std::regex_search(inst_str, r_match, r)) {
			std::clog << TraceLevel() << r_match.prefix() << " <- " << *holder << std::endl;
		}
		else
			assert (false and "regex failed");
#endif
		//llvm::errs() << inst << "\n";
		//context_.Top()->Print();
		//context_.Solver().Print();
	}

	void EvalTracer::Ret(const llvm::Value* target) {
#ifdef TRACE_INST_NAMES
		HolderPtr holder = context_.Top()->Load(target);
		std::clog << TraceLevel() << "ret " << *holder << std::endl;
#endif
	}

	void EvalTracer::Ret() {
#ifdef TRACE_INST_NAMES
		std::clog << TraceLevel() << "ret void" << std::endl;
#endif
	}
}
















