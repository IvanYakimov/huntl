#include "eval-tracer.hpp"

namespace interpreter {
	using memory::HolderPtr;

//#define EVAL_TRACING

#ifdef EVAL_TRACING
#define TRACE_CALLS
//#define TRACE_FUNC_BODIES
//#define TRACE_BR
//#define TRACE_INST
#define TRACE_RAM_OPERATIONS
//#define TRACE_PATH_CONSTRAINT
#endif

	EvalTracer::EvalTracer(ContextRef context) : context_(context) {

	}

	EvalTracer::~EvalTracer() {

	}


	void EvalTracer::Call(const llvm::Function* target, memory::ArgMapPtr args, bool status) {
#ifdef TRACE_CALLS
		if (status == true) {
			std::clog << TraceLevel() << "CALL '" << target->getName().str() << "'" <<
					" WITH ARGS:\t";
			for (auto it = args->begin(); it != args->end(); ++it) {
				std::clog << utils::ToString(*it->first) << " = ";
				std::clog  << *it->second << " | ";
			}
			std::clog << std::endl;
			level_++;
		}
		else {
			level_--;
			std::clog << TraceLevel() << "BACK FROM '" << target->getName().str() << "'" << std::endl;
		}
#ifdef TRACE_PATH_CONSTRAINT
		context_.Solver().Print();
#endif /* TRACE_PATH_CONSTRAINT */
#endif /* TRACE_CALLS */
	}

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

	void EvalTracer::Block(const llvm::BasicBlock* next) {
#ifdef TRACE_BR
		if (next != nullptr)
			std::clog << utils::ToString(*next) << std::endl;
		else
			std::clog << "--end--" << std::endl;
#endif
	}

	void EvalTracer::Assign(const llvm::Value& target) {
#ifdef TRACE_INST
		std::clog << utils::ToString(target) << std::endl;
#endif
#ifdef TRACE_RAM_OPERATIONS
		std::string inst_str = utils::ToString(target);
		HolderPtr holder = context_.Top()->Load(&target);
		std::regex r(" = ");
		std::smatch r_match;

		if (std::regex_search(inst_str, r_match, r))
			std::clog << TraceLevel() << r_match.prefix();
		else
			std::clog << TraceLevel() << inst_str;

		std::clog << " [" << context_.Top()->GetLocation(&target) << "]"
				<< " <- "
				<< *holder
				<< std::endl;
#endif
}

	void EvalTracer::Ret(const llvm::Value* target) {
#ifdef TRACE_RAM_OPERATIONS
		HolderPtr holder = context_.Top()->Load(target);
		std::clog << TraceLevel() << "ret " << *holder << std::endl;
#endif
	}

	void EvalTracer::Ret() {
#ifdef TRACE_RAM_OPERATIONS
		std::clog << TraceLevel() << "ret void" << std::endl;
#endif
	}
}
















