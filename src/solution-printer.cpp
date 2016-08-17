#include "solution-printer.hpp"

namespace interpreter {
	void PrintASCII(MetaIntRef symbol, std::ostream& os) {
		unsigned long code = symbol.getZExtValue();
		char ascii = (char)code;
		if (std::isprint(ascii))
			os << ascii;
		else
			os << "\\" << (unsigned)ascii;
	}

	void PrintSolution(SolutionPtr sol, std::ostream& file) {
		if (utils::instanceof<Integer>(sol)) {
			IntegerPtr integer = std::dynamic_pointer_cast<Integer>(sol);
			MetaIntRef val = integer->Get();
			if (val.getBitWidth() > 8)
				file << integer->Get();
			else
				PrintASCII(val, file);
		}
		else if (utils::instanceof<Pointer>(sol)) {
			PointerPtr pointer = std::dynamic_pointer_cast<Pointer>(sol);
			file << "*";
			PrintSolution(pointer->Dereference(), file);
			//assert (! "not impl");
		}
		else if (utils::instanceof<Array>(sol)) {
			ArrayPtr array = std::dynamic_pointer_cast<Array>(sol);
			file << "\'";
			for (int i = 0; i < array->GetSize(); i++) {
				SolutionPtr el_sol = array->GetElement(i);
				PrintSolution(el_sol, file);
			}
			file << "\'";
		}
		else
			assert (! "unexpected type of argument");
	}

	void PrintFunctionInfo(llvm::Function* func, std::ostream& file) {
		file << func->getName().str() << ": ";
	}

	void PrintSeparator(std::ostream& file) {
		file << " ";
	}

	void PrintTransition(std::ostream& file) {
		file << " => ";
	}

	void PrintEndl(std::ostream& file) {
		file << std::endl;
	}

	void PrintWholeSolution(llvm::Function* func, SolutionListPtr arg_sols, SolutionPtr ret_sol, std::ostream& file) {
		assert (func != nullptr and arg_sols != nullptr and ret_sol != nullptr);
		assert (func->arg_size() == arg_sols->size());

		PrintFunctionInfo(func, file);
		auto it = arg_sols->begin();
		while (it != arg_sols->end()) {
			PrintSolution(*it, file);
			if (++it != arg_sols->end())
				PrintSeparator(file);
		}
		PrintTransition(file);
		PrintSolution(ret_sol, file);
		PrintEndl(file);
	}
}
