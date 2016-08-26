#include "solution-printer.hpp"

namespace interpreter {
	using memory::HolderPtr;

	SolutionPrinter::SolutionPrinter(ContextRef context, llvm::Function* func, SolutionListPtr arg_sols, SolutionPtr ret_sol) :
		context_(context),
		func_(func),
		arg_sols_(arg_sols),
		ret_sol_(ret_sol){
		assert (func_ != nullptr and arg_sols_ != nullptr and ret_sol_ != nullptr);
	}

	SolutionPrinter::~SolutionPrinter() {

	}

	void SolutionPrinter::PrintASCII(MetaIntRef symbol, std::ostream& os) {
		//unsigned long code = symbol.getZExtValue();
		char ascii = GetChar(symbol); //ascii = (char)code;
		if (std::isprint(ascii))
			os << ascii;
		else
			os << "\\" << (unsigned)ascii;
	}

	/*
	bool SolutionPrinter::IsString(ArrayPtr array) {
		if (utils::instanceof<Integer>(array->GetElement(0))) {
			IntegerPtr integer = std::dynamic_pointer_cast<Integer>(array->GetElement(0));
			if (interpreter::GetWidth(integer->Get()) == 8) {
				return true; }}
		return false;
	}
	*/

	bool SolutionPrinter::IsEndl(SolutionPtr el_sol) {
		IntegerPtr integer = std::dynamic_pointer_cast<Integer>(el_sol);
		MetaInt val = Concretize(context_.Solver(), integer->Get());
		if (val.getZExtValue() == (unsigned long)'\0')
			return true;
		else
			return false;
	}

	void SolutionPrinter::PrintString(ArrayPtr array, std::ostream& file) {
		bool end_reached = false;
		file << "\"";
		for (int i = 0; i < array->GetSize(); i++) {
			SolutionPtr el_sol = array->GetElement(i);
			end_reached = IsEndl(el_sol);
			//if (not end_reached)
				PrintSolution(el_sol, file);
		}
		file << "\"";
	}

	void SolutionPrinter::PrintArbitraryArray(ArrayPtr array, std::ostream& file) {
		file << "{";
		for (int i = 0; i < array->GetSize(); i++) {
			SolutionPtr el_sol = array->GetElement(i);
			PrintSolution(el_sol, file);
			if (i + 1 < array->GetSize())
				file << ",";
		}
		file << "}";
	}

	void SolutionPrinter::PrintSolution(SolutionPtr sol, std::ostream& file) {
		if (utils::instanceof<Integer>(sol)) {
			IntegerPtr integer = std::dynamic_pointer_cast<Integer>(sol);
			MetaInt val = Concretize(context_.Solver(), integer->Get());
			if (val.getBitWidth() > 8)
				file << val;
			else
				PrintASCII(val, file);
		} else if (utils::instanceof<Pointer>(sol)) {
			PointerPtr pointer = std::dynamic_pointer_cast<Pointer>(sol);
			file << "* ";
			PrintSolution(pointer->Dereference(), file);
			//assert (! "not impl");
		} else if (utils::instanceof<Array>(sol)) {
			ArrayPtr array = std::dynamic_pointer_cast<Array>(sol);
			if (array->IsString())
				PrintString(array, file);
			else
				PrintArbitraryArray(array, file);
		} else
			assert (! "unexpected type of argument");
	}

	void SolutionPrinter::PrintFunctionInfo(llvm::Function* func, std::ostream& file) {
		file << func->getName().str() << ": ";
	}

	void SolutionPrinter::PrintSeparator(std::ostream& file) {
		file << " ";
	}

	void SolutionPrinter::PrintTransition(std::ostream& file) {
		file << " => ";
	}

	void SolutionPrinter::PrintEndl(std::ostream& file) {
		file << std::endl;
	}

	void SolutionPrinter::operator()(std::ostream& file_) {
		assert (func_ != nullptr and arg_sols_ != nullptr and ret_sol_ != nullptr);
		assert (func_->arg_size() == arg_sols_->size());

		if (not context_.Solver().IsSat())
			assert (false and "cannot print unsolvable memory graph");

		PrintFunctionInfo(func_, file_);
		auto it = arg_sols_->begin();
		while (it != arg_sols_->end()) {
			PrintSolution(*it, file_);
			if (++it != arg_sols_->end())
				PrintSeparator(file_);
		}
		PrintTransition(file_);
		PrintSolution(ret_sol_, file_);
		PrintEndl(file_);
	}
}
