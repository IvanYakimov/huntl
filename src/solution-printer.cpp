#include "solution-printer.hpp"

#include "options.hpp"

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

#warning "potential bug: incorrect values sometimes occur within string (see strXstr functions)"
	void SolutionPrinter::PrintASCII(MetaIntRef symbol, std::ostream& file) {
		char ascii = GetChar(symbol); //ascii = (char)code;
		if (std::isprint(ascii))
			file << ascii;
		else switch (ascii){
		case 0x0: file << "\\0"; break;
		case 0x7: file << "\\a"; break;
		case 0x8: file << "\\b"; break;
		case 0xC: file << "\\f"; break;
		case 0xA: file << "\\n"; break;
		case 0xD: file << "\\r"; break;
		case 0x9: file << "\\t"; break;
		case 0x5C: file << "\\\\"; break;
		case 0x27: file << "\\\'"; break;
		case 0x22: file << "\\\""; break;
		case 0x3F: file << "\\\?"; break;
		default:
			file << "\\x";
			std::stringstream ss;
			unsigned fst = (unsigned)ascii % 0xf;
			ascii /= 0xf;
			unsigned snd = (unsigned)ascii % 0xf;
			file << snd << fst;
		};
	}

	bool SolutionPrinter::IsEndl(SolutionPtr el_sol) {
		IntegerPtr integer = std::dynamic_pointer_cast<Integer>(el_sol);
		MetaInt val = Concretize(context_.Solver(), integer->Get());
		if (GetChar(val) == (unsigned long)'\0')
			return true;
		else
			return false;
	}

	void SolutionPrinter::PrintString(ArrayPtr array, std::ostream& file) {
		bool end_reached = false;
		std::string str;
		file << "\"";
		int i = 0;
		int len = array->GetSize();
		while (i < len) {
			SolutionPtr el_sol = array->GetElement(i);
			if (IsEndl(el_sol))
				break;
			PrintSolution(el_sol, file);
			++i;
		}
		file << "\"";
		file << "{";
		while (i < len) {
			SolutionPtr el_sol = array->GetElement(i);
			PrintSolution(el_sol, file);
			if (i+1 < len) file << ",";
			//file << "_";
			++i;
		}
		file << "}";
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
#ifdef CHAR_PRINTING
			if (val.getBitWidth() == 8)
			  PrintASCII(val, file);
			else
#endif
			  file << val;
				
		} else if (utils::instanceof<Pointer>(sol)) {
			PointerPtr pointer = std::dynamic_pointer_cast<Pointer>(sol);
			file << "&";
			PrintSolution(pointer->Dereference(), file);
			//assert (! "not impl");
		} else if (utils::instanceof<Array>(sol)) {
			ArrayPtr array = std::dynamic_pointer_cast<Array>(sol);
#ifdef STRING_PRINTING
			if (array->IsString())
				PrintString(array, file);
			else
#endif
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
		file << " :=> ";
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
