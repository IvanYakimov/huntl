#include "converter.hpp"
namespace utils {
	std::string ToString(const llvm::Value& value){
		std::string res;
		llvm::raw_string_ostream rsos(res);
		rsos << value;
		return rsos.str();
	}
}
