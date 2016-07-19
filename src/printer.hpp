#ifndef __PRINTER_HPP__
#define __PRINTER_HPP__

#include "llvm/IR/InstVisitor.h"
#include <string>

namespace utils {
class Printer {
//template<class... Args>
//std::string PrintType(const llvm::Value *val, Args... args);
//std::string PrintType(const llvm::Value *val);
public:
	template<class... Args>
	static std::string Do(Args... args) {
		return + "[ " + PrintType(args...) + " ]";
	}

private:
	static std::string PrintType(const llvm::Value *val);

	template<class... Args>
	static std::string PrintType(const llvm::Value *val, Args... args) {
		return PrintType(val) + " " + PrintType(args...);
	}
};
}

#endif
