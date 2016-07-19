#ifndef __CONVERTER_HPP__
#define __CONVERTER_HPP__

#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Value.h"
#include <iostream>
#include <string>

namespace utils {
	std::string ToString(const llvm::Value& value);
}

#endif
