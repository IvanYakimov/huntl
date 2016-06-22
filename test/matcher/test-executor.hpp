#ifndef __TEST_EXECUTOR_HPP__
#define __TEST_EXECUTOR_HPP__

// GTEST
#include "gtest/gtest.h"

// PROJECT
#include "../../src/interpreter/executor.hpp"
#include "../../src/interpreter/memory.hpp"
#include "../../src/interpreter/memory-interface.hpp"
#include "../../src/interpreter/display-interface.hpp"
#include "../../src/interpreter/display.hpp"

// LLVM
#include "llvm/IR/Verifier.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"

// TEST
#include "ir-function-builder.hpp"

#endif /* __TEST_EXECUTOR_HPP__ */
