// Google Test
#include "gtest/gtest.h"
#include "../../src/interpreter/memory.hpp"

#include <exception>

namespace interpreter {
	class MemoryTest : public ::testing::Test {

	};

	TEST_F(MemoryTest, Read) {
		Memory m;
	}
}
