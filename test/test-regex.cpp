#ifndef __TEST_REGEX_HPP__
#define __TEST_REGEX_HPP__

#include <regex>
#include <string>
#include <iostream>

// gtest
#include "gtest/gtest.h"

class RegexTest : public ::testing::Test {
public:
};

TEST_F(RegexTest, mksym_INT) {
	std::string str_mksym_i32 ("mksym_i32");
	std::string str_function ("function");
	std::string str_test_smth ("test_smth");
	std::regex regex_mksym("mksym_");
	std::smatch m;
	auto res = std::regex_search(str_mksym_i32, m, regex_mksym);
	std::cout << res << std::endl;
	//std::for_each(m.begin(), m.end(), [](auto x) {std::cout << x; });
	std::cout << *m.begin() << std::endl;
	std::cout << m.empty() << std::endl;
	auto suffix = m.suffix();
	std::cout << m.suffix() << std::endl;
}

#endif











