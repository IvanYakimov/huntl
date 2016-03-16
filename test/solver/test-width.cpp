#include "gtest/gtest.h"
#include "../../src/solver/width.hpp"

#include <list>

using namespace std;


namespace solver {
	class CommonTypesTest : public ::testing::Test {

	};

	TEST_F(CommonTypesTest, width__from_size_t__to_int__to_string) {
		using the_tuple = tuple<Width, size_t, int, string>;
		using the_list = list<the_tuple>;

		auto checker = [&] (the_tuple tpl) {
			auto width = get<0>(tpl);
			auto size = get<1>(tpl);
			auto integer = get<2>(tpl);
			auto str = get<3>(tpl);
			ASSERT_EQ(width, width::from_size_t(size));
			ASSERT_EQ(integer, width::to_int(width));
			ASSERT_EQ(str, width::to_string(width));
		};

		the_list val_list = {
				make_tuple(Width::w8, 1, 8, "8"),
				make_tuple(Width::w16, 2, 16, "16"),
				make_tuple(Width::w32, 4, 32, "32"),
				make_tuple(Width::w64, 8, 64, "64")
		};

		for_each(val_list.begin(), val_list.end(), checker);
	}
}














