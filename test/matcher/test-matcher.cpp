#include "test-matcher.hpp"

//useful link: http://llvm.org/releases/3.5.0/docs/tutorial/LangImpl3.html

using namespace llvm;

class MatcherTest : public ::testing::Test {
public:
	interpreter::MatcherStub matcher_;

	// Matching
	void Match(Func &func) {
		Function* f = func.Get();
		errs() << *f << "\n";
		ASSERT_FALSE(verifyFunction(*f));
		// If there are no errors, the function returns false.

		for (Function::iterator i = f->begin(), e = f->end(); i != e; ++i)
			matcher_.visit(i);
	}
};

TEST_F(MatcherTest, ret__void) {
	VoidFunc f; {
		auto ret = f.RetVoid();
	}
	Match(f);
}

TEST_F(MatcherTest, ret__const) {
	Int32Func f; {
		auto ret = f.Ret(f.I32(42));
	}
	Match(f);
}

TEST_F(MatcherTest, alloca_store_load_ret) {
	Int32Func f; {
		auto x = f.Alloca32("x");
		auto store_x = f.Store(f.I32(2), x);
		auto load_x = f.Load(x);
		auto ret = f.Ret(load_x);
	}
	Match(f);
}

TEST_F(MatcherTest, if_than_else) {
	Int32Func f; {
		auto true_branch = f.Block("true-branch");
		auto false_branch = f.Block("false-branch");
		auto x = f.Alloca32("x");
		auto icmp = f.EQ(f.Load(x), f.I32(2));
		auto jump = f.IfThanElse(icmp, true_branch, false_branch);
		f.Enter(true_branch); {
			auto ret = f.Ret(f.I32(1));
		}
		f.Enter(false_branch); {
			auto ret = f.Ret(f.I32(-1));
		}
	}
	Match(f);
}

TEST_F(MatcherTest, jump) {
	Int32Func f; {
		auto dest = f.Block("dest");
		auto jump = f.Jump(dest);
		f.Enter(dest); {
			f.Ret(f.I32(0));
		}
	}
	Match(f);
}

TEST_F(MatcherTest, binop) {
	Int32Func f; {
		auto x = f.Alloca32("x");
		auto y = f.Alloca32("y");
		auto res = f.Alloca32("res");
		auto store_x = f.Store(f.I32(1), x);
		auto store_y = f.Store(f.I32(2), y);
		auto store_res = f.Store(f.I32(0), res);
		auto load_x = f.Load(x);
		auto load_y = f.Load(y);
		auto binop = f.Add(load_x, load_y);
		auto store_binop = f.Store(binop, res);
		auto load_res = f.Load(res);
		auto ret = f.Ret(load_res);
	}
	Match(f);
}

TEST_F(MatcherTest, phi_node) {
	Int32Func f; {
		auto more_cmp = f.Block("more_cmp");
		auto phi_node = f.Block("phi_node");
		auto x = f.Alloca32("x");
		auto y = f.Alloca32("y");
		auto cmp_x = f.NE(f.Load(x), f.I32(0));
		auto br1 = f.IfThanElse(cmp_x, phi_node, more_cmp);
		Value* cmp_y;
		f.Enter(more_cmp); {
			cmp_y = f.NE(f.Load(y), f.I32(0));
			auto br2 = f.Jump(phi_node);
		}
		f.Enter(phi_node); {
			PHINode* phi = f.Phi(f.Int1Ty());
			phi->addIncoming(f.I1(true), f.Entry());
			phi->addIncoming(cmp_y, more_cmp);
			auto zext = f.ZExt(phi, f.Int32Ty());
			auto ret = f.Ret(zext);
		}
	}
	Match(f);
}

int main(int argc, char** argv, char **env) {
	::testing::InitGoogleTest(&argc, argv);
	return RUN_ALL_TESTS();
}











