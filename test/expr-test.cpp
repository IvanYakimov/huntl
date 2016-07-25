#include <cvc4/cvc4.h>
#include <iostream>
#include <memory>

#include "gtest/gtest.h"

class wrapper {
public:
	wrapper(CVC4::BitVectorType bv) {
		bvt = bv;
	}

	CVC4::BitVectorType bvt;
};

class ExprTest : public ::testing::Test {

};

TEST_F(ExprTest, bv_size) {
	using namespace CVC4;
	CVC4::ExprManager em;
	CVC4::BitVectorType bv32 = em.mkBitVectorType(32);
	std::cout << "bv type: " << sizeof(bv32) << std::endl;
	auto pt = std::make_shared<wrapper>(bv32);
	std::cout << "smart pointer: " << sizeof(pt) << std::endl;
	CVC4::Expr x = em.mkBoundVar(bv32);
	std::cout << "var: " << sizeof(x) << std::endl;
	CVC4::Expr c = em.mkConst(CVC4::BitVector(32, 32U));
	std::cout << "c: " << sizeof(c) << std::endl;
	CVC4::Expr x_eq_c = em.mkExpr(CVC4::Kind::BITVECTOR_AND, x, c);
	std::cout << "x = c: " << sizeof(x_eq_c) << std::endl;
}

void Init(CVC4::SmtEngine & smt) {
	smt.setOption("incremental", CVC4::SExpr("true"));
	smt.setOption("produce-models", CVC4::SExpr("true"));
	smt.setOption("rewrite-divk", CVC4::SExpr("true"));
	smt.setLogic("QF_BV");
}

// see: http://cvc4.cs.nyu.edu/wiki/Tutorials#bitvectors
TEST_F(ExprTest, trunc) {
	using namespace CVC4;
	ExprManager em;
	SmtEngine smt(&em);
	Init(smt);
	Type bv16 = em.mkBitVectorType(16);
	Type bv32 = em.mkBitVectorType(32);
	Expr y = em.mkVar("y", bv16);
	Expr x = em.mkVar("x", bv32);
	Expr c1 = em.mkConst(BitVector(16,Integer(-28)));
	Expr zext32 = em.mkConst(CVC4::BitVectorSignExtend(16));
	Expr c2 = em.mkExpr(zext32, c1);
	Expr y_eq_c1 = em.mkExpr(Kind::EQUAL, y, c1);
	Expr x_eq_c2 = em.mkExpr(Kind::EQUAL, x, c2);
	std::cout << c1 << std::endl;
	std::cout << c2 << std::endl;
	smt.assertFormula(y_eq_c1);
	smt.assertFormula(x_eq_c2);
	ASSERT_EQ(smt.checkSat(), Result::SAT);
	std::cout << "c1 = " << smt.getValue(c1) << std::endl;
	std::cout << "y = " << smt.getValue(y) << std::endl;
	std::cout << "c2 = " << smt.getValue(c2) << std::endl;
	std::cout << "ty(c2) = " << c2.getType() << std::endl;
	std::cout << "x = " << smt.getValue(x) << std::endl;

}













