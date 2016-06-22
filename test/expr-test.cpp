#include <cvc4/cvc4.h>
#include <iostream>
#include <memory>

class wrapper {
public:
	wrapper(CVC4::BitVectorType bv) {
		bvt = bv;
	}

	CVC4::BitVectorType bvt;
};

int main () {
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
