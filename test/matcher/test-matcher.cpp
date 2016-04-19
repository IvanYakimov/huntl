#include "test-matcher.hpp"

//useful link: http://llvm.org/releases/3.5.0/docs/tutorial/LangImpl3.html

using namespace llvm;

//TODO: total refactoring!!!
class MatcherTest : public ::testing::Test {
public:
	LLVMContext &context_ ;// = getGlobalContext();
	IRBuilder<> builder_ ;//(getGlobalContext());
	Module *module_ = nullptr;

	Function *func_ = nullptr;
	BasicBlock *entry_ = nullptr;
	interpreter::MatcherStub matcher_;

	MatcherTest() : builder_(getGlobalContext()), context_(getGlobalContext()) {
		module_ = new Module("test", context_);
	}

	~MatcherTest() {
		delete module_;
	}

	// <-- Helpers
	AllocaInst* Alloca32(const char *name) {
		AllocaInst* res = builder_.CreateAlloca(Type::getInt32Ty(module_->getContext()), 0, name);
		res->setAlignment(4);
		return res;
	}

	ConstantInt* I32(uint32_t val) {
		return ConstantInt::get(module_->getContext(), APInt(32, val, true));
	}

	ConstantInt* I1(bool val) {
		if (val == true)
			return ConstantInt::get(module_->getContext(), APInt(1, 1, true));
		else
			return ConstantInt::get(module_->getContext(), APInt(1, 0, true));
	}

	ConstantInt* True() {
		return I1(true);
	}

	ConstantInt* False() {
		return I1(false);
	}

	StoreInst* Store(Value* what, Value* where) {
		return builder_.CreateStore(what, where);
	}

	LoadInst* Load(Value *from) {
		return builder_.CreateLoad(from);
	}

	ReturnInst* Ret(Value *what) {
		return builder_.CreateRet(what);
	}

	Value* EQ(Value* lhs, Value* rhs) {
		return builder_.CreateICmpEQ(lhs, rhs);
	}

	Value* NE(Value* lhs, Value* rhs) {
		return builder_.CreateICmpNE(lhs, rhs);
	}

	BranchInst* IfThanElse(Value* cond, BasicBlock* iftrue, BasicBlock* iffalse) {
		return builder_.CreateCondBr(cond, iftrue, iffalse);
	}

	BranchInst* Jump(BasicBlock* dest) {
		return builder_.CreateBr(dest);
	}

	Value* Add(Value* lhs, Value* rhs) {
		return builder_.CreateAdd(lhs, rhs);
	}

	//TODO: Make variadic
	PHINode* Phi(Type* ty) {
		return builder_.CreatePHI(ty, 0);
	}

	Value* ZExt(Value* val, Type* ty){
		return builder_.CreateZExt(val, ty);
	}

	Type* Int32Ty() {
		return Type::getInt32Ty(context_);
	}

	Type* Int1Ty() {
		return Type::getInt1Ty(context_);
	}

	// -->

	BasicBlock* Block(const char* name) {
		return BasicBlock::Create(context_, name, func_);
	}

	void Enter(BasicBlock* block) {
		builder_.SetInsertPoint(block);
	}


	//Initializators
	void InitInt32Func() {
		FunctionType *void_func_ty_ = FunctionType::get(Type::getInt32Ty(context_), false);
		func_ = Function::Create(void_func_ty_, Function::InternalLinkage, "test", module_);
	}

	void InitVoidFunc() {
		FunctionType *void_func_ty_ = FunctionType::get(Type::getVoidTy(context_), false);
		func_ = Function::Create(void_func_ty_, Function::InternalLinkage, "test", module_);
	}

	// Matching
	void MatchOnFunc() {
		errs() << *func_ << "\n";
		ASSERT_FALSE(verifyFunction(*func_));
		// If there are no errors, the function returns false.

		for (Function::iterator i = func_->begin(), e = func_->end(); i != e; ++i)
			matcher_.visit(i);
	}

	// Test confuguration
	virtual void SetUp() {
		InitInt32Func();
		entry_ = Block("entry");
		Enter(entry_);
	}

	virtual void TearDown() {
		MatchOnFunc();
	}
};

TEST_F(MatcherTest, ret__const) {
	auto ret = Ret(I32(42));
}

TEST_F(MatcherTest, alloca_store_load_ret) {
	auto x = Alloca32("x");
	auto store_x = Store(I32(2), x);
	auto load_x = Load(x);
	auto ret = Ret(load_x);
}

TEST_F(MatcherTest, if_than_else) {
	auto true_branch = Block("true-branch");
	auto false_branch = Block("false-branch");
	auto x = Alloca32("x");
	auto icmp = EQ(Load(x), I32(2));
	auto jump = IfThanElse(icmp, true_branch, false_branch);
	Enter(true_branch); {
		Ret(I32(1));
	}
	Enter(false_branch); {
		Ret(I32(-1));
	}
}

TEST_F(MatcherTest, jump) {
	auto dest = Block("dest");
	auto jump = Jump(dest);
	Enter(dest); {
		Ret(I32(0));
	}
}

TEST_F(MatcherTest, binop) {
	auto x = Alloca32("x");
	auto y = Alloca32("y");
	auto binop = Add(Load(x), Load(y));
	BinaryOperator* tmp = llvm::dyn_cast<BinaryOperator>(binop);
	Instruction::BinaryOps opcode = tmp->getOpcode();
	std::string name = tmp->getOpcodeName();
	Ret(binop);
}

TEST_F(MatcherTest, phi_node) {
	auto more_cmp = Block("more_cmp");
	auto phi_node = Block("phi_node");
	auto x = Alloca32("x");
	auto y = Alloca32("y");
	auto cmp_x = NE(Load(x), I32(0));
	auto br1 = IfThanElse(cmp_x, phi_node, more_cmp);
	Value* cmp_y;
	Enter(more_cmp); {
		cmp_y = NE(Load(y), I32(0));
		auto br2 = Jump(phi_node);
	}
	Enter(phi_node); {
		PHINode* phi = Phi(Int1Ty());
		phi->addIncoming(I1(true), entry_);
		phi->addIncoming(cmp_y, more_cmp);
		auto zext = ZExt(phi, Int32Ty());
		auto ret = Ret(zext);
	}
}

int main(int argc, char** argv, char **env) {
	::testing::InitGoogleTest(&argc, argv);
	return RUN_ALL_TESTS();
}











