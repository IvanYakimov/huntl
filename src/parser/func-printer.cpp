// based on http://llvm.org/docs/WritingAnLLVMPass.html tutorial

// USEFUL REFERENCES:
// * learn llvm by example
// https://gist.github.com/alloy/d86b007b1b14607a112f
// * Analyse llvm code
// http://www.cs.cmu.edu/afs/cs.cmu.edu/academic/class/15745-s13/public/lectures/L6-LLVM-Detail-1up.pdf

# include "llvm/Pass.h"
# include "llvm/IR/Function.h"
# include "llvm/IR/Instruction.h"
# include "llvm/IR/InstIterator.h"
# include "llvm/IR/InstVisitor.h"
# include "llvm/Support/raw_ostream.h"

# include <set>

using namespace llvm;

namespace
{
  struct FuncPrinter : public FunctionPass
  {
    static char ID;
    FuncPrinter () : FunctionPass (ID) {}
    bool runOnFunction (Function &F) override;
  };
}

char FuncPrinter::ID = 0;
static RegisterPass <FuncPrinter> X("FuncPrinter", "Func Printer Pass",
				    false /* Only looks at CFG */,
				    false /* Analysis Pass */);

// TODO: add mapping for temporary "registy names" like %1, %2, ...
// http://llvm.org/docs/FAQ.html#what-api-do-i-use-to-store-a-value-to-one-of-the-virtual-registers-in-llvm-ir-s-ssa-representation

// TODO: check traversing order
// http://stackoverflow.com/questions/32853884/how-does-the-llvm-instvisitor-traverse-ir
struct Interpreter : public InstVisitor <Interpreter>
{
  Interpreter () {}

  // --------------------------------------------------
  // Specific Instruction type classes
  void visitReturnInst (const ReturnInst &inst)
  {
    errs () << "ret";
    errs () << "\n";
  }

  void visitBranchInst (const BranchInst &inst)
  {
    errs () << "br";
    errs () << "\n";
  }

  void visitICmpInst (const ICmpInst &inst)
  {
    errs () << "icmp";
    errs () << "\n";
  }
  
  void visitAllocaInst (const AllocaInst &inst)
  {
    errs () << "alloca inst";
    auto op_num = inst.getNumOperands ();
    errs () << ": " << op_num << " ops";
    errs () << "\n";
  }

  void visitLoadInst (const LoadInst &inst)
  {
    // http://www.isi.edu/~pedro/Teaching/CSCI565-Spring14/Projects/Project1-LLVM/docs/Project1-LLVM.pdf
    errs () << "load";
    auto op_num = inst.getNumOperands ();
    errs () << ": " << op_num << " ops. ";
    errs () << "\n";
  }

  void visitStoreInst (const StoreInst &inst)
  {
    // store i32 %x, i32* %2, align 4
    errs () << "store ";
    auto op_num = inst.getNumOperands ();
    if (Argument *op0 = dyn_cast <Argument> (inst.getOperand (0)))
      {
	// i32 %x
	Type *type = op0->getType ();
	if (type->isIntegerTy ())
	  {
	    unsigned width = type->getIntegerBitWidth ();
	    errs () << "i" << width << " ";
	  }
	StringRef name = op0->getName ();
	errs () << "%" << name.str () << ", ";
      }
    if (AllocaInst *op1 = dyn_cast <AllocaInst> (inst.getOperand (1)))
      {
	// i32* %2
	Type *type = op1->getAllocatedType ();
	if (type->isIntegerTy ())
	  {	    
	    unsigned width = type->getIntegerBitWidth ();
	    errs () << "i" << width;
	    // this is a pointer
	    errs () << "* ";
	  }
	
	unsigned allign = op1->getAlignment ();
	errs () << " align " << allign;
      }
    errs () << "\n";
  }
};

/// Print function
bool FuncPrinter::runOnFunction (Function &F)
{
  errs () << "define ";
  errs () << "@" << F.getName () << "\n";

  // Visit instructions
  Interpreter interpreter;
  interpreter.visit (F);

  // ----------------------------------------
  // TODO: remove, this is just for checking the instruction visitors
  std::set <Instruction*> WorkList;
  for (inst_iterator i = inst_begin (F), e = inst_end (F); i != e; i++)
    WorkList.insert (&*i);

  // it is very strange, but perhaps this loop visits instructions in incorrect order o0 !?..
  while (!WorkList.empty ())
    {
      // todo: apply Instruction Visitors http://llvm.org/doxygen/InstVisitor_8h-source.html
      // or just get operands http://stackoverflow.com/questions/8651829/getting-the-operands-in-an-llvm-instruction
      Instruction *I = *WorkList.begin ();
      WorkList.erase (WorkList.begin ());
      // /*disabled */ errs ().write_escaped (I->getOpcodeName ()) << "\n";
    }
  // ----------------------------------------
    
  // No transformations.
  return false;
}
