// Generated by llvm2cpp - DO NOT MODIFY!

#include <llvm/Pass.h>
#include <llvm/PassManager.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CallingConv.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRPrintingPasses.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/MathExtras.h>
#include <algorithm>
using namespace llvm;

Module* makeLLVMModule();

int main(int argc, char**argv) {
  Module* Mod = makeLLVMModule();
  verifyModule(*Mod, PrintMessageAction);
  PassManager PM;
  PM.add(createPrintModulePass(&outs()));
  PM.run(*Mod);
  return 0;
}


Module* makeLLVMModule() {
 // Module Construction
 Module* mod = new Module("array.ll", getGlobalContext());
 mod->setDataLayout("0x1e4dd58");
 mod->setTargetTriple("x86_64-pc-linux-gnu");
 
 // Type Definitions
 ArrayType* ArrayTy_0 = ArrayType::get(IntegerType::get(mod->getContext(), 8), 12);
 
 PointerType* PointerTy_1 = PointerType::get(ArrayTy_0, 0);
 
 std::vector<Type*>FuncTy_2_args;
 FunctionType* FuncTy_2 = FunctionType::get(
  /*Result=*/IntegerType::get(mod->getContext(), 32),
  /*Params=*/FuncTy_2_args,
  /*isVarArg=*/false);
 
 PointerType* PointerTy_3 = PointerType::get(IntegerType::get(mod->getContext(), 8), 0);
 
 std::vector<Type*>FuncTy_5_args;
 FuncTy_5_args.push_back(PointerTy_3);
 FunctionType* FuncTy_5 = FunctionType::get(
  /*Result=*/Type::getVoidTy(mod->getContext()),
  /*Params=*/FuncTy_5_args,
  /*isVarArg=*/true);
 
 PointerType* PointerTy_4 = PointerType::get(FuncTy_5, 0);
 
 
 // Function Declarations
 
 Function* func_main = mod->getFunction("main");
 if (!func_main) {
 func_main = Function::Create(
  /*Type=*/FuncTy_2,
  /*Linkage=*/GlobalValue::ExternalLinkage,
  /*Name=*/"main", mod); 
 func_main->setCallingConv(CallingConv::C);
 }
 AttributeSet func_main_PAL;
 {
  SmallVector<AttributeSet, 4> Attrs;
  AttributeSet PAS;
   {
    AttrBuilder B;
    B.addAttribute(Attribute::NoUnwind);
    B.addAttribute(Attribute::UWTable);
    PAS = AttributeSet::get(mod->getContext(), ~0U, B);
   }
  
  Attrs.push_back(PAS);
  func_main_PAL = AttributeSet::get(mod->getContext(), Attrs);
  
 }
 func_main->setAttributes(func_main_PAL);
 
 Function* func_func = mod->getFunction("func");
 if (!func_func) {
 func_func = Function::Create(
  /*Type=*/FuncTy_5,
  /*Linkage=*/GlobalValue::ExternalLinkage,
  /*Name=*/"func", mod); // (external, no body)
 func_func->setCallingConv(CallingConv::C);
 }
 AttributeSet func_func_PAL;
 {
  SmallVector<AttributeSet, 4> Attrs;
  AttributeSet PAS;
   {
    AttrBuilder B;
    PAS = AttributeSet::get(mod->getContext(), ~0U, B);
   }
  
  Attrs.push_back(PAS);
  func_func_PAL = AttributeSet::get(mod->getContext(), Attrs);
  
 }
 func_func->setAttributes(func_func_PAL);
 
 // Global Variable Declarations

 
 GlobalVariable* gvar_array__str = new GlobalVariable(/*Module=*/*mod, 
 /*Type=*/ArrayTy_0,
 /*isConstant=*/true,
 /*Linkage=*/GlobalValue::PrivateLinkage,
 /*Initializer=*/0, // has initializer, specified below
 /*Name=*/".str");
 gvar_array__str->setAlignment(1);
 
 // Constant Definitions
 Constant *const_array_6 = ConstantDataArray::getString(mod->getContext(), "hello world", true);
 std::vector<Constant*> const_ptr_7_indices;
 ConstantInt* const_int32_8 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));
 const_ptr_7_indices.push_back(const_int32_8);
 const_ptr_7_indices.push_back(const_int32_8);
 Constant* const_ptr_7 = ConstantExpr::getGetElementPtr(gvar_array__str, const_ptr_7_indices);
 ConstantInt* const_int32_9 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("2"), 10));
 ConstantInt* const_int32_10 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("28"), 10));
 
 // Global Variable Definitions
 gvar_array__str->setInitializer(const_array_6);
 
 // Function Definitions
 
 // Function: main (func_main)
 {
  
  BasicBlock* label_11 = BasicBlock::Create(mod->getContext(), "",func_main,0);
  
  // Block  (label_11)
  std::vector<Value*> void_12_params;
  void_12_params.push_back(const_ptr_7);
  void_12_params.push_back(const_int32_9);
  void_12_params.push_back(const_int32_10);
  CallInst* void_12 = CallInst::Create(func_func, void_12_params, "", label_11);
  void_12->setCallingConv(CallingConv::C);
  void_12->setTailCall(false);
  AttributeSet void_12_PAL;
  void_12->setAttributes(void_12_PAL);
  
  ReturnInst::Create(mod->getContext(), const_int32_8, label_11);
  
 }
 
 return mod;
}