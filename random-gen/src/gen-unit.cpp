#include "gen-unit.hpp"

using namespace llvm;
using std::list; using std::vector;

void PrintGenericValue(raw_ostream &output, GenericValue gval) {
  void* tmp = GVTOP(gval);
  char* s = (char*)tmp;
  if (s != nullptr)
    output << "\"" << s << "\" ";
  else
    output << "nullptr ";
}

void GenUnit::Run(Function& func) {
  std::string ostatus;
  raw_fd_ostream output("tmp.txt", ostatus, sys::fs::OpenFlags::F_RW);
  //TODO: s handling
  
  //  raw_fd_ostream output(1, false, false);
  //  output << "\n\n\nHELLO !!!!\n";

  output << "//##################################\n";
  output << "// Test suite for the " << func.getName() << " function:\n";
  list<GValGenPtr> gen_list;
  Module *mod = func.getParent();
  ExecutionEngine *jit = EngineBuilder(mod).create();

  // Initialize list of generators.
  for (auto it = func.arg_begin(); it != func.arg_end(); ++it) {
    auto ty = it->getType();
    if (ty->isPointerTy()) {
      if (ty->getContainedType(0)->isIntegerTy(8)) {
	auto gen = GStrGen::Create();
	gen_list.push_back(gen);
      } else {
	assert (false and "bad pointer type");
      }
    } else if (ty->isIntegerTy()) {
      //TODO:
      errs() << "int";
      assert (false and "not implemented");
    }  else
      assert (false and "bad type of argument");
  }

  // Produce values for arguments by the generators.
  int n = (func.getFunctionType()->getNumParams());
  vector<GenericValue> gargs(n);
  int i = 0;
  for (auto it = gen_list.begin(); it != gen_list.end(); it++) {
    auto gen = *it; gen->Update();
    GenericValue gval = gen->value;
    gargs[i] = gval;
    i++;

    PrintGenericValue(output, gval);
    /*
    void* tmp = GVTOP(gval);
    char* s = (char*)tmp;
    if (s != nullptr)
      output << s << " ";
    else
      output << "nullptr ";
    */
  }

  gargs[1] = GenericValue(0);

  output << ":=> ";

  pid_t pid = fork();
  
  if (pid== 0) {
    // CHILD PROCESS
    // Run the target function in a safe environment
    GenericValue gres = jit->runFunction(&func, gargs);

    // If successful, print the results.
    auto ret_ty = func.getFunctionType()->getReturnType();
    if (ret_ty->isPointerTy()) {
      PrintGenericValue(output, gres);
      /*
      void* res = GVTOP(gres);
      char* str = (char*)res;
      errs() << str;
      if (str != nullptr)
	output << str << " ";
      else
	output << "nullptr ";
      */
    } else if (ret_ty->isIntegerTy(32)) {
      errs() << gres.IntVal;
    }
  } else if (pid > 0) {
    // PARENT PROCESS
    int wstatus;
    wait(&wstatus);
    // Handle the waiting status:
    if (WIFEXITED(wstatus)) {
      //errs() << "\nOK";
    } else {
      output << "CRASH";
    }
  } else {
    errs() << "Error on forking. Stop\n";
    exit(0);
  }

  // Else report the error

  output << "\n";
  
  /*
    Module *mod = func.getParent();
    ExecutionEngine *jit = EngineBuilder(mod).create();
    char buff[80] = "Hello ";
    char target[] = "world!";
    std::vector<GenericValue> args(2);
    args[0] = PTOGV(buff);
    args[1] = PTOGV(target);
    GenericValue gres = jit->runFunction(&func, args);
    //  void* res = GVTOP(gres);
    //  int *val = (int*)res;
  
    errs() << "val = " << gres.IntVal << "\n";
    //char* str = (char*)res;
    //  errs() << str;

    errs() << "\nend\n";
  */

  errs() << "// Test suite generated successfully\n";
}

