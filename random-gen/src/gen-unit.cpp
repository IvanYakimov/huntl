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
  std::srand(std::time(0));
  std::string ostatus;
  raw_fd_ostream output("tmp.txt", ostatus, sys::fs::OpenFlags::F_RW);

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
  }

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
    } else if (ret_ty->isIntegerTy(32)) {
      errs() << gres.IntVal;
    }
  } else if (pid > 0) {
    // PARENT PROCESS
    int wstatus;
    wait(&wstatus);
    // Handle the waiting status:
    if (WIFEXITED(wstatus)) {
      ;
    } else {
      output << "CRASH";
    }
  } else {
    errs() << "Error on forking. Stop\n";
    exit(0);
  }

  // Else report the error

  output << "\n";

  errs() << "// Test suite generated successfully\n";
}

