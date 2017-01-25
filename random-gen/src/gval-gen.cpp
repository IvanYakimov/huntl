#include "gval-gen.hpp"

using namespace llvm;

char buff1[] = "Hello";
char buff2[] = " world!";

GValGenPtr GStrGen::Create() {
  return std::make_shared<GStrGen>();
}

void GStrGen::Update() {
  static int num = 0;
  if (num == 0) {
    num++;
  value = PTOGV((void*)buff1);
  } else {
    value = PTOGV((void*)0);
  }
    
  //  value = PTOGV((void*)buffer_);
}
