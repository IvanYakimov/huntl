#include "gval-gen.hpp"

using namespace llvm;

GValGenPtr GStrGen::Create() {
  return std::make_shared<GStrGen>();
}

void GStrGen::Update() {
  int num = std::rand() % 3;
  if (num == 0) {
    for (int i = 0; i < sizeof(buffer_); i++) {
      int k = std::rand() % sizeof(symbols_);
      char val = symbols_[k];
      buffer_[i] = val;
    }
    value = PTOGV((void*)buffer_);
  } else if (num == 1){
    value = PTOGV((void*)"");
  } else if (num == 2) {
    value = PTOGV((void*)"");
  } else {
    assert (not "implemented");
  }
}
