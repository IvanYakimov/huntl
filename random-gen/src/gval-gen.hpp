#ifndef __GVAL_GEN_HPP__
#define __GVAL_GEN_HPP__

#include <memory>
#include <cstdlib>
#include <iostream>
#include <ctime>

#include "llvm/ExecutionEngine/GenericValue.h"

using GValPtr = std::shared_ptr<llvm::GenericValue>;

class GValGen {
public:
  virtual void Update() = 0;
  llvm::GenericValue value;
};

using GValGenPtr = std::shared_ptr<GValGen>;

class GIntGen : public GValGen {
public:
  static GValGenPtr Create();
  virtual void Update();
};

class GStrGen : public GValGen {
public:
  static GValGenPtr Create();
  virtual void Update();
private:
  char buffer_[10] = "";
  char symbols_[10] = {'a','f','k','v','e',' ',' ','\0','\0','\0'};
};

#endif
