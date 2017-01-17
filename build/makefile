SHELL = /bin/sh

ALL_UNITS = $(shell ls ../src)
CPP_UNITS = $(filter %.cpp, $(ALL_UNITS))
OBJ = $(CPP_UNITS:.cpp=.o)

CXX = g++
CXXFLAGS = -fdiagnostics-color=always -g -std=c++14 -fpic -rdynamic -Wno-deprecated
CVC4FLAGS = -lcvc4 -lgmp  
LLVM_CXX = $(filter-out -g -fno-exceptions -O2 -std=c++11, $(shell llvm-config --cxxflags))
CLANG = clang -S -emit-llvm -O0 -Wint-conversion

SRC = ../src
BENCH =	../benchmarks
TESTER = ../readability

C_BENCH = $(shell ls ../benchmarks)
LL_BENCH = $(C_BENCH:.c=.o)

vpath %.cpp $(SRC) $(TESTER)
vpath %.hpp $(SRC) $(TESTER)
vpath %.c $(BENCH)
vpath %.h $(BENCH)

huntl.so: $(OBJ)
	$(CXX) -shared $^ -o $@ $(CVC4FLAGS) $(CXXFLAGS) $(LLVM_CXX)

estimate.out: estimate.o bigram-model.o
	$(CXX) $^ -o $@ 

$(OBJ):
%.o: %.cpp %.hpp
	$(CXX) -c $< -o $@ $(CXXFLAGS) 

$(C_BENCH):
%.ll: %.c
	$(CLANG) $^

.PHONY: clean
clean:
	@rm -vf *~ *.o *.so *.ll \#*\# *gcov *gcda *gcno *c *out *trace
