SHELL = /bin/sh

ALL_UNITS = $(shell ls ../src)
CPP_UNITS = $(filter %.cpp, $(ALL_UNITS))
OBJ = $(CPP_UNITS:.cpp=.o)

CXX = g++
CXXFLAGS = -fdiagnostics-color=always -g -std=c++14 -fpic -rdynamic -Wno-deprecated
LLVM_CXX = $(filter-out -g -fno-exceptions -O2 -std=c++11, $(shell llvm-config --cxxflags))
CLANG = clang -S -emit-llvm -O0 -Wint-conversion

SRC = ../src

vpath %.cpp $(SRC) 
vpath %.hpp $(SRC)

luna.so: $(OBJ)
	$(CXX) -shared $^ -o $@ $(CXXFLAGS) $(LLVM_CXX)

$(OBJ):
%.o: %.cpp %.hpp
	$(CXX) -c $< -o $@ $(CXXFLAGS) 

.PHONY: clean
clean:
	@rm -vf *~ *.o *.so *.ll \#*\# *gcov *gcda *gcno *c *out *trace
