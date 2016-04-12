SHELL = /bin/sh

INTERPRETER = matcher.o executor.o
INTERPRETER_TEST = test-matcher.o

CXX = g++
CXXFLAGS = -fdiagnostics-color=always -g -std=c++14 -fpic -rdynamic \
	$(filter-out -g -fno-exceptions -O2 -std=c++11, $(LLVMFLAGS)) $(DBGFLAGS) \
	-Wno-deprecated
LLVMFLAGS = $(shell llvm-config --cxxflags)

SRC = ../../src
TST = .

vpath %.cpp $(SRC)/interpreter $(TST)/interpreter/
vpath %.hpp $(SRC)/interpreter
vpath %.c 	$(SRC)/interpreter
		
program.so: shared.o 
	$(CXX) -shared $< -o $@ 

shared.o: $(INTERPRETER) $(INTERPRETER_TEST)
	ld -r $^ -o $@ 

$(INTERPRETER_TEST):
$(INTERPRETER):
%.o: %.cpp %.hpp
	$(CXX) -c $< -o $@ $(CXXFLAGS) 
	
.PHONY: clean
clean:
	@rm -vf *~ *.o *.out *.so
	@rm -vf *.ll api-pattern.cpp
	@rm -vf \#*\#

# < helpers ------------------------------------------------
.PHONY: run
run:	program.so test.ll
	opt -load=./program.so < test.ll > /dev/null -test
	
test.ll: test.c
	clang -S -emit-llvm $< -Wimplicit-int
# helpers ----------------------------------------------- />	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	