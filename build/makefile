SHELL = /bin/sh

SOLVER = expr.o expr-factory.o cvc4-engine.o
SOLVER_TEST = test-runner.o test-expr.o test-expr-factory.o test-cvc4-engine.o
PARSER = parser.o pattern-matcher.o interpreter.o local-memory.o
PARSER_TEST = 
UTILS = interruption.o
OBJ_TEST = $(SOLVER_TEST) $(PARSER_TEST)
OBJ = $(SOLVER) $(PARSER) $(UTILS)
CXX = g++
CXXFLAGS = -fdiagnostics-color=always -g -std=c++14 -fpic -rdynamic $(filter-out -g -fno-exceptions -O2 -std=c++11, $(LLVMFLAGS)) $(DBGFLAGS)
LDFLAGS = -lcvc4 -lgmp
LLVMFLAGS = $(shell llvm-config --cxxflags)
DBGFLAGS = -D DBG
SRC = ../src
TST = ../test

vpath %.cpp $(SRC)/solver $(TST)/solver/
vpath %.cpp $(SRC)/parser
vpath %.cpp $(SRC)/utils
vpath %.hpp $(SRC)/solver $(TST)/solver/
vpath %.hpp $(SRC)/parser
vpath %.hpp $(SRC)/utils
vpath %.c 	$(SRC)/parser
		
program.so: shared.o 
	$(CXX) -shared $< -o $@ $(CXXFLAGS) 

shared.o: $(PARSER) $(SOLVER) $(UTILS)
	ld -r $^ -o $@

solvertest.out: $(SOLVER_TEST) $(SOLVER) $(LDFLAGS)
	$(CXX) $^ -o $@ -lgtest -pthread $(CXXFLAGS)
	
#parsertest.out

$(SOLVER_TEST):
$(SOLVER):
$(PARSER_TEST):
$(PARSER):
$(UTILS):
%.o: %.cpp %.hpp
	$(CXX) -c $< -o $@ $(CXXFLAGS) 
	
.PHONY: clean
clean:
	@rm -vf *~ *.o *.out *.so
	@rm -vf *.ll api-pattern.cpp
	@rm -vf \#*\#

# < helpers ------------------------------------------------
test.ll: test.c
	clang -S -emit-llvm $< -Wimplicit-int

api-pattern.cpp: test.ll
	llc -march=cpp $< -o api-pattern.cpp

.PHONY: run
run:	program.so test.ll
	opt -load=./program.so < test.ll > /dev/null -Parser

gdb: parser.so test.ll
	gdb opt	
# helpers ----------------------------------------------- />	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	