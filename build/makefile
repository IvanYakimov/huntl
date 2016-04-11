SHELL = /bin/sh

SOLVER = kind.o type.o expr.o expr-manager.o value.o cvc4-engine.o \
	width.o expr-manager-helper.o exception.o object.o ismt-engine.o
SOLVER_TEST = test-runner.o test-value.o test-type.o test-expr.o test-expr-manager.o test-cvc4-engine.o test-width.o \
	test-z3-engine.o

INTERPRETER = interpreter.o pattern-matcher.o executor.o memory.o state.o 
INTERPRETER_TEST = test-memory.o

UTILS = 

OBJ_TEST = $(SOLVER_TEST) $(INTERPRETER_TEST)
OBJ = $(SOLVER) $(INTERPRETER) $(UTILS)

CXX = g++
CXXFLAGS = -fdiagnostics-color=always -g -std=c++14 -fpic -rdynamic \
	$(filter-out -g -fno-exceptions -O2 -std=c++11, $(LLVMFLAGS)) $(DBGFLAGS) \
	-Wno-deprecated
LDFLAGS = $(CVC4FLAGS) $(Z3FLAGS)
CVC4FLAGS = -lcvc4 -lgmp  
Z3FLAGS = /usr/lib/libz3.so
LLVMFLAGS = $(shell llvm-config --cxxflags)
DBGFLAGS = -D DBG -U NDEBUG

SRC = ../src
TST = ../test

vpath %.cpp $(SRC)/solver $(TST)/solver/
vpath %.cpp $(SRC)/interpreter $(TST)/interpreter/
vpath %.cpp $(SRC)/utils
vpath %.hpp $(SRC)/solver
vpath %.hpp $(SRC)/interpreter
vpath %.hpp $(SRC)/utils
vpath %.c 	$(SRC)/interpreter
		
program.so: shared.o 
	$(CXX) -shared $< -o $@ $(CXXFLAGS) 

shared.o: $(INTERPRETER) #$(SOLVER) $(UTILS)
	ld -r $^ -o $@

solvertest.out: $(SOLVER_TEST) $(SOLVER) $(LDFLAGS)
	$(CXX) $^ -o $@ -lgtest -pthread $(CXXFLAGS)
	
interpreter-test.out: $(INTERPRETER_TEST) memory.o state.o test-runner.o $(LDFLAGS)
	$(CXX) $^ -o $@ -lgtest -pthread $(CXXFLAGS)
	
#INTERPRETERtest.out

$(SOLVER_TEST):
$(SOLVER):
$(INTERPRETER_TEST):
$(INTERPRETER):
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
	opt -load=./program.so < test.ll > /dev/null -ll-voyager

gdb: program.so test.ll
	gdb opt	
# helpers ----------------------------------------------- />	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	