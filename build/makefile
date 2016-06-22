SHELL = /bin/sh

SOLVER = kind.o bitvec.o expr.o object-builder.o cvc4-engine.o \
	object-builder-helper.o exception.o object.o ismt-engine.o core.o
SOLVER_TEST = test-runner.o test-expr.o test-object-builder.o test-cvc4-engine.o \
	test-z3-engine.o

INTERPRETER = interpreter.o matcher.o executor.o memory.o state.o voyager-pass.o display.o
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

vpath %.cpp $(SRC) $(TST)/solver/ $(TST)/interpreter/
vpath %.hpp $(SRC)
vpath %.c 	$(SRC)
		
program.so: shared.o 
	$(CXX) -shared $< -o $@ $(CXXFLAGS) 

shared.o: $(INTERPRETER) #$(SOLVER) $(UTILS)
	ld -r $^ -o $@

solvertest.out: $(SOLVER_TEST) $(SOLVER) $(LDFLAGS)
	$(CXX) $^ -o $@ -lgtest -pthread $(CXXFLAGS)
	
#//TODO:
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
	clang -S -emit-llvm -O0 $< -Wimplicit-int

api-pattern.cpp: test.ll
	llc -march=cpp $< -o api-pattern.cpp

.PHONY: run
run:	program.so test.ll
	opt -load=./program.so < test.ll > /dev/null -ll-voyager

gdb: program.so test.ll
	gdb opt	
# helpers ----------------------------------------------- />	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
