SHELL = /bin/sh

LLVM_PASS = voyager-pass.o

INTERPRETER = kernel.o matcher.o evaluator.o meta-evaluator.o meta-int.o context.o concrete-eval.o symbolic-eval.o 
INTERPRETER_TEST = expr-test.o test-holder.o test-evaluator.o  \
$(SOLVER) $(MEMORY) $(LLVM_TEST_HELPERS) $(TEST_RUNNER)
# test-symbolic-eval.o
# matcher-stub.o test-matcher.o 

MEMORY = local-memory.o holder.o activation.o activation-stack.o
MEMORY_TEST = test-holder.o test-local-memory.o $(SOLVER) $(INTERPRETER) $(LLVM_TEST_HELPERS) $(TEST_RUNNER)

SOLVER = solver.o path-constraint.o
SOLVER_TEST = $(TEST_RUNNER) $(MEMORY) $(INTERPRETER)

LLVM_TEST_HELPERS = ir-function-builder.o

TEST_RUNNER = test-runner.o

BENCHMARKS = hweight.ll gcd.ll

OBJ = $(INTERPRETER) $(MEMORY) $(SOLVER)
OBJ_TEST = $(INTERPRETER_TEST) $(MEMORY_TEST) $(SOLVER_TEST) $(LLVM_TEST_HELPERS)

CXX = g++
CXXFLAGS = -fdiagnostics-color=always -g -std=c++14 -fpic -rdynamic -Wno-deprecated
LDFLAGS = 
CVC4FLAGS = -lcvc4 -lgmp  
GTESTFLAGS = -lgtest -pthread
#Z3FLAGS = /usr/lib/libz3.so
LLVMF_DYNAMIC = $(filter-out -g -fno-exceptions -O2 -std=c++11, $(shell llvm-config --cxxflags))
LLVM_STATIC = $(filter-out -g -fno-exceptions -O2 -std=c++11, $(shell llvm-config --cxxflags --ldflags --libs core)) \
-ltinfo -ldl
DBGFLAGS = -D DBG -U NDEBUG

SRC = ../src
TST = ../test

vpath %.cpp $(SRC) $(TST) $(TST)/solver/ $(TST)/interpreter $(TST)/matcher
vpath %.hpp $(SRC) $(TST)/matcher
vpath %.c 	$(SRC) ../benchmarks
		
program.so: shared.o 
	$(CXX) -shared $< -o $@ $(CXXFLAGS) 

shared.o: $(INTERPRETER) $(SOLVER) $(MEMORY) $(LLVM_PASS)
	ld -r $^ -o $@ $(LLVM_DYNAMIC)

solver-test.out: $(SOLVER) $(SOLVER_TEST)
	$(CXX) $^ -o $@ $(GTESTFLAGS) $(CVC4FLAGS) $(CXXFLAGS) $(LLVM_STATIC) 

interpreter-test.out: $(INTERPRETER) $(INTERPRETER_TEST) 
	$(CXX) $^ -o $@ $(GTESTFLAGS) $(CVC4FLAGS) $(CXXFLAGS) $(LLVM_STATIC)
	
memory-test.out: $(MEMORY) $(MEMORY_TEST)
	$(CXX) $^ -o $@ $(GTESTFLAGS) $(CVC4FLAGS) $(CXXFLAGS) $(LLVM_STATIC)

$(OBJ_TEST):
$(OBJ):
%.o: %.cpp %.hpp
	$(CXX) -c $< -o $@ $(CXXFLAGS) 
	
.PHONY: clean
clean:
	@rm -vf *~ *.o *.out *.so
	@rm -vf *.ll api-pattern.cpp
	@rm -vf \#*\#

benchmarks: $(BENCHMARKS)
	touch benchmarks
	
$(BENCHMARKS):
%.ll: %.c
	clang -S -emit-llvm -O0 $<

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
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
