SHELL = /bin/sh

LLVM_PASS = voyager-pass.o

INTERPRETER = kernel.o matcher.o evaluator.o meta-evaluator.o meta-int.o context.o concrete-eval.o symbolic-eval.o \
	eval-tracer.o built-in-impl.o test-generator.o solution.o solution-printer.o jit-verifier.o solution-generator.o \
	readability-optimizer.o holder-helper.o bigram-model.o
 
INTERPRETER_TEST = $(SOLVER) $(MEMORY) $(LLVM_TEST_HELPERS) $(TEST_RUNNER) \
test-holder.o test-regex.o test-evaluator.o 
#test-symbolic-eval.o 
# 
# expr-test.o

MEMORY = local-memory.o holder.o activation.o activation-stack.o stack.o ram.o
MEMORY_TEST = test-holder.o test-local-memory.o $(SOLVER) $(INTERPRETER) $(LLVM_TEST_HELPERS) $(TEST_RUNNER)

SOLVER = solver.o path-constraint.o
SOLVER_TEST = $(TEST_RUNNER) $(MEMORY) $(INTERPRETER)

UTILS = converter.o printer.o

LLVM_TEST_HELPERS = ir-function-builder.o

TEST_RUNNER = test-runner.o

PLAYGROUND = expr-test.o

BENCHMARKS = gcd.ll hweight.ll basic.ll ptr.ll str.ll lab.ll arrays.ll
BLAH = test-gcd.ll test-hweight.ll test-basic.ll test-ptr.ll test-str.ll test-lab.ll

OBJ = $(INTERPRETER) $(MEMORY) $(SOLVER) $(UTILS)
OBJ_TEST = $(INTERPRETER_TEST) $(MEMORY_TEST) $(SOLVER_TEST) $(LLVM_TEST_HELPERS) $(PLAYGROUND)

CXX = g++
#CXX = clang++
CXXFLAGS = -fdiagnostics-color=always -g -std=c++14 -fpic -rdynamic -Wno-deprecated
LDFLAGS = 
CVC4FLAGS = -lcvc4 -lgmp  
GTESTFLAGS = -lgtest -pthread
#Z3FLAGS = /usr/lib/libz3.so
LLVMF_DYNAMIC = $(filter-out -g -fno-exceptions -O2 -std=c++11, $(shell llvm-config --cxxflags))
LLVM_STATIC = $(filter-out -g -fno-exceptions -O2 -std=c++11, $(shell llvm-config --cxxflags --ldflags --libs core engine)) \
-ltinfo -ldl
DBGFLAGS = -D DBG -U NDEBUG
CLANG = clang -S -emit-llvm -O0 -Wint-conversion

SRC = ../src
TST = ../test

vpath %.cpp $(SRC) $(TST) $(TST)/solver/ $(TST)/interpreter $(TST)/matcher
vpath %.hpp $(SRC) $(TST)/matcher
vpath %.c 	$(SRC) ../benchmarks
vpath %.h	$(SRC) ../benchmarks
		
program.so: shared.o 
	$(CXX) -shared $< -o $@ $(CXXFLAGS) $(CVC4FLAGS) 

#shared.o: $(INTERPRETER) $(SOLVER) $(MEMORY) $(LLVM_PASS) $(UTILS)
shared.o: $(OBJ) $(LLVM_PASS)
	ld -r $^ -o $@ $(LLVM_DYNAMIC)

solver-test.out: $(SOLVER) $(SOLVER_TEST)
	$(CXX) $^ -o $@ $(GTESTFLAGS) $(CVC4FLAGS) $(CXXFLAGS) $(LLVM_STATIC) 

interpreter.out: $(INTERPRETER)
	$(CXX) $^ -o $@ $(CVC4FLAGS) $(CXXFLAGS) $(LLVM_STATIC)

interpreter-test.out: $(INTERPRETER) $(INTERPRETER_TEST) 
	$(CXX) $^ -o $@ $(GTESTFLAGS) $(CVC4FLAGS) $(CXXFLAGS) $(LLVM_STATIC)
	
memory-test.out: $(MEMORY) $(MEMORY_TEST)
	$(CXX) $^ -o $@ $(GTESTFLAGS) $(CVC4FLAGS) $(CXXFLAGS) $(LLVM_STATIC)
	
playground-test.out: $(PLAYGROUND) $(TEST_RUNNER)
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
	
$(BLAH):
test-%.ll: test-%.c %.c
	$(CLANG) $^
		
	
$(BENCHMARKS):
%.ll: %.c
	$(CLANG) $<

# < helpers ------------------------------------------------
test.ll: test.c
	$(CLANG) $< 

api-pattern.cpp: test.ll
	llc -march=cpp $< -o api-pattern.cpp


.PHONY: run
run:	program.so test.ll
	opt -load=./program.so < test.ll > /dev/null -ll-voyager

gdb: program.so test.ll
	gdb opt	
# helpers ----------------------------------------------- />	

















	
