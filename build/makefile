SHELL = /bin/sh

INTERPRETER = kernel.o matcher.o voyager-pass.o evaluator.o 
INTERPRETER_TEST = expr-test.o test-holder.o

MEMORY = display.o holder.o
MEMORY_TEST = test-holder.o test-display.o $(SOLVER)

SOLVER = solver.o
SOLVER_TEST = test-solver.o

OBJ = $(INTERPRETER) $(MEMORY) $(SOLVER)
OBJ_TEST = $(INTERPRETER_TEST) $(MEMORY_TEST) $(SOLVER_TEST)

CXX = g++
CXXFLAGS = -fdiagnostics-color=always -g -std=c++14 -fpic -rdynamic \
	$(filter-out -g -fno-exceptions -O2 -std=c++11, $(LLVMFLAGS)) $(DBGFLAGS) \
	-Wno-deprecated
LDFLAGS = $(CVC4FLAGS) $(Z3FLAGS)
CVC4FLAGS = -lcvc4 -lgmp  
GTESTFLAGS = -lgtest -pthread
#Z3FLAGS = /usr/lib/libz3.so
LLVMFLAGS = $(shell llvm-config --cxxflags)
DBGFLAGS = -D DBG -U NDEBUG

SRC = ../src
TST = ../test

vpath %.cpp $(SRC) $(TST)/solver/ $(TST)/interpreter/ $(TST)
vpath %.hpp $(SRC)
vpath %.c 	$(SRC)
		
program.so: shared.o 
	$(CXX) -shared $< -o $@ $(CXXFLAGS) 

shared.o: $(INTERPRETER) #$(SOLVER) $(UTILS)
	ld -r $^ -o $@

solver-test.out: $(SOLVER_TEST) $(SOLVER) test-runner.o $(LDFLAGS)
	$(CXX) $^ -o $@ $(GTESTFLAGS) $(CVC4FLAGS) $(CXXFLAGS)
	
interpreter-test.out: $(INTERPRETER_TEST) $(INTERPRETER) test-runner.o $(LDFLAGS)
	$(CXX) $^ -o $@ $(GTESTFLAGS) $(CXXFLAGS)
	
memory-test.out: $(MEMORY) $(MEMORY_TEST) test-runner.o $(LDFLAGS)
	$(CXX) $^ -o $@ $(GTESTFLAGS) $(CVC4FLAGS) $(CXXFLAGS)

$(OBJ_TEST):
$(OBJ):
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
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
