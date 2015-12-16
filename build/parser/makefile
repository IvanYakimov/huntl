SHELL = /bin/sh
PARSER = parser.o pattern-matcher.o interpreter.o 
CXX = g++ 
CXXFLAGS = -fdiagnostics-color=always -fexceptions -std=c++1y -fpic -ggdb -O0
LLVMFLAGS = `llvm-config --cxxflags`
#lib = `llvm-config --libs` -pthread -ltinfo `llvm-config --ldflags` -ldl

vpath %.cpp ../../src/parser
vpath %.hpp ../../src/parser
vpath %.c 	../../src/parser

all: parser.so

debug: CXXFLAGS += -D DBG
debug: parser.so

parser.so: shared.o 
	$(CXX) -shared $< -o $@ $(CXXFLAGS) 

shared.o: $(PARSER)
	ld -r $^ -o $@

$(PARSER):
%.o: %.cpp %.hpp
	$(CXX) -c $< -o $@ $(CXXFLAGS) $(LLVMFLAGS)

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

.PHONY: run debug
run:	parser.so test.ll
	opt -load=./parser.so < test.ll > /dev/null -Parser

gdb: parser.so test.ll
	gdb opt	
# helpers ----------------------------------------------- />



