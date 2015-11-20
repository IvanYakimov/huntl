# useful links:
# https://www.gnu.org/software/make/manual/html_node/Pattern-Rules.html
# https://www.gnu.org/prep/standards/html_node/Makefile-Conventions.html
SHELL = /bin/sh

PARSER = func-printer.o pattern-matcher.o inst-printer.o interpreter.o
CXX = g++ 
CXXFLAGS = -fdiagnostics-color=always -O0 -ggdb -fexceptions -std=c++1y -fpic 
LLVMFLAGS = `llvm-config --cxxflags`
#lib = `llvm-config --libs` -pthread -ltinfo `llvm-config --ldflags` -ldl

vpath %.cpp ../../src/parser
vpath %.hpp ../../src/parser
vpath %.c 	../../src/parser

func-printer.so: parser.o 
	$(CXX) -shared $< -o $@ $(CXXFLAGS) 

parser.o: $(PARSER)
	ld -r $^ -o $@

$(PARSER):
%.o: %.cpp %.hpp
	$(CXX) -c $< -o $@ $(CXXFLAGS) $(LLVMFLAGS)

# < helpers
test.ll: test.c
	clang -S -emit-llvm $< -Wimplicit-int

api-pattern.cpp: test.ll
	llc -march=cpp $< -o api-pattern.cpp

.PHONY: run debug
run:	func-printer.so test.ll
	@opt -load=./func-printer.so -FuncPrinter test.ll > /dev/null

debug: func-printer.so test.ll
	gdb opt	
# helpers />

print: *.hpp *.cpp
	lpr $?
	touch $@

.PHONY: clean
clean:
	@rm -vf *~ *.o *.out *.so
	@rm -vf *.ll api-pattern.cpp
	@rm -vf \#*\#





