# useful links:
# https://www.gnu.org/software/make/manual/html_node/Pattern-Rules.html
# https://www.gnu.org/prep/standards/html_node/Makefile-Conventions.html
SHELL = /bin/sh

OBJ = func-printer.o pattern-matcher.o inst-printer.o
CXX = g++ 
CXXFLAGS = -fdiagnostics-color=always -O0 -ggdb -fexceptions -std=c++1y -fpic 
LLVMFLAGS = `llvm-config --cxxflags`
lib = `llvm-config --libs` -pthread -ltinfo `llvm-config --ldflags` -ldl

func-printer.so: linked.o 
	$(CXX) $(CXXFLAGS) -shared -o func-printer.so linked.o

linked.o: $(OBJ)
	ld -r $(OBJ) -o linked.o

#\
linked.o: func-printer.o pattern-matcher.o inst-printer.o	\
	ld -r func-printer.o pattern-matcher.o inst-printer.o \
		-o linked.o	
		
# see https://www.gnu.org/software/make/manual/html_node/Automatic-Variables.html#Automatic-Variables
%.o: %.cpp %.hpp
	$(CXX) $(CXXFLAGS) -c $< -o $@ $(LLVMFLAGS)

test.ll: test.c
	clang -S -emit-llvm test.c -Wimplicit-int

api-pattern.cpp: test.ll
	llc -march=cpp test.ll -o api-pattern.cpp

run:	func-printer.so test.ll
	@opt -load=./func-printer.so -FuncPrinter test.ll > /dev/null

debug: func-printer.so test.ll
	gdb opt
	
lldebug: func-printer.so test.ll
	lldb opt

clean:
	@rm -vf *~ *.o *.out *.so
	@rm -vf *.ll api-pattern.cpp
	@rm -vf \#*\#