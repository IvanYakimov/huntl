objects = func-printer.o 
gxx = g++ -fdiagnostics-color=always -O0 -ggdb -fexceptions -std=c++14 -fpic
src = `llvm-config --cxxflags`
lib = `llvm-config --libs` -pthread -ltinfo `llvm-config --ldflags` -ldl

func-printer.so: linked.o 
	$(gxx) -shared -o func-printer.so linked.o

linked.o: func-printer.o pattern-matcher.o inst-printer.o
	ld -r func-printer.o pattern-matcher.o inst-printer.o \
		-o linked.o

func-printer.o: func-printer.cpp func-printer.hpp
	$(gxx) -c func-printer.cpp $(src)

pattern-matcher.o: pattern-matcher.cpp pattern-matcher.hpp
	$(gxx) -c pattern-matcher.cpp $(src)

inst-printer.o: inst-printer.cpp inst-printer.hpp
	$(gxx) -c inst-printer.cpp $(src)

test.ll: test.c
	clang -S -emit-llvm test.c

api-pattern.cpp: test.ll
	llc -march=cpp test.ll -o api-pattern.cpp

run:	func-printer.so test.ll
	opt -load=./func-printer.so -FuncPrinter test.ll > /dev/null

debug: func-printer.so test.ll
	gdb opt
	
lldebug: func-printer.so test.ll
	lldb opt

clean:
	@rm -vf *~ *.o *.out *.so
	@rm -vf *.ll api-pattern.cpp
	@rm -vf \#*\#