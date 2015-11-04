objects = func-printer.o 
gxx = g++ -fdiagnostics-color=always -O0 -g -fexceptions -std=c++14
src = `llvm-config --cxxflags`
lib = `llvm-config --libs` -pthread -ltinfo `llvm-config --ldflags` -ldl

func-printer.so: linked.o 
	$(gxx) -shared -o func-printer.so linked.o

linked.o: func-printer.o inst-printer.o
	ld -r func-printer.o inst-printer.o \
		-o linked.o

func-printer.o: func-printer.cpp func-printer.hpp
	$(gxx) -c -fpic func-printer.cpp $(src)

inst-printer.o: inst-printer.cpp inst-printer.hpp
	$(gxx) -c inst-printer.cpp $(src)

pattern-matcher.out: pattern-matcher.cpp
	$(gxx) pattern-matcher.cpp -o pattern-matcher.out $(src);
	chmod u+x pattern-matcher.out

test.ll: test.c
	clang -S -emit-llvm test.c

api-pattern.cpp: test.ll
	llc -march=cpp test.ll -o api-pattern.cpp

run:	func-printer.so test.ll
	opt -load=./func-printer.so -FuncPrinter test.ll > /dev/null

debug:
	gdb opt

clean:
	@rm -vf *~ *.o *.out *.so
	@rm -vf *.ll api-pattern.cpp
