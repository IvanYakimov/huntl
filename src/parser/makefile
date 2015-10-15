objects = func-printer.o 
gxx = g++ -fdiagnostics-color=always -O0 -g
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

clean:
	rm -vf *~ *.o *.out *.so

run:
	opt -load=./func-printer.so -FuncPrinter test.ll > /dev/null

debug:
	gdb opt
