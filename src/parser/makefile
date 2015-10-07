objects = func-printer.o 
gxx = g++ -fdiagnostics-color=always -O0 -g
compile = -c
src = `llvm-config --cxxflags`
lib = `llvm-config --libs` -pthread -ltinfo `llvm-config --ldflags` -ldl

func-printer.so: func-printer.o
	$(gxx) -shared -o func-printer.so func-printer.o

func-printer.o: func-printer.cpp
	$(gxx) -c -fpic func-printer.cpp $(src)

clean:
	rm -vf *~ *.o *.out *.so

run:
	opt -load=./func-printer.so -FuncPrinter test.ll > /dev/nullg

debug:
	gdb opt
