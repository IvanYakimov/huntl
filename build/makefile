src = ../src
z3-src = $(src)/solver/z3-binding
compile = clang -std=c++14

target: solver expr expr-factory
solver: z3-solver.o
expr-factory: z3-expr-factory.o
expr: z3-expr.o

# z3 support
z3-expr.o: $(z3-src)/z3-expr.hpp $(z3-src)/z3-expr.cpp
	$(compile) -c $(z3-src)/z3-expr.cpp

z3-expr-factory.o: $(z3-src)/z3-expr-factory.hpp \
	$(z3-src)/z3-expr-factory.hpp
	$(compile) -c $(z3-src)/z3-expr-factory.cpp

clean:
	rm -fv *.o
	rm -fv $(z3-src)/*~
