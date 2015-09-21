src = ../src
test = ../test
z3-src = $(src)/solver/z3-binding
z3-test = $(test)/solver/z3-binding
compile = clang -std=c++14 -c

# solver infrastructure

# z3 support
z3-expr.o: $(z3-src)/z3-expr.hpp $(z3-src)/z3-expr.cpp
	$(compile) $(z3-src)/z3-expr.cpp

z3-expr-factory.o: $(z3-src)/z3-expr-factory.hpp \
	$(z3-src)/z3-expr-factory.hpp
	$(compile) $(z3-src)/z3-expr-factory.cpp

z3-op-test: $(z3-test)/z3-op-test.hpp $(z3-test)/z3-op-test.cpp
	$(compile) $(z3-test)/z3-op-test.cpp

# phony
clean:
	rm -fv *.o
	rm -fv $(z3-src)/*~
