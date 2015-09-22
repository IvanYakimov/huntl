src = ../src
test = ../test
z3-src = $(src)/solver/z3-binding
z3-test = $(test)/solver/z3-binding
cvc4-src = $(src)/solver/cvc4-binding
cvc4-test = $(test)/solver/cvc4-binding
compile = clang -std=c++14 -c

# solver infrastructure

# z3 support
z3-solver.o: $(z3-src)/z3-solver.hpp $(z3-src)/z3-solver.cpp
	$(compile) $(z3-src)/z3-solver.cpp

z3-expr.o: $(z3-src)/z3-expr.hpp $(z3-src)/z3-expr.cpp
	$(compile) $(z3-src)/z3-expr.cpp

z3-expr-factory.o: $(z3-src)/z3-expr-factory.hpp \
	$(z3-src)/z3-expr-factory.hpp
	$(compile) $(z3-src)/z3-expr-factory.cpp

z3-op-test: $(z3-test)/z3-op-test.hpp $(z3-test)/z3-op-test.cpp
	$(compile) $(z3-test)/z3-op-test.cpp

# cvc4 support
cvc4-expr.o: $(cvc4-src)/cvc4-expr.hpp $(cvc4-src)/cvc4-expr.cpp
	$(compile) $(cvc4-src)/cvc4-expr.hpp

cvc4-expr-factory.o: $(cvc4-src)/cvc4-expr-factory.hpp \
	$(cvc4-src)/cvc4-expr-factory.cpp
	$(compile) $(cvc4-src)/cvc4-expr-factory.cpp 

# phony
clean:
	rm -fv *.o
	rm -fv $(z3-src)/*~ $(z3-src)/*.gch
	rm -fv $(cvc4-src)/*~ $(cvc4-src)/*.gch
