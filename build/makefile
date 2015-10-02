src = ../src
solver = $(src)/solver
z3-src = $(src)/solver/z3-binding
cvc4-src = $(src)/solver/cvc4-binding
CXX = g++ -fdiagnostics-color=auto
CXXFLAGS = -std=c++14 -c
# LDFLAGS =

expr.o: $(solver)/expr.hpp $(solver)/expr.cpp
	$(CXX) $(CXXFLAGS) $(solver)/expr.cpp

bitvector-expr.o: $(solver)/bitvector-expr.hpp $(solver)/bitvector-expr.cpp \
	$(solver)/expr.hpp $(solver)/expr-factory.hpp
	$(CXX) $(CXXFLAGS) $(solver)/bitvector-expr.cpp

expr-factory.o: $(solver)/expr-factory.hpp $(solver)/expr-factory.cpp \
	$(solver)/expr.hpp
	$(CXX) $(CXXFLAGS) $(solver)/expr-factory.cpp

# phony
clean:
	rm -fv *.o
