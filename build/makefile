src = ../src
solver = $(src)/solver
z3-src = $(src)/solver/z3-binding
cvc4-src = $(src)/solver/cvc4-binding
CXX = g++ -fdiagnostics-color=auto
CXXFLAGS = -std=c++14 -c
# LDFLAGS =

expr: $(solver)/expr.hpp $(solver)/expr.cpp
	$(CXX) $(CXXFLAGS) $(solver)/expr.cpp

expr-factory: $(solver)/expr-factory.hpp $(solver)/expr-factory.cpp \
	$(solver)/expr.hpp
	$(CXX) $(CXXFLAGS) $(solver)/expr-factory.cpp

# phony
clean:
	rm -fv *.o
