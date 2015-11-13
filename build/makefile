# see http://scottmcpeak.com/autodepend/autodepend.html

src = ../src
solver = $(src)/solver
z3-src = $(src)/solver/z3-binding
cvc4-src = $(src)/solver/cvc4-binding
CXX = g++ -fdiagnostics-color=auto
CXXFLAGS = -std=c++14 -c
# LDFLAGS =
OBJS = $(solver)/expr.o

# link
program: $(OBJ)
	$(GXX) -o program

# compile
%.o: %.cpp
	$(CXX) $(CXXFLAGS) $

# phony
clean:
	rm -fv *.o

