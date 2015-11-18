# useful links:
# https://www.gnu.org/software/make/manual/html_node/Pattern-Rules.html
# https://www.gnu.org/prep/standards/html_node/Makefile-Conventions.html
SHELL = /bin/sh

SOLVERTEST = expr-test.o 
SOLVER = expr.o
CXX = g++ 
CXXFLAGS = -fdiagnostics-color=always -O0 -ggdb -fexceptions -std=c++1y -fpic
LDFLAGS = -lgtest -pthread 

vpath %.cpp ../test/solver/
vpath %.hpp ../test/solver/

solvertest.out: $(SOLVERTEST) $(SOLVER)
	$(CXX) $^ -o $@ $(LDFLAGS) $(CSSFLAGS)

$(SOLVERTEST):
%.o: %.cpp %.hpp
	$(CXX) -c $< -o $@ $(CXXFLAGS)

print: *.hpp *.cpp
	lpr $?
	touch $@

