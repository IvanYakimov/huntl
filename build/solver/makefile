#########################
#	SOLVER MAKEFILE		# 
######################### useful links:
# https://www.gnu.org/software/make/manual/html_node/Pattern-Rules.html
# https://www.gnu.org/prep/standards/html_node/Makefile-Conventions.html
SHELL = /bin/sh

TESTOBJ = test-expr.o test-expr-factory.o 
OBJ = expr.o expr-factory.o
CXX = g++ 
CXXFLAGS = -fdiagnostics-color=always -O0 -ggdb -fexceptions -std=c++1y -fpic -rdynamic
LDFLAGS = 

vpath %.cpp ../../src/solver ../../test/solver/
vpath %.hpp ../../src/solver ../../test/solver/

solvertest.out: $(TESTOBJ) $(OBJ)
	$(CXX) $^ -o $@ -lgtest -pthread 

$(TESTOBJ):
$(OBJ):
%.o: %.cpp %.hpp
	$(CXX) -c $< -o $@ $(CXXFLAGS)

print: *.hpp *.cpp
	lpr $?
	touch $@
	
.PHONY: clean
clean: 
	@rm -fv *.o \#*\# *.out
