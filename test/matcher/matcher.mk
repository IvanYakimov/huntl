SHELL = /bin/sh

OBJ = test-matcher.o matcher-stub.o matcher.o \
	test-executor.o executor.o display-stub.o \
	ir-function-builder.o

CXX = g++  
CXXFLAGS = -fdiagnostics-color=always -g -std=c++11 -Wno-deprecated
LLVMFLAGS = $(filter-out -g -fno-exceptions -O2 -std=c++11, $(shell llvm-config --cxxflags --ldflags --libs core))

SRC = ../../src
TST = .

vpath %.cpp $(SRC)/interpreter $(TST)
vpath %.hpp $(SRC)/interpreter $(TST)
		
test-matcher.out: $(OBJ)
	$(CXX) $^ -o $@ -pthread -ltinfo -lgtest $(LLVMFLAGS) -ldl

$(OBJ):
%.o: %.cpp %.hpp
	$(CXX) -c $< -o $@ $(CXXFLAGS)
# $(LLVMFLAGS) 
	
.PHONY: clean
clean:
	@rm -vf *~ *.o *.out
	@rm -vf *.ll 
	@rm -vf \#*\#

	
	
	
	
	
	
	
	
	
	