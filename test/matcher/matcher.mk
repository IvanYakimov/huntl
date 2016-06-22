SHELL = /bin/sh

OBJ = test-matcher.o matcher-stub.o matcher.o \
	ir-function-builder.o object-stub.o \
	test-display.o display.o \
	executor.o test-executor.o \
	expr.o value.o type.o kind.o width.o object-builder.o

CXX = g++ 
CXXFLAGS = -fdiagnostics-color=always -g -std=c++14 -Wno-deprecated
LLVMFLAGS = $(filter-out -g -fno-exceptions -O2 -std=c++11, $(shell llvm-config --cxxflags --ldflags --libs core))

SRC = ../../src
TST = .

vpath %.cpp $(SRC)/interpreter $(TST)
vpath %.cpp $(SRC)/solver
vpath %.cpp ../helpers
vpath %.hpp $(SRC)/interpreter $(TST)
vpath %.hpp $(SRC)/solver
vpath %.hpp ../helpers
		
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

	
	
	
	
	
	
	
	
	
	