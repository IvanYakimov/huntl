test-package = ../test-package
solver-test = $(test-package)/solver-test
CXX = g++
CXXFLAGS = -std=c++14 -fdiagnostics-color=auto
LDFLAGS = -lcppunit

bitvector-test: $(solver-test)/bitvector-test.cpp
	$(CXX) $(CXXFLAGS) $(solver-test)/bitvector-test.cpp \
	-o bitvector-test $(LDFLAGS)

.PHONY: clean
clean:
	@rm -rvf *-test
	@rm -rvf *~
	@rm -rvf $(solver-test)/*~
