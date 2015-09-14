objects = ast.o lexer.o parser.o  main.o 
gxx = g++ -g -O0 -fdiagnostics-color=always -std=c++11 
compile = -c

kaleidoscope: $(objects)
	$(gxx) -o kaleidoscope $(objects) -pthread -ltinfo `llvm-config --cxxflags --libs` `llvm-config --ldflags` -ldl

main.o: main.cpp
	$(gxx) $(compile) main.cpp

lexer.o: lexer.hpp lexer.cpp
	$(gxx) $(compile) lexer.cpp

parser.o: parser.cpp parser.hpp \
	lexer.hpp
	$(gxx) $(compile) parser.cpp

ast.o: ast.cpp ast.hpp
	$(gxx) $(compile) ast.cpp

clean:
	rm -f *.o *~ kaleidoscope
