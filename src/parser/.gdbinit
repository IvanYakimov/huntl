run -load=./func-printer.so -FuncPrinter test.ll > /dev/null
break func-printer.cpp:6
run
break pattern-matcher.cpp:62
break pattern-matcher.cpp:35
