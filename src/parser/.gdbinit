run -load=./func-printer.so -FuncPrinter test.ll > /dev/null
break func-printer.cpp:8
run
break pattern-matcher.cpp:5
break pattern-matcher.cpp:13
break pattern-matcher.cpp:67