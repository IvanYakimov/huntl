run -load=./func-printer.so -FuncPrinter test.ll > /dev/null
break func-printer.cpp : 43
run
la


