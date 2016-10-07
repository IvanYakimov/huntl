#!/bin/bash
make lab.ll
make program.so
./run.sh lab.ll 2> lab2.ll
clang lab2.ll -c -o lab2.o
make engine.o
g++ lab2.o engine.o -o self-runner.out 
