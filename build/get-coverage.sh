gcc -fprofile-arcs -ftest-coverage -g $@-driver.c -o $@-driver.out;
./$@-driver.out
 gcov $@-driver.c
