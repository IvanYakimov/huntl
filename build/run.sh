make program.so && rm -f test-gcd.ll && make test-gcd.ll && opt -load=./program.so < test-gcd.ll > /dev/null -ll-voyager
