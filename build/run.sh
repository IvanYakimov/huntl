#!/bin/bash
target="$1"
if [[ -z $target ]]; then
	echo "target name is empty. format is './run <target-name>'" 
else
	make program.so && rm -f test-$target && make test-$target && opt -load=./program.so < test-$target > /dev/null -ll-voyager
fi
