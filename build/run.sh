#!/bin/bash
target="$1"
if [[ -z $target ]]; then
	echo "target name is empty. format is './run <target-name>'" 
else
	make program.so && rm -f $target && make $target && opt -load=./program.so < $target > /dev/null -ll-voyager
fi
