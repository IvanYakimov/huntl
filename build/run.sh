#!/bin/bash
target="$1"
if [[ -z $target ]]; then
	echo "target name is empty. format is './run <target-name>'" 
else
	opt -load=./program.so < $target > /dev/null -ll-voyager
fi
