#!/bin/bash
target="$1"
if [[ -z $target ]]; then
	echo "target name is empty. format is './frun <target-name>'" 
else
	./run.sh $target 2>&1 >/dev/null | grep ':=>'
fi
