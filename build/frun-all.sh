#!/bin/bash
target="$@"
if [[ -z $target ]]; then
	echo "file list is empty. format is './frun <target-name>'" 
else
	for f in $target; do ./frun.sh $f; done;
fi



