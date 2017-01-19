#!/bin/bash
target="$1"

helper() {
    opt -load=./huntl.so < $1 -ll-voyager 1>/dev/null
}

show_help() {
    echo "Format is: ./run.sh -f target.ll "
}

# reset getopts
OPTIND=1

# declare vars for args
ifile=""
ofile=""
silent=0

# Note: "--" means end of options!
while getopts "hsf:o:" opt; do
    case "$opt" in
	h) show_help && exit 0;;
	s) silent=1;;
	f) ifile=$OPTARG;;
	o) ofile=$OPTARG;;
    esac
done

shift $((OPTIND-1))
[ "$1" = "--" ] && shift
# now we can use $@ to get POSIX operands

if [[ -n $ofile ]]; then
    echo "Output redirected to" $ofile
    exec 2>$ofile
fi

if [[ -z $ifile ]]; then
    echo "Target name is empty"
    show_help
else
    if ((silent == 0)); then
	helper $ifile
    else
	echo "// SILENT MODE ENABLED"
	(helper $ifile) | grep ":=>"
    fi
fi
