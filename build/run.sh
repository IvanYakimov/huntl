#!/bin/bash
target="$1"

helper() {
    opt -load=./huntl.so -ll-voyager 1>/dev/null
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
while getopts "hsi:o:" opt; do
    case "$opt" in
	h) show_help && exit 0;;
	s) silent=1;;
	i) ifile=$OPTARG;;
	o) ofile=$OPTARG;;
    esac
done

shift $((OPTIND-1))
[ "$1" = "--" ] && shift
# now we can use $@ to get POSIX operands

if [[ -n $ofile ]]; then
    if [[ -f $ofile ]] || ! [[ -e $ofile ]]; then
	echo "Output redirected to" $ofile
	exec 2>$ofile
    else
	echo "Cannot redirect output to '" $ofile "'"
	exit 0
    fi
fi

if ! [[ -z $ifile ]]; then
    if [[ -f $ifile ]]; then
	echo "Input redirected from" $ifile
	exec 0<$ifile
    fi
fi

if ((silent == 0)); then
    helper $ifile
else
    echo "// SILENT MODE ENABLED"
    (helper $ifile) | grep ":=>"
fi
