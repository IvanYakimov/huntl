#!/usr/bin/env bash
print=0
if (( $# == 1 )); then
    echo ""
elif (( $# == 2)); then
    if [[ $2 == "--print" ]]; then
	print=1
    else
	echo "wrong option: --print expected" && exit
    fi
else echo "Illegal number of arguments: target name expected" && exit
fi
cd "$( dirname "${BASH_SOURCE[0]}" )"
name="$1"
template=$name".xml"
hpre=$name".hpre"
spre=$name".spre"
hpost=$name".hpost"
spost=$name".spost"
header=$name".hpp"
source=$name".cpp"

tmpdecl=$(mktemp)
tmpdef=$(mktemp)
cat $template | ./macrogen.py --decl > $tmpdecl
cat $template | ./macrogen.py --def > $tmpdef
cat $hpre $tmpdecl $hpost > $header
cat $spre $tmpdef $spost > $source
if ((print == 1)); then
    gedit $header $source &
fi
rm $tmpdecl
rm $tmpdef
