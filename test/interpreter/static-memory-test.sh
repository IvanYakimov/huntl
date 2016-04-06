#!/bin/bash
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color
valid=$(cat ../../src/interpreter/memory.* | grep -i "address.*state" | wc -l)
invalid=$(cat ../../src/interpreter/memory.* | grep -i "state.*address" | wc -l)
if [[ (($valid > 0)) && (($invalid == 0)) ]]; then
    printf "Test ${GREEN} DONE\n"
    exit 0
else
    printf "Test ${RED} FAILED\n"
    exit 1
fi
