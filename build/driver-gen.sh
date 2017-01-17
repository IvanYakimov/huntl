target="*trace"
for f in $target;
do
    dest=$(basename $f .ll.trace)-driver.c
    rm -vf $dest
    echo '#include "../benchmarks/string.c"' >> $dest
    cat $f | ../driver-gen/./main.py >> $dest;
    cc $dest -o $(basename $dest .c).out
done;
