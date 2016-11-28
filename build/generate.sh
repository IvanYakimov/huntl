targets="strlen.ll"
for f in $targets;
do echo $f && ./frun.sh $f 2>&1 | ./estimate.out > $f.trace
done;

