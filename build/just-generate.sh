targets="strlen.ll strcmp.ll strcpy.ll strcat.ll strstr.ll"
for f in $targets;
do echo $f && ./frun.sh $f 2>&1> $f.trace
done;

