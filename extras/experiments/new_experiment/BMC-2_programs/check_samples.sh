#!/bin/sh
TIMEFORMAT="%E";
for file in *.txt
do
  for i in {1..15}
  do
    result=out/${file%.*}$i.out
    { time timeout 300 bin/bmc2 $file $i | z3 -in; } &> $result
  done
done
