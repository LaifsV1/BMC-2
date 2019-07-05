#!/bin/sh
TIMEFORMAT="%U";
for file in *.txt
do
  for i in {1..15}
  do
    result=out/${file%.*}_1_$i.out
    { time timeout 180 bin/bmc2 $file $i | z3 -in; } &> $result
  done
done
for file in *.txt
do
  for i in {1..15}
  do
    result=out/${file%.*}_2_$i.out
    { time timeout 180 bin/bmc2 $file $i | z3 -in; } &> $result
  done
done
