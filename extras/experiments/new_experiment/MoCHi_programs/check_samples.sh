#!/bin/sh
TIMEFORMAT="%U";
for file in *.ml
do
  result=out/${file%.*}.out
  { time timeout 180 bin/mochi.opt -limit 180 $file ; } &> $result
done
