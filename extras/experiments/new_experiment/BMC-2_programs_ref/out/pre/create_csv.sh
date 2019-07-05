#!/bin/bash

result1=final/1.csv
result2=final/2.csv


for file in ref-1 ref-1-e ref-2 ref-2-e ref-3
do
  echo -n $file, >> $result1
  echo -n $file, >> $result2

  for bound in {1..15}
  do
    file1=${file}_1_$bound.txt
    file2=${file}_2_$bound.txt

    cat $file1 | tr '\n' , >> $result1
    cat $file2 | tr '\n' , >> $result2

  done
  echo >> $result1
  echo >> $result2

done
