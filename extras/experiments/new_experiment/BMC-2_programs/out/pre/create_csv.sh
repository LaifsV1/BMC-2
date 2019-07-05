#!/bin/bash

result1=final/1.csv
result2=final/2.csv


for file in 100_1-e 100_2 100_3-e 100_4-e 100_5-e 200_1-e 200_2-e 200_3-e 200_4-e 200_5-e 400_1-e 400_2-e ack a-cppr a-init-me a-init a-max-me a-max copy_intro e-fact e-simple hors hrec intro1 intro3 l-zipmap l-zipunzip max mc91-e mc91 mult-e-m2 mult-e-m3 mult-e mult repeat-e r-lock-e r-lock sum-e sum-mult-e sum
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
