#!/bin/bash
for file in *.out
do
  result=pre/${file%.*}.txt
  { awk '/./{line=$0} END{print line}' $file ; } > $result
done
