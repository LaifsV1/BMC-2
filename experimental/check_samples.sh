#!/bin/sh
d=exp
t=600
rm -r $d 2> /dev/null
mkdir -p $d
for k in {0..15}
do
    echo "===========================";
    echo "k=$k";
    for p in ack copy_intro e-fact e-simple hors hrec intro1 intro3 l-zipmap l-zipunzip max mc91-e mc91 mult-e-m1 mult-e-m2 mult-e mult-m1 mult repeat-e r-lock-e sum-e-m1 sum-e sum
    do
	echo "------------------------";
	echo $p;
	(echo $p ; time timeout $t ./TopLevel.native ../extras/sample_programs/MoCHi_samples/$p.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
	echo "------------------------";
    done
done
