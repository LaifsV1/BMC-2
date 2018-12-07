#!/bin/sh
d=exp
rm -r $d 2> /dev/null
mkdir -p $d
for k in {0..6}
do
echo "===========================";
echo "k=$k";
(echo ack ;       time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/ack.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo copy_intro ;time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/copy_intro.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo e-fact ;    time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/e-fact.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo e-simple ;  time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/e-simple.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo hors ;      time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/hors.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo hrec ;      time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/hrec.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo intro1 ;    time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/intro1.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo intro3 ;    time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/intro3.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo l-zipmap ;  time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/l-zipmap.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo l-zipunzip ;time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/l-zipunzip.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo max ;       time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/max.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo mc91-e ;    time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mc91-e.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo mc91 ;      time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mc91.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo mult-e-m1 ; time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mult-e-m1.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo mult-e-m2 ; time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mult-e-m2.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo mult-e ;    time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mult-e.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo mult-m1 ;   time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mult-m1.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo mult ;      time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mult.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo repeat-e ;  time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/repeat-e.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo r-lock-e ;  time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/r-lock-e.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo r-lock ;    time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/r-lock.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo sum-e-m1 ;  time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/sum-e-m1.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo sum-e ;     time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/sum-e.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
(echo sum ;       time timeout 300 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/sum.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt
done
