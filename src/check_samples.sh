#!/bin/sh
for k in {0..10}
do
echo "===========================";
echo $k;
echo PAD ;        time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/sum.txt $k | z3 -in | grep -v "(error" ; echo ""
echo ack ;        time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/ack.txt $k | z3 -in | grep -v "(error" ; echo "";
echo copy_intro ; time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/copy_intro.txt $k | z3 -in | grep -v "(error" ; echo "";
echo e-fact ;     time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/e-fact.txt $k | z3 -in | grep -v "(error" ; echo "";
echo e-simple ;   time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/e-simple.txt $k | z3 -in | grep -v "(error" ; echo "";
echo hors ;       time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/hors.txt $k | z3 -in | grep -v "(error" ; echo "";
echo hrec ;       time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/hrec.txt $k | z3 -in | grep -v "(error" ; echo "";
echo intro1 ;     time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/intro1.txt $k | z3 -in | grep -v "(error" ; echo "";
echo intro3 ;     time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/intro3.txt $k | z3 -in | grep -v "(error" ; echo "";
echo l-zipmap ;   time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/l-zipmap.txt $k | z3 -in | grep -v "(error" ; echo "";
echo l-zipunzip ; time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/l-zipunzip.txt $k | z3 -in | grep -v "(error" ; echo "";
echo max ;        time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/max.txt $k | z3 -in | grep -v "(error" ; echo "";
echo mc91-e ;     time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mc91-e.txt $k | z3 -in | grep -v "(error" ; echo "";
echo mc91 ;       time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mc91.txt $k | z3 -in | grep -v "(error" ; echo "";
echo mult-e-m1 ;  time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mult-e-m1.txt $k | z3 -in | grep -v "(error" ; echo "";
echo mult-e-m2 ;  time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mult-e-m2.txt $k | z3 -in | grep -v "(error" ; echo "";
echo mult-e ;     time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mult-e.txt $k | z3 -in | grep -v "(error" ; echo "";
echo mult-m1 ;    time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mult-m1.txt $k | z3 -in | grep -v "(error" ; echo "";
echo mult ;       time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mult.txt $k | z3 -in | grep -v "(error" ; echo "";
echo repeat-e ;   time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/repeat-e.txt $k | z3 -in | grep -v "(error" ; echo "";
echo r-lock-e ;   time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/r-lock-e.txt $k | z3 -in | grep -v "(error" ; echo "";
echo r-lock ;     time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/r-lock.txt $k | z3 -in | grep -v "(error" ; echo "";
echo sum-e-m1 ;   time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/sum-e-m1.txt $k | z3 -in | grep -v "(error" ; echo "";
echo sum-e ;      time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/sum-e.txt $k | z3 -in | grep -v "(error" ; echo "";
echo sum ;        time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHi_samples/sum.txt $k | z3 -in | grep -v "(error" ; echo ""
done
