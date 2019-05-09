#!/bin/sh
run_tests() {
    for k in $(eval echo {$1..$2})
    do
	echo "===========================";
	echo "k=$k";
	for p in ${@:3}
	do
	    echo "------------------------";
	    echo $p;
	    (echo $p ; time timeout $t ./TopLevel.native ../extras/sample_programs/MoCHi_samples/$p.txt $k | z3 -in | grep -v "(error" ; echo "") &>> $d/$k.txt;
	    echo "------------------------";
	done
    done    
}

run_all_tests() {
    run_tests 1 8 copy_intro e-fact e-simple hors intro1 intro3 l-zipmap l-zipunzip max mult-e-m1 mult-e-m2 mult-e mult-m1 mult repeat-e r-lock-e sum-e-m1 sum-e sum hrec ack mc91-e mc91;    
    run_tests 9 11 copy_intro e-fact e-simple hors intro1 intro3 l-zipmap l-zipunzip max mult-e-m1 mult-e-m2 mult-e mult-m1 mult repeat-e r-lock-e sum-e-m1 sum-e sum hrec mc91-e mc91;
    run_tests 12 13 copy_intro e-fact e-simple hors intro1 intro3 l-zipmap l-zipunzip max mult-e-m1 mult-e-m2 mult-e mult-m1 mult repeat-e r-lock-e sum-e-m1 sum-e sum mc91-e mc91;
    run_tests 14 20 copy_intro e-fact e-simple hors intro1 intro3 l-zipmap l-zipunzip max mult-e-m1 mult-e-m2 mult-e mult-m1 mult repeat-e r-lock-e sum-e-m1 sum-e sum;
}

d=exp1
t=600
rm -r $d 2> /dev/null
mkdir -p $d

run_all_tests

d=exp2
rm -r $d 2> /dev/null
mkdir -p $d

run_all_tests

d=exp3
rm -r $d 2> /dev/null
mkdir -p $d

run_all_tests

d=exp4
rm -r $d 2> /dev/null
mkdir -p $d

run_all_tests

d=exp5
rm -r $d 2> /dev/null
mkdir -p $d

run_all_tests
