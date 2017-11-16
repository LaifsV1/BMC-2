You can find two versions of the implementation: the base algorithm, and an implementation optimised with points-to analysis. The base algorithm is found in `base_algorithm_src`, while the optimised implementation is found in `src`.

To compile:

    ocamlbuild -I parser -use-menhir TopLevel.native

Checking a file:
e.g. Check file `mc91-e.txt` with bound `4` for `10` seconds. Returns `sat` if `fail` is reachable.

    time timeout 10 ./TopLevel.native ../extras/sample_programs/MoCHI_samples/mc91-e.txt 4 | z3 -in | grep -v "(error"

The command above prints the following

    sat
    ((n 102))

    real        0m0.028s
    user        0m0.018s
    sys         0m0.013s

where program fails with input `n = 102`.