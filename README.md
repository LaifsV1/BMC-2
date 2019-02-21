# BMC-2

`BMC-2` is a bounded model checking tool that translates the behaviour
of higher-order programs into SMT-LIB 2 constraints. We recommend an SMT solver such as Z3 to check the output for satisfiability.

Programs are written in a functional language similar to OCaml. Sample programs can be found under `/extras/sample_programs`.

## Compiling

You will need `ocamlbuild`, `menhir`, and an OCaml 4.04 compiler or above. Run the following command from within `/src`.

    ocamlbuild -I parser -use-menhir TopLevel.native

## Checking a file

To check a file `<somefile>`, use `TopLevel.native <somefile> <k>` where `<k>` is the desired depth for the analysis. The formula produced is satisfiable iff an assertion violation is reachable within `k`.

### Example
We check file `mc91-e.txt` with bound `4`.

    time ./TopLevel.native ../extras/sample_programs/MoCHi_samples/mc91-e.txt 4 | z3 -in | grep -v "(error"

The command above prints the following

    sat
    ((n 102))

    real        0m0.028s
    user        0m0.018s
    sys         0m0.013s

which means `mc91-e.txt` reaches a violation with input `n = 102`.
