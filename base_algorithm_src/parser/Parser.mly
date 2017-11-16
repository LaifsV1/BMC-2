%{
  open AbstractSyntax
  open Format
  open Lexing

  let ptypes_seen = ref empty_ptypes
  let methods_seen = ref empty_prepo
  let ptypes_main_args = ref empty_ptypes
  let main_args_neq_nil_fail = ref []

  let parse_failure (msg : string) (pos1 : position) (pos2 : position) =
    ParseError ((sprintf "    error parsing %s" msg),(pos1,pos2))
%}

/*=================*/
/*---- LEXEMES ----*/
/*=================*/

(*** TYPE-TOKENS ***)
%token Unit_TYPE
%token Integer_TYPE

(*** TERMS-TOKENS ***)
%token Fail_TERM Skip_TERM
%token <int> Int_TERM
%token Lambda_TERM
%token Deref_TERM_OP
%token Left_TERM_OP
%token Right_TERM_OP
%token Assign_TERM_OP
%token Let_TERM
%token In_TERM
%token If_TERM
%token Then_TERM
%token Else_TERM
%token PAIR_OP
%token Assert_TERM
(*%token Apply_TERM_OP*)

(*** OTHER-TOKENS ***)
%token ARROW_OP
%token TIMES_OP PLUS_OP MINUS_OP GTE_OP LTE_OP EQ_OP AND_OP OR_OP
%token OPEN_PAREN CLOSE_PAREN COMMA COLON SEMICOLON
%token EQUALS_OP
%token STORE METHOD MAIN
%token <string> NAME
%token EOF

/*======================================*/
/*---- PRECEDENCE AND ASSOCIATIVITY ----*/
/*======================================*/
	/*~~~~~~~~~~~~~~~~~~~*/
	/* lowest precedence */
	/*~~~~~~~~~~~~~~~~~~~*/
(*** TERMS ***)
(*%nonassoc COMMA*)
%left ARROW_OP
%nonassoc GTE_OP LTE_OP EQ_OP AND_OP OR_OP
%left MINUS_OP PLUS_OP
%left TIMES_OP
(*%nonassoc Apply_TERM_OP*)
	/*~~~~~~~~~~~~~~~~~~~~*/
	/* highest precedence */
	/*~~~~~~~~~~~~~~~~~~~~*/

/*=================================*/
/*---- START SYMBOLS AND TYPES ----*/
/*=================================*/

%start file
%type <AbstractSyntax.file * AbstractSyntax.tp> file
%type <AbstractSyntax.assignlist> store
%type <AbstractSyntax.methlist> repo
%type <AbstractSyntax.term> term
%type <AbstractSyntax.tp> tp
%type <AbstractSyntax._var> var

%%

/*=================*/
/*---- GRAMMAR ----*/
/*=================*/

(*** FILE ***)
file:
| STORE COLON store METHOD COLON repo MAIN main_vars COLON tp COLON term EOF { let args = !ptypes_main_args in ($3,$6,$12,get_ptypes_decl args [],get_main_args_assertions args []),$10 }
| METHOD COLON repo MAIN main_vars COLON tp COLON term EOF                   { let args = !ptypes_main_args in ([],$3,$9 ,get_ptypes_decl args [],get_main_args_assertions args []), $7 }
| STORE COLON store MAIN main_vars COLON tp COLON term EOF                   { let args = !ptypes_main_args in ($3,[],$9 ,get_ptypes_decl args [],get_main_args_assertions args []), $7 }
| MAIN main_vars COLON tp COLON term EOF                                     { let args = !ptypes_main_args in ([],[],$6 ,get_ptypes_decl args [],get_main_args_assertions args []), $4 }
| error                                                                      { raise (parse_failure "file" $startpos $endpos) }

(*** STORE ***)
store:
| store_elem store { $1::$2 }
| store_elem       { [$1] }
| error            { raise (parse_failure "store" $startpos $endpos) }

store_elem:
| var Assign_TERM_OP Int_TERM SEMICOLON  { $1,string_of_int $3 }
| var Assign_TERM_OP NAME SEMICOLON      { $1,z3_method $3 }

(*** REPO ***)
repo:
| repo_elem repo { $1::$2 }
| repo_elem      { [$1] }
| error          { raise (parse_failure "methods" $startpos $endpos) }

repo_elem:
| hack_evalorder_name vars COLON tp EQUALS_OP term SEMICOLON {$1,($2,$6,Arrow(tps_from_vars $2,$4)) }

hack_evalorder_name:
| NAME    { methods_seen:=prepo_update (!methods_seen) $1;$1 }

(*** TERMS ***)
simple_term:
| Fail_TERM { Fail }
| Skip_TERM { Skip }
| Int_TERM  { Int $1 }
| NAME                { let b = prepo_exists (!methods_seen) $1 in
                        if b
                        then Method ($1)
                        else let x = $1 in
                             let tp = ptypes_get (!ptypes_seen) x in
                             Var (x,tp) }
| Deref_TERM_OP NAME  { let x = $2 in
                        let tp = ptypes_get (!ptypes_seen) x in
                        Deref (x,tp) }
| OPEN_PAREN term CLOSE_PAREN { $2 }

term:
| simple_term                                               { $1 }
| term PLUS_OP  term  { BinOp("+",$1,$3) }
| term MINUS_OP term  { BinOp("-",$1,$3) }
| term TIMES_OP term  { BinOp("*",$1,$3) }
| term GTE_OP   term  { BinOp("gte",$1,$3) }
| term LTE_OP   term  { BinOp("lte",$1,$3) }
| term EQ_OP    term  { BinOp("eq",$1,$3) }
| term AND_OP   term  { BinOp("and_int",$1,$3) }
| term OR_OP    term  { BinOp("or_int",$1,$3) }
| Lambda_TERM vars COLON tp ARROW_OP term                   { Lambda($2,$6,Arrow(tps_from_vars $2,$4)) }
| OPEN_PAREN Left_TERM_OP COLON tp CLOSE_PAREN simple_term  { Left ($6,$4) }
| OPEN_PAREN Right_TERM_OP COLON tp CLOSE_PAREN simple_term { Right ($6,$4) }
| NAME Assign_TERM_OP simple_term                           { let x = $1 in
                                                              let tp = ptypes_get (!ptypes_seen) x in
                                                              Assign((x,tp),$3) }
| PAIR_OP OPEN_PAREN term COMMA term CLOSE_PAREN     { Pair($3,$5) }
| Let_TERM var EQUALS_OP term In_TERM term           { Let($2,$4,$6) }
| NAME terms                                         { let b = prepo_exists (!methods_seen) $1 in
                                                       if b
                                                       then ApplyM($1,$2)
                                                       else let x = $1 in
                                                            let tp = ptypes_get (!ptypes_seen) x in
                                                            ApplyX((x,tp),$2) } (*%prec Apply_TERM_OP*)
| If_TERM term Then_TERM term Else_TERM term         { If($2,$4,$6) }
| Assert_TERM simple_term                            { If($2,Skip,Fail) }
| error                                              { raise (parse_failure "term" $startpos $endpos) }

terms:
| term                     { [$1] }
| OPEN_PAREN terms_helper  { $2 }

terms_helper:
| term COMMA terms_helper { $1::$3 }
| term CLOSE_PAREN        { [$1] }

var:
| NAME COLON tp              { ptypes_seen:=ptypes_add (!ptypes_seen) $1 $3; (* always call var to add var type to map *)
                               $1,$3 }
| OPEN_PAREN var CLOSE_PAREN { $2 }

vars:
| OPEN_PAREN vars_helper  { $2 }
vars_helper:
| var CLOSE_PAREN       { [$1] }
| var COMMA vars_helper { $1::$3 }

main_var:
| NAME COLON tp  { ptypes_seen:=ptypes_add (!ptypes_seen) $1 $3; (* always call var to add var type to map *)
                   ptypes_main_args:=ptypes_add (!ptypes_main_args) $1 $3; (* always call var to add args type to map *)
                   () }
main_vars:
| OPEN_PAREN CLOSE_PAREN       { () }
| OPEN_PAREN main_vars_helper  { () }
main_vars_helper:
| main_var  CLOSE_PAREN           { () }
| main_var COMMA main_vars_helper { () }

simple_tp:
| OPEN_PAREN tp CLOSE_PAREN { $2 }
| Unit_TYPE                 { Unit }
| Integer_TYPE              { Integer }

tp:
| simple_tp                 { $1 }
| tps ARROW_OP tp           { Arrow($1,$3) }
| tp TIMES_OP tp            { Product($1,$3) }

tps:
| tp                                { [$1] }
| OPEN_PAREN tps_helper CLOSE_PAREN { $2 }

tps_helper:
| tp                  { [$1] }
| tp COMMA tps_helper { $1::$3 }
