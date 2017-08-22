%{
  open AbstractSyntax
  open Format
  open Lexing

  let ptypes_seen = ref empty_ptypes
  let methods_seen = ref empty_prepo
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
%token Apply_TERM_OP

(*** OTHER-TOKENS ***)
%token ARROW_OP
%token TIMES_OP PLUS_OP MINUS_OP
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
%nonassoc COMMA
%nonassoc MINUS_OP PLUS_OP
%nonassoc TIMES_OP

%left Apply_TERM_OP  (* function application *)
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
| STORE COLON store METHOD COLON repo MAIN COLON tp COLON term EOF { ($3,$6,$11),$9 } (* file , expected main type, declaration list *)
| METHOD COLON repo MAIN COLON tp COLON term EOF                   { ([],$3,$8), $6 }
| STORE COLON store MAIN COLON tp COLON term EOF                   { ($3,[],$8), $6 }
| MAIN COLON tp COLON term EOF                                     { ([],[],$5), $3 }

(*** STORE ***)
store:
| store_elem store { $1::$2 }
| store_elem       { [$1] }

store_elem:
| var Assign_TERM_OP Int_TERM SEMICOLON  { $1,string_of_int $3 }
| var Assign_TERM_OP NAME SEMICOLON      { $1,z3_method $3 }

(*** REPO ***)
repo:
| repo_elem repo { $1::$2 }
| repo_elem      { [$1] }

repo_elem:
| NAME var COLON tp EQUALS_OP term SEMICOLON { let (x,tp) = $2 in
                                               ptypes_seen:=ptypes_add (!ptypes_seen) x tp;
                                               methods_seen:=prepo_update (!methods_seen) $1;
                                               $1,((x,tp),$6,Arrow(tp,$4)) }

(*** TERMS ***)
term:
| Fail_TERM                                  { Fail }
| Skip_TERM                                  { Skip }
| Int_TERM                                   { Int $1 }
| NAME                                       { let b = prepo_exists (!methods_seen) $1 in
                                               if b
                                               then Method ($1)
                                               else let x = $1 in
                                                    let tp = ptypes_get (!ptypes_seen) x in
                                                    Var (x,tp) }
| Deref_TERM_OP NAME                         { let x = $2 in
                                               let tp = ptypes_get (!ptypes_seen) x in
                                               Deref (x,tp) }
| Lambda_TERM var COLON tp ARROW_OP term     { let x,tp = $2 in
                                               Lambda((x,tp),$6,Arrow(tp,$4)) }
| Left_TERM_OP term                          { Left $2 }
| Right_TERM_OP term                         { Right $2 }
| NAME Assign_TERM_OP term                   { let x = $1 in
                                               let tp = ptypes_get (!ptypes_seen) x in
                                               Assign((x,tp),$3) }
| term COMMA term                            { Pair($1,$3) }
| term PLUS_OP term                          { BinOp("+",$1,$3) }
| term MINUS_OP term                         { BinOp("-",$1,$3) }
| term TIMES_OP term                         { BinOp("*",$1,$3) }
| Let_TERM var EQUALS_OP term In_TERM term   { Let($2,$4,$6) }
| NAME term                                  { let b = prepo_exists (!methods_seen) $1 in
                                               if b
                                               then ApplyM($1,$2)
                                               else let x = $1 in
                                                    let tp = ptypes_get (!ptypes_seen) x in
                                                    ApplyX((x,tp),$2) } %prec Apply_TERM_OP
| If_TERM term Then_TERM term Else_TERM term { If($2,$4,$6) }
| OPEN_PAREN term CLOSE_PAREN                { $2 }

var:
| NAME COLON tp              { ptypes_seen:=ptypes_add (!ptypes_seen) $1 $3;
                               $1,$3 }
| OPEN_PAREN var CLOSE_PAREN { $2 }

tp:
| Unit_TYPE                 { Unit }
| Integer_TYPE              { Integer }
| tp ARROW_OP tp            { Arrow($1,$3) }
| tp COMMA tp               { Product($1,$3) }
| OPEN_PAREN tp CLOSE_PAREN { $2 }
