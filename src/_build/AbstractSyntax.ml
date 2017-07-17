(*author: Yu-Yang Lin, date: 17/07/2017*)
open Format

(* Natural Numbers *)
type nat = Nil | Suc of nat
let rec nat_of_int (i : int) :(nat) =
  match i > 0 with
  | true -> Suc(nat_of_int (i-1))
  | false -> Nil

(*********)
(* Types *)
(*********)
type tp = Unit | Integer | Arrow of tp * tp | Product of tp * tp
let rec string_of_tp (t : tp) :(string) =
  match t with
  | Unit -> "Unit"
  | Integer -> "Int"
  | Arrow(t1,t2) -> sprintf "(%s -> %s)" (string_of_tp t1) (string_of_tp t2)
  | Product(t1,t2) -> sprintf "(%s * %s)" (string_of_tp t1) (string_of_tp t2)

(*********)
(* Terms *)
(*********)
type _var   = string * tp  (* Variables *)
type _meth  = string       (* Methods *)
type _ref   = string       (* References *)
type _binop = string       (* Binary Operations *)
type _ret   = string       (* Return Variable *)

let tfail = "fail"
let tnil  = "nil"
let tskip = "skip"

type term = Fail | Skip | Int of int | Method of _meth
            | Var of _var | Deref of _ref | Lambda of _var * term * tp
            | Left of term | Right of term | Assign of _ref * term
            | Pair of term * term | BinOp of _binop * term * term
            | Let of _var * term * term | ApplyM of _meth * term
            | If of term * term * term | ApplyX of _var * term
let rec string_of_term (t : term) :(string) =
  match t with
  | Fail -> tfail
  | Skip -> tskip
  | Int i -> string_of_int i
  | Method m -> m
  | Var (x,t) -> sprintf "(%s : %s)" x (string_of_tp t)
  | Deref r -> sprintf "(!%s)" r
  | Lambda((x,tp),t,tp') ->
     sprintf "(\\%s:%s.%s : %s)"
             x (string_of_tp tp) (string_of_term t) (string_of_tp tp')
  | Left t -> sprintf "(Left %s)" (string_of_term t)
  | Right t -> sprintf "(Right %s)" (string_of_term t)
  | Assign(r,t) -> sprintf "(%s := %s)" r (string_of_term t)
  | Pair(t1,t2) -> sprintf "(%s,%s)" (string_of_term t1) (string_of_term t2)
  | BinOp(op,t1,t2) -> sprintf "(%s %s %s)" (string_of_term t1) op (string_of_term t2)
  | Let((x,tp),t1,t2) ->
     sprintf "(let %s:%s = %s in %s)"
             x (string_of_tp tp) (string_of_term t1) (string_of_term t2)
  | ApplyM(m,t) -> sprintf "(%s %s)" m (string_of_term t)
  | If(t,t1,t0) ->
     sprintf "(if %s then %s else %s)"
             (string_of_term t) (string_of_term t1) (string_of_term t0)
  | ApplyX((x,tp),t) -> sprintf "((%s:%s) %s)" x (string_of_tp tp) (string_of_term t)

let string_of_typed_term t tp = sprintf "(%s : %s)" (string_of_term t) (string_of_tp tp)

(****************)
(* Propositions *)
(****************)
type clause = string
type proposition = True | False
                 |Eq of clause * clause
                 | Neq of clause * clause
                 | Implies of proposition * proposition
                 | And of proposition * proposition
                 | Or of proposition * proposition
let rec string_of_proposition (p : proposition) :(string) =
  match p with
  | True -> "true"
  | False -> "false"
  | Eq(a,b) -> sprintf "(%s == %s)" a b
  | Neq(a,b) -> sprintf "(%s != %s)" a b
  | Implies(a,b) -> sprintf "(%s => %s)" (string_of_proposition a) (string_of_proposition b)
  | And(a,b) -> sprintf "(%s && %s)" (string_of_proposition a) (string_of_proposition b)
  | Or(a,b) -> sprintf "(%s || %s)" (string_of_proposition a) (string_of_proposition b)

let (===) s1 s2 = if s1 = s2 then True else Eq(s1,s2)
let (=/=) s1 s2 = if s1 = s2 then Neq(s1,s2) else True
let (==>) p1 p2 = if p1 = True then p2 else Implies(p1,p2)
let (&&&) p1 p2 =
  match p1,p2 with
  | True,_ -> p2
  | _,True -> p1
  | False,_ -> False
  | _,False -> False
  | _,_ -> And(p1,p2)
let (|||) p1 p2 =
  match p1,p2 with
  | True,_ -> True
  | _,True -> True
  | False,_ -> p2
  | _,False -> p1
  | _,_ -> Or(p1,p2)

(********************************************)
(* Method Repository and Reference Counters *)
(********************************************)
(* partial map, method names to functions *)
module Repo = Map.Make(struct type t = _meth let compare = compare end)
let repo_get map m =
  try Repo.find m map
  with Not_found ->
    failwith (sprintf "***[error] : method '%s' not in repo." m)
let repo_update map key record = Repo.add key record map

type repo  = (_var * term * tp) Repo.t
let empty_repo :(repo) = Repo.empty
let get_methods map tp =
  Repo.fold (fun mi (xi,ti,tpi) acc -> if tpi = tp then (mi,xi,ti)::acc else acc) map []

(* partial map, references to int *)
(* counter maps r to its assignments seen so far; i.e. if none, then zero *)
module Counter = Map.Make(struct type t = _ref let compare = compare end)
let cd_get    map key = try Counter.find key map with Not_found -> 0
let c_update  map key = Counter.add key ((cd_get map key)+1) map
let d_update  map key new_val = Counter.add key new_val map
let ref_get   map key = sprintf "_%s%s_" key (string_of_int (cd_get map key))
let string_of_ref key int = sprintf "_%s%s_" key (string_of_int int)
type counter = int Counter.t
let empty_counter :(counter) = Counter.empty

let c_update_all map = Counter.map (fun i -> i+1) map

let c_wedge c d =
  Counter.fold (fun r i acc -> ((string_of_ref r i)===ref_get d r) &&& acc) c True
