(* BMC-2 Abstract Syntax *)
(*author: Yu-Yang Lin, date: 20/07/2017*)
open Format

(* Parse Exceptions *)
type pos_range = (Lexing.position * Lexing.position)
exception SyntaxError of string * pos_range
exception ParseError of string * pos_range

(* Natural Numbers *)
type nat = Nil | Suc of nat
let rec nat_of_int (i : int) :(nat) =
  match i > 0 with
  | true -> Suc(nat_of_int (i-1))
  | false -> Nil

(*********)
(* Types *)
(*********)
type tp = Unit | Integer | Arrow of tp list * tp | Product of tp * tp

let rec string_of_tp (t : tp) :(string) =
  match t with
  | Unit -> "Unit"
  | Integer -> "Int"
  | Arrow(ts,t2) -> sprintf "(%s -> %s)" (string_of_tps ts) (string_of_tp t2)
  | Product(t1,t2) -> sprintf "(%s * %s)" (string_of_tp t1) (string_of_tp t2)
and string_of_tps (tps : tp list) :(string) =
  match tps with
  | []      -> ""
  | tp::tps -> sprintf "%s,%s" (string_of_tp tp) (string_of_tps tps)

let left_tp tp =
  match tp with
  | Product(t1,t2) -> t1
  | _ -> failwith (sprintf "type %s is not a pair" (string_of_tp tp))

let right_tp tp =
  match tp with
  | Product(t1,t2) -> t2
  | _ -> failwith (sprintf "type %s is not a pair" (string_of_tp tp))

type z3_tp = Unit | Int | Meth | Pair of z3_tp * z3_tp

let rec z3_of_tp (tp : tp) =
  match tp with
  | Unit -> Unit
  | Integer -> Int
  | Arrow _ -> Meth
  | Product(a,b) -> Pair(z3_of_tp a,z3_of_tp b)

let rec string_of_z3_tp tp =
  match tp with
  | Unit -> "Unit"
  | Int  -> "Int"
  | Meth -> "String"
  | Pair(a,b) -> sprintf "(Pair %s %s)" (string_of_z3_tp a) (string_of_z3_tp b)

let get_z3_tp tp = string_of_z3_tp (z3_of_tp tp)

let z3_decl var stype = sprintf "(declare-const %s %s)" var stype

let z3_unit_type = "(declare-sort Unit)"
let z3_pairs_type = "(declare-datatypes (T1 T2) ((Pair (mk-pair (left T1) (right T2)))))"
let z3_default_type = sprintf "%s\n%s" z3_unit_type z3_pairs_type

let z3_pair_maker left right = sprintf "(mk-pair %s %s)" left right
let z3_pair_decl left right = sprintf "(Pair %s %s)" left right
let z3_pair_left  pair = sprintf "(left %s)"  pair
let z3_pair_right pair = sprintf "(right %s)" pair
let z3_binops a op b = sprintf "(%s %s %s)" op a b

(*********)
(* Terms *)
(*********)
type _name  = string       (* Names *)
type _var   = _name * tp   (* Variables *)
type _ref   = _name * tp   (* References *)
type _meth  = _name        (* Methods *)
type _ret   = _var         (* Return Variable *)
type _binop = string       (* Binary Operations *)
type _val   = string       (* Values for assignment: i|m *)
type _decl  = (_name * z3_tp) list (* Name and Type for SMT-Lib declarations *)

let tfail = "fail"
let tnil = "nil"
let tfail_i = "fail_int"
let tnil_i  = "nil_int"
let tfail_u = "fail_unit"
let tnil_u  = "nil_unit"
let tfail_m = "\"fail_meth\""
let tnil_m  = "\"nil_meth\""
let tskip = "skip"

let tfail_n n = sprintf "%s_%s" tfail (string_of_int n)
let tnil_n  n = sprintf "%s_%s" tnil (string_of_int n)

let rec z3_fail_of_tp (tp : tp) =
  match tp with
  | Unit -> tfail_u
  | Integer -> tfail_i
  | Arrow _ -> tfail_m
  | Product(t1,t2) -> z3_pair_maker (z3_fail_of_tp t1) (z3_fail_of_tp t2)

let rec z3_nil_of_tp (tp : tp) =
  match tp with
  | Unit -> tnil_u
  | Integer -> tnil_i
  | Arrow _ -> tnil_m
  | Product(t1,t2) -> z3_pair_maker (z3_nil_of_tp t1) (z3_nil_of_tp t2)

let get_default_decl = [(tfail_i,Int);(tnil_i,Int);
                        (tfail_u,Unit);(tnil_u,Unit);
                        (*(tfail_m,Meth);(tnil_m,Meth); (*they strings*)*)
                        (tskip,Unit)]

let rec decl_of_list (s : string) (xs : _decl) =
  match xs with
  | (x,tp)::xs -> decl_of_list (sprintf "%s\n%s" (z3_decl x (string_of_z3_tp tp)) s) xs
  | [] -> s

let rec string_of_args args =
  match args with
  | [] -> ""
  | ((x,tp)::xs) -> sprintf "(%s:%s) %s" (x) (string_of_tp tp) (string_of_args xs)
let rec string_of_vars vars =
  match vars with
  | [] -> failwith "string of empty vars"
  | (x,tp)::[] -> x
  | (x,tp)::xs -> sprintf "%s,%s" x (string_of_args xs)

type term = Fail | Skip | Int of int | Method of _meth
            | Var of _var | Deref of _ref | Lambda of _var list * term * tp (*syntax fun (x:arg type) :(ret type) -> M*)
            | Left of term * tp | Right of term * tp | Assign of _ref * term
            | Pair of term * term | BinOp of _binop * term * term
            | Let of _var * term * term | ApplyM of _meth * term list
            | If of term * term * term | ApplyX of _var * term list
let rec string_of_term (t : term) :(string) =
  match t with
  | Fail -> tfail
  | Skip -> tskip
  | Int i -> string_of_int i
  | Method m -> m
  | Var (x,t) -> sprintf "%s" x
  | Deref (r,t) -> sprintf "(!%s)" r
  | Lambda(xs,t,tp') ->
     sprintf "(fun %s :%s -> %s)"
             (string_of_args xs) (string_of_tp tp') (string_of_term t)
  | Left(t,tp) -> sprintf "((fst : %s) %s)" (string_of_tp tp) (string_of_term t)
  | Right(t,tp) -> sprintf "((snd : %s) %s)" (string_of_tp tp) (string_of_term t)
  | Assign((r,tp),t) -> sprintf "(%s := %s)" r (string_of_term t)
  | Pair(t1,t2) -> sprintf "Pair(%s,%s)" (string_of_term t1) (string_of_term t2)
  | BinOp(op,t1,t2) -> sprintf "(%s %s %s)" (string_of_term t1) op (string_of_term t2)
  | Let((x,tp),t1,t2) ->
     sprintf "(let (%s:%s) = %s in %s)"
             x (string_of_tp tp) (string_of_term t1) (string_of_term t2)
  | ApplyM(m,t) -> sprintf "(%s (%s))" m (List.fold_right (fun ti acc ->
                                                          match acc with
                                                          | "" -> string_of_term ti
                                                          | _ -> sprintf "%s,%s" (string_of_term ti) acc) t "")
  | If(t,t1,t0) ->
     sprintf "(if %s then %s else %s)"
             (string_of_term t) (string_of_term t1) (string_of_term t0)
  | ApplyX((x,tp),t) -> sprintf "(%s (%s))" x (List.fold_right (fun ti acc ->
                                                          match acc with
                                                          | "" -> string_of_term ti
                                                          | _ -> sprintf "%s %s" (string_of_term ti) acc) t "")

let string_of_typed_term t tp = sprintf "(%s : %s)" (string_of_term t) (string_of_tp tp)

(****************)
(* Propositions *)
(****************)
type clause = string
type proposition = True | False
                 | Eq of clause * clause
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

let rec z3_of_proposition (p : proposition) :(string) =
  match p with
  | True -> "true"
  | False -> "false"
  | Eq(a,b) -> sprintf "(= %s %s)" a b
  | Neq(a,b) -> sprintf "(not (= %s %s))" a b
  | Implies(a,b) -> sprintf "(=> %s %s)" (z3_of_proposition a) (z3_of_proposition b)
  | And(a,b) -> sprintf "(and %s %s)" (z3_of_proposition a) (z3_of_proposition b)
  | Or(a,b) -> sprintf "(or %s %s)" (z3_of_proposition a) (z3_of_proposition b)

let rec z3_assertions_of_list xs =
  match xs with
  | [] -> ""
  | x::xs -> sprintf "(assert %s)\n%s" (z3_of_proposition x) (z3_assertions_of_list xs)

let (===) s1 s2 = if s1 = s2 then True  else Eq(s1,s2)
let (=/=) s1 s2 = if s1 = s2 then False else Neq(s1,s2)
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

type repo  = (_var list * term * tp) Repo.t
let empty_repo :(repo) = Repo.empty
let get_methods map tp =
  Repo.fold (fun mi (xi,ti,tpi) acc -> if tpi = tp then (mi,xi,ti)::acc else acc) map []

let repo_get_decl map acc :(_decl) = Repo.fold (fun mi (xi,ti,tpi) acc -> (mi,z3_of_tp tpi)::acc) map acc

let z3_method s = sprintf "\"%s\"" s
type prepo  = bool Repo.t
let prepo_exists map m =
  try Repo.find m map
  with Not_found -> false
let prepo_update (map:prepo) key = Repo.add key true map
let empty_prepo :(prepo) = Repo.empty

(* partial map, references to int *)
(* counter maps r to its assignments seen so far; i.e. if none, then zero *)
module Counter = Map.Make(struct type t = _ref let compare = compare end)
let string_of_ref key int = sprintf "_%s_%s_" (fst key) (string_of_int int)
let cd_get    map key = try Counter.find key map with Not_found -> -1
let c_update  map key = let new_val = (cd_get map key)+1 in
                        Counter.add key new_val map,string_of_ref key new_val
let d_update  map key new_val = Counter.add key new_val map,string_of_ref key new_val
let ref_get   map key = sprintf "_%s_%s_" (fst key) (string_of_int (cd_get map key))
type counter = int Counter.t
let empty_counter :(counter) = Counter.empty

let c_get_decl map acc :(_decl) = Counter.fold (fun r i acc -> ((string_of_ref r i),z3_of_tp (snd r))::acc) map acc

let c_update_all map acc = let newmap = Counter.map (fun i -> i+1) map in newmap,c_get_decl newmap acc

let c_wedge c d =
  Counter.fold (fun r i acc -> ((string_of_ref r i)===ref_get d r) &&& acc) c True

(**********************)
(* counter for types  *)
(**********************)
module Types = Map.Make(struct type t = tp let compare = compare end)
let types_get map key = try Types.find key map with Not_found -> -1
let types_add map key new_val = Types.add key new_val map
type types = int Types.t
let empty_types :(types) = Types.empty

let get_types_decl map acc :(_decl) = Types.fold (fun tp i acc -> let tp' = z3_of_tp tp in (tfail_n i,tp')::(tnil_n i,tp')::acc ) map acc

(********************************)
(* parser types map for parsing *)
(********************************)
(* ONLY FOR REFERENCES AND VARIABLES *)
module PTypes = Map.Make(struct type t = _name let compare = compare end)
type ptypes = tp PTypes.t
let empty_ptypes :(ptypes) = PTypes.empty
let ptypes_get map key = try PTypes.find key map with Not_found -> failwith (sprintf "variable %s not found" key)
let ptypes_add map key new_val = PTypes.add key new_val map
let get_ptypes_decl map acc :(_decl) = PTypes.fold (fun key tp acc -> (key,z3_of_tp tp)::acc ) map acc

let rec tps_from_vars (vars: _var list) :(tp list)=
  match vars with
  | (x,tp)::[] -> [tp]
  | (x,tp)::vars -> tp::(tps_from_vars vars)
  | [] -> failwith "arguments missing, can't build vars type"

(*********************)
(* File to Translate *)
(*********************)
type assignlist = (_ref * _val) list
type methlist = (_meth * (_var list * term * tp)) list
type file = assignlist * methlist * term

let rec build_cdphi counter phi (alist : assignlist) acc :(counter * proposition * _decl) =
  match alist with
  | [] -> counter , phi , acc
  | (r,v)::xs -> build_cdphi
                   (fst (d_update counter r 0))
                   (((string_of_ref r 0)===v)&&&phi)
                   xs (((string_of_ref r 0),z3_of_tp (snd r))::acc)

let rec build_repo repo methods :(repo) =
  match methods with
  | [] -> repo
  | (m,xttp)::xs -> build_repo (repo_update repo m xttp) xs
