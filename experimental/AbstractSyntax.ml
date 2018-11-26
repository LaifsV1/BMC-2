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
let rec int_of_nat (i : nat) :(int) =
  match i with
  | Nil -> -1
  | Suc(k) -> int_of_nat k + 1

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
  | (x,tp)::xs -> sprintf "%s,%s" x (string_of_vars xs)

let rec tps_from_vars (vars: _var list) :(tp list)=
  match vars with
  | (x,tp)::[] -> [tp]
  | (x,tp)::vars -> tp::(tps_from_vars vars)
  | [] -> failwith "arguments missing, can't build vars type"

type term = Fail | Skip | Int of int | Method of _meth
            | Var of _var | Deref of _ref | Lambda of _var list * term * tp (*syntax fun (x:arg type) :(ret type) -> M*)
            | Left of term * tp | Right of term * tp | Assign of _ref * term
            | Pair of term * term | BinOp of _binop * term * term
            | Let of _var * term * term | ApplyM of _meth * term list
            | If of term * term * term | ApplyX of _var * term list
            | Letrec of _var * _var list * term * term
            | Assert of term
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
  | Assert(t) -> sprintf "(assert(%s))" (string_of_term t)
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
  | Letrec((x,tp),xs,t1,t2) ->
     sprintf "(letrec (%s:%s) = fun %s :%s -> %s in %s)"
             x (string_of_tp tp) (string_of_args xs) (string_of_tp tp) (string_of_term t1) (string_of_term t2)

let string_of_typed_term t tp = sprintf "(%s : %s)" (string_of_term t) (string_of_tp tp)

let rec z3_getval_of_decl (xs:_decl) =
  match xs with
  | [] -> printf ""
  | (x,tp)::xs -> printf "(get-value (%s))" x; z3_getval_of_decl xs

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
  | And(a,b) -> sprintf "%s && %s" (string_of_proposition a) (string_of_proposition b)
  | Or(a,b) -> sprintf "(%s || %s)" (string_of_proposition a) (string_of_proposition b)

let id x = x

let rec z3_of_proposition (p : proposition) (acc : string->string) :(string) =
  match p with
  | True -> acc "true"
  | False -> acc "false"
  | Eq(a,b) -> acc (sprintf "(= %s %s)" a b)
  | Neq(a,b) -> acc (sprintf "(not (= %s %s))" a b)
  | Implies(a,b) -> let a = (z3_of_proposition a (sprintf "(=> %s")) in
                    let b = (z3_of_proposition b (sprintf "%s %s)" a)) in
                    acc b
  | And(a,b) -> let a = (z3_of_proposition a (sprintf "\n(and %s")) in
                let b = (z3_of_proposition b (sprintf "%s %s)" a)) in
                acc b
  | Or(a,b) -> let a = (z3_of_proposition a (sprintf "(or %s")) in
               let b = (z3_of_proposition b (sprintf "%s %s)" a)) in
               acc b

let rec print_z3_of_proposition (p : proposition) :(unit) =
  match p with
  | True -> printf "true"
  | False -> printf "false"
  | Eq(a,b) -> printf "(= %s %s)" a b
  | Neq(a,b) -> printf "(not (= %s %s))" a b
  | Implies(a,b) -> printf "(=> ";
                    print_z3_of_proposition a;
                    printf " ";
                    print_z3_of_proposition b;
                    printf ")"
  | And(a,b) -> printf "\n(and ";
                print_z3_of_proposition a;
                printf " ";
                print_z3_of_proposition b;
                printf ")"
  | Or(a,b) -> printf "(or ";
               print_z3_of_proposition a;
               printf " ";
               print_z3_of_proposition b;
               printf ")"

let print_z3_assertion (f,x) = printf "(assert\n";f x;printf ")"
let rec z3_assertions_of_list xs =
  match xs with
  | [] -> ""
  | x::xs -> sprintf "(assert %s)\n%s" (z3_of_proposition x id) (z3_assertions_of_list xs)

let (===) s1 s2 = if s1 = s2 then True  else Eq(s1,s2)
let (=/=) s1 s2 = if s1 = s2 then False else Neq(s1,s2)
let (==>) p1 p2 = if p1 = True then p2 else
                    if p1 = False then True else Implies(p1,p2)
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

let rec z3_create_fresh_inputs fresh (xs:_decl) fresh_acc phi decl_acc :(_name list * proposition * _decl) =
  match xs with
  | [] -> fresh_acc,phi,decl_acc
  | (x,tp)::xs ->
     let fresh_x = fresh () in
     z3_create_fresh_inputs fresh xs (fresh_x::fresh_acc) ((x===fresh_x) &&& phi) ((fresh_x,tp)::decl_acc)

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
let rec get_method_body_of_list map ms acc =
  match ms with
  | [] -> acc
  | (m::ms) -> let x,t,tp = repo_get map m in get_method_body_of_list map ms ((m,x,t)::acc)

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

(*generates fail and nil declarations for each complex type*)
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
let get_ptypes_decl map acc :(_decl * _var list) = PTypes.fold (fun key tp (decl_acc,var_acc) -> ((key,z3_of_tp tp)::decl_acc,(key,tp)::var_acc)) map acc

let rec get_neq_fail_nil args acc =
  match args with
  | (x,tp)::xs -> get_neq_fail_nil xs (((x=/=(z3_fail_of_tp tp))&&&(x=/=(z3_nil_of_tp tp)))::acc)
  | [] -> acc

let get_main_args_assertions map acc = get_neq_fail_nil (PTypes.bindings map) acc

(*********************)
(* File to Translate *)
(*********************)
type assignlist = (_ref * _val) list
type methlist = (_meth * (_var list * term * tp)) list
type file = assignlist * methlist * term * _decl * _var list * proposition list

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

(***********************)
(* Points-to Analyisis *)
(***********************)
type _pts = Meths of (_meth list) | Pair of (_pts * _pts)

let rec string_of_list xs =
  match xs with
  | [] -> ""
  | x::xs -> sprintf "%s,%s" x (string_of_list xs)

let rec string_of_pts (pts:_pts) =
  match pts with
  | Meths xs -> sprintf "[%s]" (string_of_list xs)
  | Pair(a,b) -> sprintf "(%s,%s)" (string_of_pts a) (string_of_pts b)

let empty_pts = Meths []

let pts_left pts =
  match pts with
  | Meths _ -> failwith "tried to left project points-to set"
  | Pair(a,b) -> a

let pts_right pts =
  match pts with
  | Meths _ -> failwith "tried to right project points-to set"
  | Pair(a,b) -> b

let rec pts_union (a:_pts) (b:_pts) =
  match a,b with
  | Meths a, Meths b -> Meths (List.sort_uniq compare (List.rev_append a b))
  | Pair(a1,a2), Pair(b1,b2) -> Pair(pts_union a1 b1,pts_union a2 b2)
  | _ -> failwith "pts type mismatch"

(*we already have Counter which takes in a _ref*)
type ptsmap = _pts Counter.t
let empty_ptsmap :(ptsmap) = Counter.empty

let rec print_meths ms =
  match ms with
  | Meths [] -> ""
  | Meths (m::ms) -> sprintf "%s,%s" m (print_meths (Meths ms))
  | _ -> failwith "tried to print not Meths"

let pts_get map key = try Counter.find key map with Not_found -> empty_pts
let pts_update  map key new_pts =
  (* printf "\n;;;ADDED KEY TO PTSMAP: (%s,%s) --> %s\n" (fst key) (string_of_tp (snd key)) (string_of_pts new_pts); *)
  match snd key with
  | Arrow _ -> Counter.add key new_pts map
  | _ -> map

let pts_get_methods map key =
  match pts_get map key with
  | Meths m -> m
  | _ -> failwith "pts set is not a set"

let previous_time = ref (Sys.time())

let time' f x =
    let t = Sys.time() in
    let fx = f x in
    previous_time := (!previous_time +. (Sys.time() -. t));
    printf "\n;;;; TIME TAKEN SO FAR: %fs\n" (!previous_time);
    fx

let ptsmap_merge (pt1:ptsmap) (pt2:ptsmap) =
  let f k a b =
    match a,b with
    | None,None -> None
    | x,None | None,x -> x
    | Some a, Some b -> Some (pts_union a b)
  in Counter.merge f pt1 pt2

(* let rec tfail_prod tp :(_pts)=                        *)
(*   match tp with                                       *)
(*   | Product (a,b) -> Pair(tfail_prod a, tfail_prod b) *)
(*   | _ -> Meths([tfail_m])                             *)
(*                                                       *)
(* let rec tnil_prod tp :(_pts)=                         *)
(*   match tp with                                       *)
(*   | Product (a,b) -> Pair(tnil_prod a, tnil_prod b)   *)
(*   | _ -> Meths([tnil_m])                              *)
