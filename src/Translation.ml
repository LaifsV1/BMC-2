(* BMC-2 Translation *)
(*author: Yu-Yang Lin, date: 20/07/2017*)

open AbstractSyntax
open Format

(*******************)
(* Fresh Variables *)
(*******************)
let counter_x   = ref 0
let counter_r   = ref 0
let counter_m   = ref 0
let counter_ret = ref 0
let fresh_x   () = counter_x  := !counter_x + 1;
                   sprintf "_x_%s_"   (string_of_int (!counter_x))
let fresh_m   () = counter_m  := !counter_m + 1;
                   sprintf "\"_m_%s_\""   (string_of_int (!counter_m))
let fresh_ret () = counter_ret := !counter_ret + 1;
                   sprintf "_ret_%s_" (string_of_int (!counter_ret))

(****************************************)
(* Types Seen for fail/nil declarations *)
(****************************************)
let types_seen = ref 0
let fresh_type () = types_seen := !types_seen + 1;!types_seen

let global_types = ref empty_types
let get_type_number tp :(int * bool) =
  let map = !global_types in
  match types_get map tp with
  | -1 -> global_types := (types_add map tp (fresh_type ())); !types_seen,true
  | n  -> n,false

let get_fail_neq_nil () =
  let rec helper n acc = if n < 1 then acc else helper (n-1) (((tfail_n n)=/=(tnil_n n))::acc) in
  helper (!types_seen) [tfail_i=/=tnil_i ; tfail_u=/=tnil_u ; tfail_m=/=tnil_m]

let get_global_types () =
  Types.fold (fun tp i acc -> ((tfail_n i)===z3_fail_of_tp tp)::((tnil_n i)===z3_nil_of_tp tp)::acc) (!global_types) []

(**********************)
(* Substitute: M{t/y} *)
(**********************)
let rec subs (m : term) (t : _var) (y : _var) =
  match m with
  | Fail | Skip | Int _ | Method _ | Deref _ -> m
  | Var x -> if x = y then Var(t) else m
  | Lambda(x,t',tp) ->
     if x = y
     then let x' = (fresh_x (),snd x) in
          Lambda(x',subs t' x' x,tp)
     else Lambda(x,subs t' t y,tp)
  | Left (t',tp) -> Left(subs t' t y,tp)
  | Right (t',tp) -> Right(subs t' t y,tp)
  | Assign(r,t') -> Assign(r,subs t' t y)
  | Pair(t1,t2) -> Pair(subs t1 t y, subs t2 t y)
  | BinOp(op,t1,t2) -> BinOp(op,subs t1 t y,subs t2 t y)
  | Let(x,t1,t2) -> if x = y
                    then let x' = (fresh_x (),snd x) in
                         Let(x',subs t1 t y,subs t2 x' x)
                    else Let(x,subs t1 t y,subs t2 t y)
  | ApplyM(m,t') -> ApplyM(m,subs t' t y)
  | If(tb,t1,t0) -> If(subs tb t y,subs t1 t y,subs t0 t y)
  | ApplyX(x,t') -> if x = y
                    then ApplyX(t,subs t' t y)
                    else ApplyX(x,subs t' t y)

(*******************)
(* BMC Translation *)
(*******************)

(* error propagation type *)
type e_prop = Fail | Nil | Both | Val
let (+++) (a : e_prop) (b : e_prop) =
  match a,b with
  | Nil,Fail -> Both
  | Fail,Nil -> Both
  | Both,_ -> Both
  | _,Both -> Both
  | Nil,_ -> Nil
  | _,Nil -> Nil
  | Fail,_ -> Fail
  | _,Fail -> Fail
  | Val,Val -> Val

(* fail/nil-guards function*)
let f (a,tpa : _ret) (b,tpb : _ret) (p : proposition) (q : e_prop) (acc : _decl) :(proposition * _decl) =
  let pred faila failb nila nilb =
    match q with
    | Both -> ((a === faila) ==> (b === failb))
              &&& ((a === nila) ==> (b === nilb))
              &&& (((a === faila) ||| (a === nila)) ||| p)
    | Fail -> ((a === faila) ==> (b === failb))
              &&& ((a === faila) ||| p)
    | Nil -> ((a === nila) ==> (b === nilb))
             &&& ((a === nila) ||| p)
    | Val -> p
  in
  let select_check (tp : tp) (acc : _decl) :(string * string * _decl) =
    match tp with
      | Unit         -> tfail_u,tnil_u,acc
      | Integer      -> tfail_i,tnil_i,acc
      | Arrow(_,_)   -> tfail_m,tfail_m,acc
      | Product(a,b) -> let n,is_new = get_type_number tp in
                        let a,b = tfail_n n,tnil_n n in
                        if is_new
                        then a,b,(tfail_n n,z3_of_tp tp)::(tnil_n n,z3_of_tp tp)::acc
                        else a,b,acc in
  let faila,nila,decl1 = select_check tpa acc in
  let failb,nilb,decl2 = select_check tpb decl1 in
  pred faila failb nila nilb , decl2

(* translation *)
let rec bmc_translation
          (m : term) (r : repo) (c : counter) (d : counter)
          (phi : proposition) (k : nat) (etype : tp) (tps : (_name * z3_tp) list)
        :(_ret * proposition * repo * counter * counter * e_prop * (_name * z3_tp) list) =
  let ret = fresh_ret () in
  let ret_tp = ret,etype in
  let new_tps = (ret,z3_of_tp etype)::tps in (* (ret1,type1)::(ret2,type2)::tps *)
  match k with
  | Nil ->
     (match etype with
      | Unit    -> (ret_tp,(ret===tnil_u) &&& phi,r,c,d,Nil,new_tps)
      | Integer -> (ret_tp,(ret===tnil_i) &&& phi,r,c,d,Nil,new_tps)
      | Arrow _ -> (ret_tp,(ret===tnil_m) &&& phi,r,c,d,Nil,new_tps)
      | Product (tp1,tp2) ->
         let n,is_new = get_type_number etype in
         let new_tps' = if is_new then (tnil_n n,z3_of_tp etype)::new_tps else new_tps in
         (ret_tp,(ret===(tnil_n n)) &&& phi,r,c,d,Nil,new_tps'))
  | Suc(k') ->
     (match m with
      (* base cases *)
      | Fail ->
         (match etype with
          | Unit    -> (ret_tp,(ret===tfail_u) &&& phi,r,c,d,Fail,new_tps)
          | Integer -> (ret_tp,(ret===tfail_i) &&& phi,r,c,d,Fail,new_tps)
          | Arrow _ -> (ret_tp,(ret===tfail_m) &&& phi,r,c,d,Fail,new_tps)
          | Product (tp1,tp2) ->
             let n,is_new = get_type_number etype in
             let new_tps' = if is_new then (tfail_n n,z3_of_tp etype)::new_tps else new_tps in
             (ret_tp,(ret===(tfail_n n)) &&& phi,r,c,d,Fail,new_tps'))
      | Skip -> (ret_tp,(ret===tskip) &&& (ret=/=tfail_u) &&& (ret=/=tnil_u) &&& phi,r,c,d,Val,new_tps)
      | Int i -> (ret_tp,(ret===(string_of_int i)) &&& (ret=/=tfail_i) &&& (ret=/=tnil_i) &&& phi,r,c,d,Val,new_tps)
      | Method m -> (ret_tp,(ret===(z3_method m)) &&& (ret=/=tfail_m) &&& (ret=/=tnil_m) &&& phi,r,c,d,Val,new_tps)
      | Var(x,t) -> (ret_tp,(ret===x) &&& phi,r,c,d,Val,new_tps) (*adding != fail/nil is not sound here*)
      | Deref aref ->
         let d_r = ref_get d aref in
         (match etype with
          | Unit    -> failwith "you shouldn't be able to store Unit in refs"
          | Integer -> (ret_tp,(ret===d_r) &&& (ret=/=tfail_i) &&& (ret=/=tnil_i) &&& phi,r,c,d,Val,new_tps)
          | Arrow _ -> (ret_tp,(ret===d_r) &&& (ret=/=tfail_m) &&& (ret=/=tnil_m) &&& phi,r,c,d,Val,new_tps)
          | Product (tp1,tp2) -> failwith "you shouldn't be able to store products in refs")
      | Lambda(x,t,tp') ->
         let new_meth = fresh_m () in
         let r' = repo_update r new_meth (x,t,tp') in
         (ret_tp,(ret===(z3_method new_meth)) &&& (ret=/=tfail_m) &&& (ret=/=tnil_m) &&& phi,
          r',c,d,Val,(new_meth,Meth)::new_tps)
      (* inductive cases *)
      | Left (t,tp) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t r c d phi k tp new_tps in
         let guard_1,tpsg1 = (f ret1 ret_tp (ret===(z3_pair_left (fst ret1))) q1 tps1) in
         (ret_tp,guard_1 &&& phi1,r1,c1,d1,q1,tpsg1)
      | Right (t,tp) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t r c d phi k tp new_tps in
         let guard_1,tpsg1 = (f ret1 ret_tp (ret===(z3_pair_right (fst ret1))) q1 tps1) in
         (ret_tp,guard_1 &&& phi1,r1,c1,d1,q1,tpsg1)
      | Assign(aref,t) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t r c d phi k (snd aref) new_tps in
         let c1',caref = c_update c aref in
         let d1',daref = d_update d aref (cd_get c1' aref) in
         let d1_r' = ref_get d1' aref in
         let guard_1,tpsg1 = (f ret1 ret_tp ((ret===tskip) &&& (d1_r'===(fst ret1))) q1 tps1) in
         (ret_tp,guard_1 &&& phi1,r1,c1',d1',q1,
          (daref,z3_of_tp (snd aref))::(caref,z3_of_tp (snd aref))::tpsg1)
      | Pair(t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t1 r c d phi k (left_tp etype) new_tps in
         let (ret2,phi2,r2,c2,d2,q2,tps2) = bmc_translation t2 r1 c1 d1 phi1 k (right_tp etype) tps1 in
         let guard_1,tpsg1 = (f ret2 ret_tp (ret===(z3_pair_maker (fst ret1) (fst ret2))) q2 tps2) in
         let guard_2,tpsg2 = (f ret1 ret_tp guard_1 q1 tpsg1) in
         (ret_tp,guard_2 &&& phi2,r2,c2,d2,q1+++q2,tpsg2)
      | BinOp(op,t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t1 r c d phi k (etype) new_tps in
         let (ret2,phi2,r2,c2,d2,q2,tps2) = bmc_translation t2 r1 c1 d1 phi1 k (etype) tps1 in
         let guard_1,tpsg1 = (f ret2 ret_tp ((ret===(z3_binops (fst ret1) op (fst ret2))) &&& (ret=/=tfail_i) &&& (ret=/=tnil_i)) q2 tps2) in
         let guard_2,tpsg2 = (f ret1 ret_tp guard_1 q1 tpsg1) in
         (ret_tp,guard_2 &&& phi2,r2,c2,d2,q1+++q2,tpsg2)
      | Let((x,tp),t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t1 r c d phi k tp new_tps in
         let (ret2,phi2,r2,c2,d2,q2,tps2) = bmc_translation (subs t2 ret1 (x,tp))
                                                            r1 c1 d1 phi1 k etype tps1 in
         let guard_1,tpsg1 = (f ret2 ret_tp (ret===(fst ret2)) q2 tps2) in
         let guard_2,tpsg2 = (f ret1 ret_tp guard_1 q1 tpsg1) in
         (ret_tp,guard_2 &&& phi2,r2,c2,d2,q1+++q2,tpsg2)
      | ApplyM(m,t) ->
         let (x,n,tp) = repo_get r m in
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t r c d phi k (snd x) new_tps in
         let (ret2,phi2,r2,c2,d2,q2,tps2) = bmc_translation (subs n ret1 x)
                                                            r1 c1 d1 phi1 k' etype tps1 in
         let guard_1,tpsg1 = (f ret2 ret_tp (ret===(fst ret2)) q2 tps2) in
         let guard_2,tpsg2 = (f ret1 ret_tp guard_1 q1 tpsg1) in
         (ret_tp,guard_2 &&& phi2,r2,c2,d2,q1+++q2,tpsg2)
      | If(tb,t1,t0) ->
         let (retb,phib,rb,cb,db,qb,tpsb) = bmc_translation tb r c d phi k Integer new_tps in
         let (ret0,phi0,r0,c0,d0,q0,tps0) = bmc_translation t0 rb cb db phib k etype tpsb in
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t1 r0 c0 d0 phi0 k etype tps0 in
         let c',varsc' = c_update_all c1 tps1 in
         let guard_0,tpsg0 = (f ret0 ret_tp ((ret===(fst ret0)) &&& (c_wedge c' d0)) q0 varsc') in
         let guard_1,tpsg1 = (f ret1 ret_tp ((ret===(fst ret1)) &&& (c_wedge c' d1)) q1 tpsg0) in
         let pi0 = ((fst retb) === "0") ==> guard_0 in
         let pi1 = ((fst retb) =/= "0") ==> guard_1 in
         let guard_b,tpsgb = (f retb ret_tp (pi0 &&& pi1) qb tpsg1) in
         (ret_tp,guard_b &&& phi1,r1,c',c',qb+++q0+++q1,tpsgb)
      | ApplyX((x,tp),t) ->
         (match tp with
          | Arrow(one,two) ->
             (let (ret0,phi0,r0,c0,d0,q0,tps0) = bmc_translation t r c d phi k one new_tps in
              let r_tp = get_methods r tp in
              let phin,rn,cn,xs,tpsn =
                List.fold_left
                  (fun (phii_,ri_,ci_,ys,tpsi_) (mi,xi,ti) ->  (*mi = \(xi).ti*)
                    match ys with
                    | [] -> failwith "variable type does not match any existing method (1)"
                    | ((mi_,reti_,di_,qi_)::ys') ->
                       let (reti,phii,ri,ci,di,qi,tpsi) = bmc_translation (subs ti ret0 xi)
                                                                          ri_ ci_ d0 phii_ k' etype tpsi_ in
                       if mi_ = "_not_a_method_"
                       then phii,ri,ci,[(mi,reti,di,qi+++qi_)],tpsi
                       else phii,ri,ci,((mi,reti,di,qi+++qi_)::ys),tpsi)
                  (phi0,r0,c0,["_not_a_method_",ret0,d0,q0],tps0) r_tp in
              match xs with
              | [] -> failwith "variable type does not match any existing method (2)"
              | (("_not_a_method_",retn,dn,qn)::xs) ->
                 failwith "variable type does not match any existing method (3)"
              | ((mn,retn,dn,qn)::xs) ->
                 let cn',varscn' = c_update_all cn tpsn in
                 let pi,tpsgs =
                   List.fold_left
                     (fun (acc,decls) (mi,reti,di,qi) ->
                       (let guard_i,tpsgi = (f reti ret_tp (ret===(fst reti)) qi decls) in
                        (x===(z3_method mi)) ==> (guard_i &&& c_wedge cn' di)&&&acc,tpsgi))
                     (True,varscn') ((mn,retn,dn,qn)::xs) in
                 let guard_final,tpsgfinal = (f ret0 ret_tp pi q0 tpsgs) in
                 (ret_tp,guard_final &&& phin,rn,cn',cn',qn,tpsgfinal))
          | _ -> failwith "is not an arrow type"))
