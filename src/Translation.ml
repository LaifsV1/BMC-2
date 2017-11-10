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
                   sprintf "_m_%s_"   (string_of_int (!counter_m))
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
(* THIS ASSUMES t IS ALWAYS FRESH, WHICH IT IS IN THE TRANSLATION *)
let rec subs (m : term) (t : _var) (y : _var) =
  match m with
  | Fail | Skip | Int _ | Method _ | Deref _ -> m
  | Var x -> if x = y then Var(t) else m
  | Lambda(xs,t',tp) ->
     if List.mem t xs then failwith "accidental binding in subs"
     else
       if List.mem y xs
       then (printf "\n ;;;;;; WARNING: t = y \n"; Lambda(xs,t',tp)) (* WARNING: this is not standard *)
       else Lambda(xs,subs t' t y,tp)
  | Left (t',tp) -> Left(subs t' t y,tp)
  | Right (t',tp) -> Right(subs t' t y,tp)
  | Assign(r,t') -> Assign(r,subs t' t y)
  | Pair(t1,t2) -> Pair(subs t1 t y, subs t2 t y)
  | BinOp(op,t1,t2) -> BinOp(op,subs t1 t y,subs t2 t y)
  | Let(x,t1,t2) -> if x = y
                    then Let(x,t1,t2)
                    else Let(x,subs t1 t y,subs t2 t y)
  | ApplyM(m,t') -> ApplyM(m,List.map (fun ti -> subs ti t y) t')
  | If(tb,t1,t0) -> If(subs tb t y,subs t1 t y,subs t0 t y)
  | ApplyX(x,t') -> if x = y
                    then ApplyX(t,List.map (fun ti -> subs ti t y) t')
                    else ApplyX(x,List.map (fun ti -> subs ti t y) t')
  | Letrec(f,xs,t1,t2) ->
     if f = y
     then Letrec(f,xs,t1,t2)
     else
       if List.mem t xs then failwith "accidental binding in subs"
       else
         if List.mem y xs
         then (printf "\n ;;;;;; WARNING: t = y \n";  (* WARNING: this is not standard *)
               Letrec(f,xs,t1,subs t2 t y))
         else Letrec(f,xs,subs t1 t y,subs t2 t y)

let rec subslist (m : term) (ts : _var list) (ys : _var list) =
  match ts,ys with
  | [t],[y] -> subs m t y
  | t::ts, y::ys -> subslist (subs m t y) ts ys
  | _ -> failwith "not same number of arguments (1)"

let rec untyped_subslist (m : term) (ts : _name list) (ys : _var list) =
  match ts,ys with
  | [],[] -> m
  | t::ts, (y,tp)::ys -> untyped_subslist (subs m (t,tp) (y,tp)) ts ys
  | _ -> failwith (sprintf "not same number of arguments (2): %s" (string_of_term m))

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
      | Arrow(_,_)   -> tfail_m,tnil_m,acc
      | Product(a,b) -> let n,is_new = get_type_number tp in
                        let a,b = tfail_n n,tnil_n n in
                        if is_new
                        then a,b,(tfail_n n,z3_of_tp tp)::(tnil_n n,z3_of_tp tp)::acc
                        else a,b,acc in
  let faila,nila,decl1 = select_check tpa acc in
  let failb,nilb,decl2 = select_check tpb decl1 in
  pred faila failb nila nilb , decl2

let rec f_rets_helper rets (b : _ret) (p : proposition) (acc : _decl) :(proposition * _decl) =
  match rets with
  | [] -> p , acc
  | (a,q)::rets -> let p,decl = f a b p q acc in
                   f_rets_helper rets b p decl
let f_rets rets = f_rets_helper (List.rev rets)

(* translation *)
let rec bmc_translation
          (m : term) (r : repo) (c : counter) (d : counter)
          (phi : proposition) (k : nat) (etype : tp) (tps : (_name * z3_tp) list)
          (ptc : ptsmap) (ptd : ptsmap)
        :(_ret * proposition * repo * counter * counter * e_prop * (_name * z3_tp) list * ptsmap * ptsmap) =
  let ret = fresh_ret () in
  let ret_tp = ret,etype in
  let new_tps = (ret,z3_of_tp etype)::tps in (* (ret1,type1)::(ret2,type2)::tps *)
  match k with
  | Nil ->
     (match etype with
      | Unit    -> (ret_tp,(ret===tnil_u) &&& phi,r,c,d,Nil,new_tps,ptc,ptd)
      | Integer -> (ret_tp,(ret===tnil_i) &&& phi,r,c,d,Nil,new_tps,ptc,ptd)
      | Arrow _ -> (ret_tp,(ret===tnil_m) &&& phi,r,c,d,Nil,new_tps,ptc,ptd)
      | Product (tp1,tp2) ->
         let n,is_new = get_type_number etype in
         let new_tps' = if is_new then (tnil_n n,z3_of_tp etype)::new_tps else new_tps in
         (ret_tp,(ret===(tnil_n n)) &&& phi,r,c,d,Nil,new_tps',ptc,ptd))
  | Suc(k') ->
     (match m with
      (* base cases *)
      | Fail ->
         (match etype with
          | Unit    -> (ret_tp,(ret===tfail_u) &&& phi,r,c,d,Fail,new_tps,ptc,ptd)
          | Integer -> (ret_tp,(ret===tfail_i) &&& phi,r,c,d,Fail,new_tps,ptc,ptd)
          | Arrow _ -> (ret_tp,(ret===tfail_m) &&& phi,r,c,d,Fail,new_tps,ptc,ptd)
          | Product (tp1,tp2) ->
             let n,is_new = get_type_number etype in
             let new_tps' = if is_new then (tfail_n n,z3_of_tp etype)::new_tps else new_tps in
             (ret_tp,(ret===(tfail_n n)) &&& phi,r,c,d,Fail,new_tps',ptc,ptd))
      | Skip -> (ret_tp,(ret===tskip) &&& (ret=/=tfail_u) &&& (ret=/=tnil_u) &&& phi,r,c,d,Val,new_tps,ptc,ptd)
      | Int i -> (ret_tp,(ret===(string_of_int i)) &&& (ret=/=tfail_i) &&& (ret=/=tnil_i) &&& phi,r,c,d,Val,new_tps,ptc,ptd)
      | Method m ->  (ret_tp,(ret===(z3_method m)) &&& (ret=/=tfail_m) &&& (ret=/=tnil_m) &&& phi,r,c,d,Val,new_tps,
                     pts_update ptc (ret_tp) (Meths [m]),pts_update ptd (ret_tp) (Meths [m]))
      (*adding != fail/nil is not sound here vvv*) (*warning: we removed ret, but we might want to add it back*)
      | Var(x,t) -> ((x,t),phi,r,c,d,Both,new_tps,
                     pts_update ptc (ret_tp) (pts_get ptd (x,t)),pts_update ptd (ret_tp) (pts_get ptd (x,t)))
      | Deref aref ->
         let d_r = ref_get d aref in
         (match etype with
          | Unit    -> (ret_tp,(ret===d_r) &&& phi,r,c,d,Val,new_tps,ptc,ptd)
          | Integer -> (ret_tp,(ret===d_r) &&& phi,r,c,d,Val,new_tps,ptc,ptd)
          | Arrow _ -> (ret_tp,(ret===d_r) &&& phi,r,c,d,Val,new_tps,
                        pts_update ptc (ret_tp) (pts_get ptd aref),pts_update ptd (ret_tp) (pts_get ptd aref))
          | Product (tp1,tp2) ->
             let n,is_new = get_type_number etype in
             let new_tps' = if is_new then (tnil_n n,z3_of_tp etype)::(tfail_n n,z3_of_tp etype)::new_tps else new_tps in
             (ret_tp,(ret===d_r) &&& phi,r,c,d,Nil,new_tps',ptc,ptd))
      | Lambda(x,t,tp') ->
         let new_meth = fresh_m () in
         let r' = repo_update r new_meth (x,t,tp') in
         (ret_tp,(ret===(z3_method new_meth)) &&& (ret=/=tfail_m) &&& (ret=/=tnil_m) &&& phi,
          r',c,d,Val,new_tps,pts_update ptc (ret_tp) (Meths [new_meth]),pts_update ptd (ret_tp) (Meths [new_meth]))
      (* inductive cases *)
      | Left (t,tp) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1,ptc1,ptd1) = bmc_translation t r c d phi k tp new_tps ptc ptd in
         let guard_1,tpsg1 = (f ret1 ret_tp (ret===(z3_pair_left (fst ret1))) q1 tps1) in
         (ret_tp,guard_1 &&& phi1,r1,c1,d1,q1,tpsg1,
          pts_update ptc1 (ret_tp) (pts_left (pts_get ptd1 ret_tp)),pts_update ptd1 (ret_tp) (pts_left (pts_get ptd1 ret_tp)))
      | Right (t,tp) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1,ptc1,ptd1) = bmc_translation t r c d phi k tp new_tps ptc ptd in
         let guard_1,tpsg1 = (f ret1 ret_tp (ret===(z3_pair_right (fst ret1))) q1 tps1) in
         (ret_tp,guard_1 &&& phi1,r1,c1,d1,q1,tpsg1,
          pts_update ptc1 (ret_tp) (pts_right (pts_get ptd1 ret_tp)),pts_update ptd1 (ret_tp) (pts_right (pts_get ptd1 ret_tp)))
      | Assign(aref,t) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1,ptc1,ptd1) = bmc_translation t r c d phi k (snd aref) new_tps ptc ptd in
         let c1',caref = c_update c aref in
         let d1',daref = d_update d aref (cd_get c1' aref) in
         let guard_1,tpsg1 = (f ret1 ret_tp ((ret===tskip) &&& (ret=/=tfail_u) &&& (ret=/=tnil_u) &&& (daref===(fst ret1))) q1 tps1) in
         (ret_tp,guard_1 &&& phi1,r1,c1',d1',q1,
          (daref,z3_of_tp (snd aref))::tpsg1,
          pts_update ptc1 aref (pts_union (pts_get ptd1 aref) (pts_get ptd1 ret1)),pts_update ptd1 aref (pts_union (pts_get ptd1 aref) (pts_get ptd1 ret1)))
      | Pair(t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1,ptc1,ptd1) = bmc_translation t1 r c d phi k (left_tp etype) new_tps ptc ptd in
         let (ret2,phi2,r2,c2,d2,q2,tps2,ptc2,ptd2) = bmc_translation t2 r1 c1 d1 phi1 k (right_tp etype) tps1 ptc1 ptd1 in
         let guard_1,tpsg1 = (f ret2 ret_tp (ret===(z3_pair_maker (fst ret1) (fst ret2))) q2 tps2) in
         let guard_2,tpsg2 = (f ret1 ret_tp guard_1 q1 tpsg1) in
         (ret_tp,guard_2 &&& phi2,r2,c2,d2,q1+++q2,tpsg2,
          pts_update ptc2 ret_tp (Pair(pts_get ptd2 ret1,pts_get ptd2 ret2)),pts_update ptd2 ret_tp (Pair(pts_get ptd2 ret1,pts_get ptd2 ret2)))
      | BinOp(op,t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1,ptc1,ptd1) = bmc_translation t1 r c d phi k (etype) new_tps ptc ptd in
         let (ret2,phi2,r2,c2,d2,q2,tps2,ptc2,ptd2) = bmc_translation t2 r1 c1 d1 phi1 k (etype) tps1 ptc1 ptd1 in
         let guard_1,tpsg1 = (f ret2 ret_tp ((ret===(z3_binops (fst ret1) op (fst ret2))) &&& (ret=/=tfail_i) &&& (ret=/=tnil_i)) q2 tps2) in
         let guard_2,tpsg2 = (f ret1 ret_tp guard_1 q1 tpsg1) in
         (ret_tp,guard_2 &&& phi2,r2,c2,d2,q1+++q2,tpsg2,ptc2,ptd2)
      | Let((x,tp),t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1,ptc1,ptd1) = bmc_translation t1 r c d phi k tp new_tps ptc ptd in
         let (ret2,phi2,r2,c2,d2,q2,tps2,ptc2,ptd2) = bmc_translation (subs t2 ret1 (x,tp))
                                                                      r1 c1 d1 phi1 k etype tps1 ptc1 ptd1 in
         let guard_1,tpsg1 = (f ret2 ret_tp (ret===(fst ret2)) q2 tps2) in
         let guard_2,tpsg2 = (f ret1 ret_tp guard_1 q1 tpsg1) in
         (ret_tp,guard_2 &&& phi2,r2,c2,d2,q1+++q2,tpsg2,
          pts_update ptc2 ret_tp (pts_get ptd2 ret2),pts_update ptd2 ret_tp (pts_get ptd2 ret2))
      | Letrec((f,tp),xs,t1,t2) ->
         let new_meth = fresh_m () in
         let new_f    = fresh_x () in
         let r' = repo_update r new_meth (xs,subs t1 (new_f,tp) (f,tp),tp) in
         let ptc' = pts_update ptc (new_f,tp) (Meths [new_meth]) in
         let ptd' = pts_update ptd (new_f,tp) (Meths [new_meth]) in
         let (ret1,phi1,r1,c1,d1,q1,tps1,ptc1,ptd1) = bmc_translation (subs t2 (new_f,tp) (f,tp))
                                                                      r' c d ((new_f === (sprintf "\"%s\""new_meth)) &&& phi) k etype
                                                                      ((new_f,z3_of_tp tp)::new_tps) ptc' ptd' in
         (ret_tp,(ret===(fst ret1))&&&phi1,r1,c1,d1,q1,tps1,ptc1,ptd1)
      | ApplyM(m,ts) ->
         let (xs,n,tp) = repo_get r m in
         let args,rets,phi1,r1,c1,d1,q1,tps1,ptc1,ptd1 = bmc_args (List.map snd xs) ts r c d phi k new_tps [] [] Val ptc ptd in
         let (ret2,phi2,r2,c2,d2,q2,tps2,ptc2,ptd2) = bmc_translation (subslist n rets xs)
                                                                      r1 c1 d1 phi1 k' etype tps1 ptc1 ptd1 in
         let guard_1,tpsg1 = (f ret2 ret_tp (ret===(fst ret2)) q2 tps2) in
         let guard_2,tpsg2 = (f_rets args ret_tp guard_1 tpsg1) in
         (ret_tp,guard_2 &&& phi2,r2,c2,d2,q1+++q2,tpsg2,
          pts_update ptc2 ret_tp (pts_get ptd2 ret2),pts_update ptd2 ret_tp (pts_get ptd2 ret2))
      | If(tb,t1,t0) ->
         let (retb,phib,rb,cb,db,qb,tpsb,ptcb,ptdb) = bmc_translation tb r c d phi k Integer new_tps ptc ptd in
         let (ret0,phi0,r0,c0,d0,q0,tps0,ptc0,ptd0) = bmc_translation t0 rb cb db phib k etype tpsb ptcb ptdb in
         let (ret1,phi1,r1,c1,d1,q1,tps1,ptc1,ptd1) = bmc_translation t1 r0 c0 db phi0 k etype tps0 ptc0 ptdb in
         let c',varsc' = c_update_all c1 tps1 in
         let guard_0,tpsg0 = (f ret0 ret_tp ((ret===(fst ret0)) &&& (c_wedge c' d0)) q0 varsc') in
         let guard_1,tpsg1 = (f ret1 ret_tp ((ret===(fst ret1)) &&& (c_wedge c' d1)) q1 tpsg0) in
         let pi0 = ((fst retb) === "0") ==> guard_0 in
         let pi1 = ((fst retb) =/= "0") ==> guard_1 in
         let guard_b,tpsgb = (f retb ret_tp (pi0 &&& pi1) qb tpsg1) in
         let ptc1' = pts_update ptc1 ret_tp (pts_union (pts_get ptd0 ret0) (pts_get ptd1 ret1)) in
         (ret_tp,guard_b &&& phi1,r1,c',c',qb+++q0+++q1,tpsgb,ptc1',ptc1')
      | ApplyX((x,tp),ts) ->
         (match tp with
          | Arrow(one,two) ->
             (let args,rets,phi0,r0,c0,d0,q0,tps0,ptc0,ptd0 = bmc_args one ts r c d phi k new_tps [] [] Val ptc ptd in
              let r_tp = get_method_body_of_list r (pts_get_methods ptd0 (x,tp)) [] in
              match r_tp with
              | [] -> (ret_tp,(ret =/= (z3_nil_of_tp etype)) &&& (ret =/= (z3_fail_of_tp etype)) &&& phi0,r0,c0,c0,q0,tps0,ptc0,ptc0)
              | _ ->
                 let phin,rn,cn,xs,tpsn,ptcn =
                   List.fold_left
                     (fun (phii_,ri_,ci_,ys,tpsi_,ptci_) (mi,xi,ti) ->  (*mi = \(xi).ti*)
                       let (reti,phii,ri,ci,di,qi,tpsi,ptci,ptdi) = bmc_translation (subslist ti rets xi)
                                                                                    ri_ ci_ d0 phii_ k' etype tpsi_ ptci_ ptd0 in
                       match ys with
                       | [] ->
                          phii,ri,ci,[(mi,reti,di,qi+++q0,ptdi)],tpsi,ptci
                       | ((mi_,reti_,di_,qi_,ptdi_)::ys') ->
                          phii,ri,ci,((mi,reti,di,qi+++qi_,ptdi)::ys),tpsi,ptci)
                     (phi0,r0,c0,[],tps0,ptc0) r_tp in
                 match xs with
                 | [] -> failwith (sprintf "variable %s does not match any method." x)
                 | ((mn,retn,dn,qn,ptdn)::xs) ->
                    let cn',varscn' = c_update_all cn tpsn in
                    let pi,tpsgs,pts =
                      List.fold_left
                        (fun (acc,decls,pts) (mi,reti,di,qi,ptdi) ->
                          (let guard_i,tpsgi = (f reti ret_tp (ret===(fst reti)) qi decls) in
                           (x===(z3_method mi)) ==> (guard_i &&& c_wedge cn' di)&&&acc,tpsgi,pts_union (pts_get ptdi reti) pts))
                        (True,varscn',Meths []) ((mn,retn,dn,qn,ptdn)::xs) in
                    let guard_final,tpsgfinal = (f_rets args ret_tp pi tpsgs) in
                    let ptcn' = pts_update ptcn ret_tp pts in
                    (ret_tp,guard_final &&& phin,rn,cn',cn',qn,tpsgfinal,ptcn',ptcn'))
          | _ -> failwith "is not an arrow type"))
  and bmc_args (xs : tp list) (ts : term list) (r:repo) (c:counter) (d:counter) (phi:proposition) (k:nat) (new_tps:(_name*z3_tp)list) acc rets q ptc ptd =
    match xs,ts with
    | [],[] -> List.rev acc,List.rev rets,phi,r,c,d,q,new_tps,ptc,ptd
    | x::xs,t::ts -> let (ret1,phi1,r1,c1,d1,q1,tps1,ptc1,ptd1) = bmc_translation t r c d phi k x new_tps ptc ptd in
                     let new_acc = (ret1,q1)::acc in
                     let new_rets = ret1::rets in
                     bmc_args xs ts r1 c1 d1 phi1 k tps1 new_acc new_rets (q1+++q) ptc1 ptd1
    | _ -> failwith "number of arguments mismatch"
