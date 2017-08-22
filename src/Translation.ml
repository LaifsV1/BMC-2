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

let types_seen = ref 0
let fresh_type () = types_seen := !types_seen + 1;!types_seen

let global_types = ref empty_types
let get_type_number tp =
  let map = !global_types in
  match types_get map tp with
  | -1 -> global_types := (types_add map tp (fresh_type ())); !types_seen
  | n  -> n

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
  | Left t' -> Left(subs t' t y)
  | Right t' -> Right(subs t' t y)
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
(* fail/nil-guards function*)
let f (a,tp : _ret) (b,_ : _ret) (p : proposition) (q : bool) :(proposition) =
  let pred tfail tnil = ((a === tfail) ==> (b === tfail))
                        &&& ((a === tnil) ==> (b === tnil))
                        &&& (((a === tfail) ||| (a === tnil)) ||| p)
  in  match tp with
      | Unit         -> if q then pred tfail_u tnil_u else p
      | Integer      -> if q then pred tfail_i tnil_i else p
      | Arrow(_,_)   -> if q then pred tfail_m tnil_m else p
      | Product(a,b) ->
         let n = get_type_number tp in
         if q then pred (tfail_n n) (tnil_n n) else p

(* translation *)
let rec bmc_translation
          (m : term) (r : repo) (c : counter) (d : counter)
          (phi : proposition) (k : nat) (etype : tp) (tps : (_name * z3_tp) list)
        :(_ret * proposition * repo * counter * counter * bool * (_name * z3_tp) list) =
  let ret = fresh_ret () in
  let ret_tp = ret,etype in
  let new_tps = (ret,z3_of_tp etype)::tps in (* (ret1,type1)::(ret2,type2)::tps *)
  match k with
  | Nil ->
     (match etype with
      | Unit    -> (ret_tp,(ret===tnil_u) &&& phi,r,c,d,true,new_tps)
      | Integer -> (ret_tp,(ret===tnil_i) &&& phi,r,c,d,true,new_tps)
      | Arrow _ -> (ret_tp,(ret===tnil_m) &&& phi,r,c,d,true,new_tps)
      | Product (tp1,tp2) ->
         let n = get_type_number etype in
         (ret_tp,(ret===(tnil_n n)) &&& phi,r,c,d,true,new_tps)) (**remember to get the decl from global types later**)
  | Suc(k') ->
     (match m with
      (* base cases *)
      | Fail ->
         (match etype with
          | Unit    -> (ret_tp,(ret===tfail_u) &&& phi,r,c,d,true,new_tps)
          | Integer -> (ret_tp,(ret===tfail_i) &&& phi,r,c,d,true,new_tps)
          | Arrow _ -> (ret_tp,(ret===tfail_i) &&& phi,r,c,d,true,new_tps)
          | Product (tp1,tp2) ->
             let n = get_type_number etype in
             (ret_tp,(ret===(tfail_n n)) &&& phi,r,c,d,true,new_tps))
      | Skip -> (ret_tp,(ret===tskip) &&& phi,r,c,d,false,new_tps)
      | Int i -> (ret_tp,(ret===(string_of_int i)) &&& phi,r,c,d,false,new_tps)
      | Method m -> (ret_tp,(ret===(z3_method m)) &&& phi,r,c,d,false,new_tps)
      | Var(x,t) -> (ret_tp,(ret===x) &&& phi,r,c,d,false,new_tps)
      | Deref aref ->
         let d_r = ref_get d aref in (ret_tp,(ret===d_r) &&& phi,r,c,d,false,new_tps)
      | Lambda(x,t,tp') ->
         let new_meth = fresh_m () in
         let r' = repo_update r new_meth (x,t,tp') in
         (ret_tp,(ret===(z3_method new_meth)) &&& phi,r',c,d,false,(new_meth,Meth)::new_tps)
      (* inductive cases *)
      | Left t ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t r c d phi k (left_tp etype) new_tps in
         (ret_tp,(f ret1 ret_tp (ret===(z3_pair_left (fst ret1))) q1) &&& phi1,r1,c1,d1,q1,tps1)
      | Right t ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t r c d phi k (right_tp etype) new_tps in
         (ret_tp,(f ret1 ret_tp (ret===(z3_pair_right (fst ret1))) q1) &&& phi1,r1,c1,d1,q1,tps1)
      | Assign(aref,t) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t r c d phi k (snd aref) new_tps in
         let c1',caref = c_update c aref in
         let d1',daref = d_update d aref (cd_get c1' aref) in
         let d1_r' = ref_get d1' aref in
         (ret_tp,(f ret1 ret_tp ((ret===tskip) &&& (d1_r'===(fst ret1))) q1) &&& phi1,r1,c1',d1',q1,
          (daref,z3_of_tp (snd aref))::(caref,z3_of_tp (snd aref))::tps1)
      | Pair(t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t1 r c d phi k (left_tp etype) new_tps in
         let (ret2,phi2,r2,c2,d2,q2,tps2) = bmc_translation t2 r1 c1 d1 phi1 k (right_tp etype) tps1 in
         (ret_tp,(f ret1 ret_tp (f ret2 ret_tp (ret===(z3_pair_maker (fst ret1) (fst ret2))) q2) q1)
                 &&& phi2,r2,c2,d2,q1||q2,tps2)
      | BinOp(op,t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t1 r c d phi k (etype) new_tps in
         let (ret2,phi2,r2,c2,d2,q2,tps2) = bmc_translation t2 r1 c1 d1 phi1 k (etype) tps1 in
         (ret_tp,(f ret1 ret_tp (f ret2 ret_tp (ret===(z3_binops (fst ret1) op (fst ret2))) q2) q1)
                 &&& phi2,r2,c2,d2,q1||q2,tps2)
      | Let((x,tp),t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t1 r c d phi k tp new_tps in
         let (ret2,phi2,r2,c2,d2,q2,tps2) = bmc_translation (subs t2 ret1 (x,tp))
                                                            r1 c1 d1 phi1 k etype tps1 in
         (ret_tp,(f ret1 ret_tp (f ret2 ret_tp (ret===(fst ret2)) q2) q1) &&& phi2,r2,c2,d2,q1||q2,tps2)
      | ApplyM(m,t) ->
         let (x,n,tp) = repo_get r m in
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t r c d phi k (snd x) new_tps in
         let (ret2,phi2,r2,c2,d2,q2,tps2) = bmc_translation (subs n ret1 x)
                                                            r1 c1 d1 phi1 k' etype tps1 in
         (ret_tp,(f ret1 ret_tp (f ret2 ret_tp (ret===(fst ret2)) q2) q1) &&& phi2,r2,c2,d2,q1||q2,tps2)
      | If(tb,t1,t0) ->
         let (retb,phib,rb,cb,db,qb,tpsb) = bmc_translation tb r c d phi k Integer new_tps in
         let (ret0,phi0,r0,c0,d0,q0,tps0) = bmc_translation t0 rb cb db phib k etype tpsb in
         let (ret1,phi1,r1,c1,d1,q1,tps1) = bmc_translation t1 r0 c0 d0 phi0 k etype tps0 in
         let c',varsc' = c_update_all c1 tps1 in
         let pi0 = ((fst retb) === "0") ==> (f ret0 ret_tp ((ret===(fst ret0)) &&& (c_wedge c' d0)) q0) in
         let pi1 = ((fst retb) =/= "0") ==> (f ret1 ret_tp ((ret===(fst ret1)) &&& (c_wedge c' d1)) q1) in
         (ret_tp,(f retb ret_tp (pi0 &&& pi1) qb) &&& phi1,r1,c',c',qb||q0||q1,varsc')
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
                       then phii,ri,ci,[(mi,reti,di,qi||qi_)],tpsi
                       else phii,ri,ci,((mi,reti,di,qi||qi_)::ys),tpsi)
                  (phi0,r0,c0,["_not_a_method_",ret0,d0,q0],tps0) r_tp in
              match xs with
              | [] -> failwith "variable type does not match any existing method (2)"
              | (("_not_a_method_",retn,dn,qn)::xs) ->
                 failwith "variable type does not match any existing method (3)"
              | ((mn,retn,dn,qn)::xs) ->
                 let cn',varscn' = c_update_all cn tpsn in
                 let pi =
                   List.fold_left
                     (fun acc (mi,reti,di,qi) ->
                       (x===(z3_method mi)) ==> ((f reti ret_tp (ret===(fst reti)) qi) &&& c_wedge cn' di)&&&acc)
                     True ((mn,retn,dn,qn)::xs) in
                 (ret_tp,(f ret0 ret_tp pi q0) &&& phin,rn,cn',cn',qn,varscn'))
          | _ -> failwith "is not an arrow type"))
