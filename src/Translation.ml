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
                   sprintf "_x%s_"   (string_of_int (!counter_x))
let fresh_m   () = counter_m  := !counter_m + 1;
                   sprintf "_m%s_"   (string_of_int (!counter_m))
let fresh_ret () = counter_ret := !counter_ret + 1;
                   sprintf "_ret%s_" (string_of_int (!counter_ret))

(**********************)
(* Substitute: M{t/y} *)
(**********************)
let rec subs (m : term) (t : term) (y : _var) =
  match m with
  | Fail | Skip | Int _ | Method _ | Deref _ -> m
  | Var x -> if x = y then t else m
  | Lambda(x,t',tp) ->
     if x = y
     then let x' = (fresh_x (),snd x) in
          Lambda(x',subs t' (Var x') x,tp)
     else Lambda(x,subs t' t y,tp)
  | Left t' -> Left(subs t' t y)
  | Right t' -> Right(subs t' t y)
  | Assign(r,t') -> Assign(r,subs t' t y)
  | Pair(t1,t2) -> Pair(subs t1 t y, subs t2 t y)
  | BinOp(op,t1,t2) -> BinOp(op,subs t1 t y,subs t2 t y)
  | Let(x,t1,t2) -> if x = y
                    then let x' = (fresh_x (),snd x) in
                         Let(x',subs t1 t y,subs t2 (Var x') x)
                    else Let(x,subs t1 t y,subs t2 t y)
  | ApplyM(m,t') -> ApplyM(m,subs t' t y)
  | If(tb,t1,t0) -> If(subs tb t y,subs t1 t y,subs t0 t y)
  | ApplyX(x,t') -> if x = y
                    then ApplyX(y,subs t' t y)
                    else ApplyX(x,subs t' t y)

(*******************)
(* BMC Translation *)
(*******************)
let f a b p q =
  if q
  then ((a === tfail) ==> (b === tfail))
       &&& ((a === tnil) ==> (b === tnil))
       &&& (((a === tfail) ||| (a === tnil)) ||| p)
  else p

let rec bmc_translation
          (m : term) (r : repo) (c : counter) (d : counter)
          (phi : proposition) (k : nat)
        :(_ret * proposition * repo * counter * counter * bool) =
  let ret = fresh_ret () in
  match k with
  | Nil -> (ret,(ret===tnil) &&& phi,r,c,d,true)
  | Suc(k') ->
     (match m with
      (* base cases *)
      | Fail -> (ret,(ret===(string_of_term m)) &&& phi,r,c,d,true)
      | Skip | Int _ | Method _ ->
         let s = (string_of_term m) in (ret,(ret===s) &&& phi,r,c,d,false)
      | Var(x,t) -> (ret,(ret===x) &&& phi,r,c,d,false)
      | Deref aref ->
         let d_r = ref_get d aref in (ret,(ret===d_r) &&& phi,r,c,d,false)
      | Lambda(x,t,tp') ->
         let new_meth = fresh_m () in
         let r' = repo_update r new_meth (x,t,tp') in
         (ret,(ret===new_meth) &&& phi,r',c,d,false)
      (* inductive cases *)
      | Left t ->
         let (ret1,phi1,r1,c1,d1,q1) = bmc_translation t r c d phi k in
         (ret,(f ret1 ret (ret===(sprintf "(Left %s)" ret1)) q1) &&& phi1,r1,c1,d1,q1)
      | Right t ->
         let (ret1,phi1,r1,c1,d1,q1) = bmc_translation t r c d phi k in
         (ret,(f ret1 ret (ret===(sprintf "(Right %s)" ret1)) q1) &&& phi1,r1,c1,d1,q1)
      | Assign(aref,t) ->
         let (ret1,phi1,r1,c1,d1,q1) = bmc_translation t r c d phi k in
         let c1' = c_update c aref in
         let d1' = d_update d aref (cd_get c1' aref) in
         (ret,(f ret1 ret (ret===tskip) q1) &&& phi1,r1,c1',d1',q1)
      | Pair(t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1) = bmc_translation t1 r c d phi k in
         let (ret2,phi2,r2,c2,d2,q2) = bmc_translation t2 r1 c1 d1 phi1 k in
         (ret,(f ret1 ret (f ret2 ret (ret===(sprintf "(%s,%s)" ret1 ret2)) q2) q1)
              &&& phi2,r2,c2,d2,q1||q2)
      | BinOp(op,t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1) = bmc_translation t1 r c d phi k in
         let (ret2,phi2,r2,c2,d2,q2) = bmc_translation t2 r1 c1 d1 phi1 k in
         (ret,(f ret1 ret (f ret2 ret (ret===(sprintf "(%s %s %s)" ret1 op ret2)) q2) q1)
              &&& phi2,r2,c2,d2,q1||q2)
      | Let((x,tp),t1,t2) ->
         let (ret1,phi1,r1,c1,d1,q1) = bmc_translation t1 r c d phi k in
         let (ret2,phi2,r2,c2,d2,q2) = bmc_translation (subs t2 (Var (ret1,tp)) (x,tp))
                                                       r1 c1 d1 phi1 k in
         (ret,(f ret1 ret (f ret2 ret (ret===ret2) q2) q1) &&& phi2,r2,c2,d2,q1||q2)
      | ApplyM(m,t) ->
         let (ret1,phi1,r1,c1,d1,q1) = bmc_translation t r c d phi k in
         let (x,n,tp) = repo_get r m in
         let (ret2,phi2,r2,c2,d2,q2) = bmc_translation (subs n (Var (ret1,snd x)) x)
                                                       r1 c1 d1 phi1 k' in
         (ret,(f ret1 ret (f ret2 ret (ret===ret2) q2) q1) &&& phi2,r2,c2,d2,q1||q2)
      | If(tb,t1,t0) ->
         let (retb,phib,rb,cb,db,qb) = bmc_translation tb r c d phi k in
         let (ret0,phi0,r0,c0,d0,q0) = bmc_translation t0 rb cb db phib k in
         let (ret1,phi1,r1,c1,d1,q1) = bmc_translation t1 r0 c0 d0 phi0 k in
         let c' = c_update_all c1 in
         let pi0 = f ret0 ret ((retb === "0") ==> ((ret===ret0) &&& (c_wedge c' d0))) q0 in
         let pi1 = f ret1 ret ((retb =/= "0") ==> ((ret===ret1) &&& (c_wedge c' d1))) q1 in
         (ret,(f retb ret (pi0 &&& pi1) qb) &&& phi1,r1,c',c',qb||q0||q1)
      | ApplyX((x,tp),t) ->
         let (ret0,phi0,r0,c0,d0,q0) = bmc_translation t r c d phi k in
         let r_tp = get_methods r0 tp in
         let phin,rn,cn,xs =
           List.fold_left
             (fun (phii_,ri_,ci_,ys) (mi,xi,ti) ->
               match ys with
               | [] -> failwith "variable type does not match any existing method (1)"
               | ((mi_,reti_,di_,qi_)::ys') ->
                  let (reti,phii,ri,ci,di,qi) = bmc_translation (subs ti (Var (ret0,tp)) (x,tp))
                                                                ri_ ci_ d0 phii_ k' in
                  if mi_ = "_not_a_method_"
                  then phii,ri,ci,[(mi,reti,di,qi||qi_)]
                  else phii,ri,ci,((mi,reti,di,qi||qi_)::ys))
             (phi0,r0,c0,["_not_a_method_",ret0,d0,q0]) r_tp in
         match xs with
         | [] -> failwith "variable type does not match any existing method (2)"
         | (("_not_a_method_",retn,dn,qn)::xs) ->
            failwith "variable type does not match any existing method (3)"
         | ((mn,retn,dn,qn)::xs) ->
            let cn' = c_update_all cn in
            let pi =
              List.fold_left
                (fun acc (mi,reti,di,qi) ->
                  (x===mi) ==> ((f reti ret (ret===reti) qi) &&& c_wedge cn' di)&&&acc)
                True ((mn,retn,dn,qn)::xs) in
            (ret,(f ret0 ret pi q0) &&& phin,rn,cn',cn',qn))
