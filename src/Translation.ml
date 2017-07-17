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
let f a b p =
  ((a === tfail) ==> (b === tfail))
  &&& ((a === tnil) ==> (b === tnil))
  &&& (((a === tfail) ||| (a === tnil)) ||| p)

let rec bmc_translation
          (m : term) (r : repo) (c : counter) (d : counter)
          (phi : proposition) (k : nat)
        :(_ret * proposition * repo * counter * counter) =
  let ret = fresh_ret () in
  match k with
  | Nil -> (ret,(ret===tnil) &&& phi,r,c,d)
  | Suc(k') ->
     (match m with
      | Fail | Skip | Int _ | Method _ ->
         let s = (string_of_term m) in (ret,(ret===s) &&& phi,r,c,d)
      | Var(x,t) -> (ret,(ret===x) &&& phi,r,c,d)
      | Deref aref ->
         let d_r = ref_get d aref in (ret,(ret===d_r) &&& phi,r,c,d)
      | Lambda(x,t,tp') ->
         let new_meth = fresh_m () in
         let r' = repo_update r new_meth (x,t,tp') in
         (ret,(ret===new_meth) &&& phi,r',c,d)
      | Left t ->
         let (ret1,phi1,r1,c1,d1) = bmc_translation t r c d phi k in
         (ret,(f ret1 ret (ret===(sprintf "(Left %s)" ret1))) &&& phi1,r1,c1,d1)
      | Right t ->
         let (ret1,phi1,r1,c1,d1) = bmc_translation t r c d phi k in
         (ret,(f ret1 ret (ret===(sprintf "(Right %s)" ret1))) &&& phi1,r1,c1,d1)
      | Assign(aref,t) ->
         let (ret1,phi1,r1,c1,d1) = bmc_translation t r c d phi k in
         let c1' = c_update c aref in
         let d1' = d_update d aref (cd_get c1' aref) in
         (ret,(f ret1 ret (ret===tskip)) &&& phi1,r1,c1',d1')
      | Pair(t1,t2) ->
         let (ret1,phi1,r1,c1,d1) = bmc_translation t1 r c d phi k in
         let (ret2,phi2,r2,c2,d2) = bmc_translation t2 r1 c1 d1 phi1 k in
         (ret,(f ret1 ret (f ret2 ret (ret===(sprintf "(%s,%s)" ret1 ret2))))
              &&& phi2,r2,c2,d2)
      | BinOp(op,t1,t2) ->
         let (ret1,phi1,r1,c1,d1) = bmc_translation t1 r c d phi k in
         let (ret2,phi2,r2,c2,d2) = bmc_translation t2 r1 c1 d1 phi1 k in
         (ret,(f ret1 ret (f ret2 ret (ret===(sprintf "(%s %s %s)" ret1 op ret2))))
              &&& phi2,r2,c2,d2)
      | Let((x,tp),t1,t2) ->
         let (ret1,phi1,r1,c1,d1) = bmc_translation t1 r c d phi k in
         let (ret2,phi2,r2,c2,d2) = bmc_translation (subs t2 (Var (ret1,tp)) (x,tp))
                                                    r1 c1 d1 phi1 k in
         (ret,(f ret1 ret (f ret2 ret (ret===ret2))) &&& phi2,r2,c2,d2)
      | ApplyM(m,t) ->
         let (ret1,phi1,r1,c1,d1) = bmc_translation t r c d phi k in
         let (x,n,tp) = repo_get r m in
         let (ret2,phi2,r2,c2,d2) = bmc_translation (subs n (Var (ret1,snd x)) x)
                                                    r1 c1 d1 phi1 k' in
         (ret,(f ret1 ret (f ret2 ret (ret===ret2))) &&& phi2,r2,c2,d2)
      | If(tb,t1,t0) ->
         let (retb,phib,rb,cb,db) = bmc_translation tb r c d phi k in
         let (ret0,phi0,r0,c0,d0) = bmc_translation t0 rb cb db phib k in
         let (ret1,phi1,r1,c1,d1) = bmc_translation t1 r0 c0 d0 phi0 k in
         let c' = c_update_all c1 in
         let pi0 = f ret0 ret ((retb === "0") ==> ((ret===ret0) &&& (c_wedge c' d0))) in
         let pi1 = f ret1 ret ((retb =/= "0") ==> ((ret===ret1) &&& (c_wedge c' d1))) in
         (ret,(f retb ret (pi0 &&& pi1)) &&& phi1,r1,c',c')
      | ApplyX((x,tp),t) ->
         let (ret0,phi0,r0,c0,d0) = bmc_translation t r c d phi k in
         let r_tp = get_methods r0 tp in
         let xs =
           List.fold_left
             (fun ys (mi,xi,ti) ->
               match ys with
               | [] -> failwith "variable type does not match any existing method (1)"
               | ((mi_,reti_,phii_,ri_,ci_,di_)::ys') ->
                  let (reti,phii,ri,ci,di) = bmc_translation (subs ti (Var (ret0,tp)) (x,tp))
                                                             ri_ ci_ d0 phii_ k' in
                  if mi_ = "_not_a_method_"
                  then [(mi,reti,phii,ri,ci,di)]
                  else (mi,reti,phii,ri,ci,di)::ys)
             ["_not_a_method_",ret0,phi0,r0,c0,d0] r_tp in
         match xs with
         | [] -> failwith "variable type does not match any existing method (2)"
         | ((mn,retn,phin,rn,cn,dn)::xs) ->
            let cn' = c_update_all cn in
            let pi =
              List.fold_left
                (fun acc (mi,reti,_,_,_,di) ->
                  (x===mi) ==> ((f reti ret (ret===reti)) &&& c_wedge cn' di))
                True ((mn,retn,phin,rn,cn,dn)::xs) in
            (ret,(f ret0 ret pi) &&& phin,rn,cn',cn'))

(****************)
(*** RUN TEST ***)
(****************)
let factorial = (("x",Integer),If(Var("x",Integer),Int(1),ApplyM("fact",BinOp("-",Var("x",Integer),Int(1)))),Arrow(Integer,Integer))

let result = bmc_translation (ApplyM("fact",Int(3)))
                             (Repo.add "fact" factorial (empty_repo))
                             (empty_counter)
                             (empty_counter) True (nat_of_int 1)

let _ = let (ret,phi,repo,c_counter,d_counter) = result in
        printf "Formula:\n %s\n" (string_of_proposition (phi));
        exit 0
