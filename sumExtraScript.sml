open hardwarePreamble;

open alistTheory;

open monadsyntax;

val _ = new_theory "sumExtra";

(* Error type, should probably have a lot more cases *)
val error_def = Datatype `
 error = UnknownVariable | TypeError | InvalidIndex | NotImplemented | InvalidArgument`;

val sum_bind_def = Define `
  (sum_bind (INL l) _ = INL l) /\
  (sum_bind (INR r) f = f r)`;

declare_monad ("sum", { bind = ``sum_bind``,
                        ignorebind = NONE,
                        unit = ``INR``,
                        guard = NONE,
                        choice = NONE,
                        fail = SOME ``INL`` });

enable_monadsyntax ();
enable_monad "sum";

Theorem sum_bind_INR:
 !x f v. sum_bind x f = INR v <=> ?v'. x = INR v' /\ f v' = INR v
Proof
 Cases \\ simp [sum_bind_def]
QED

Theorem sum_bind_cong:
 ∀x1 f1 f2. (∀x. f1 x = f2 x) ⇒ sum_bind x1 f1 = sum_bind x1 f2
Proof
 rw [GSYM FUN_EQ_THM]
QED

Theorem sum_bind_id[simp]:
 (∀x. sum_bind x INR = x) ∧ (∀x. sum_bind x (λx. INR x) = x)
Proof
 simp [PULL_FORALL] \\ rpt Cases \\ simp [sum_bind_def]
QED

val sum_bind_INR_old = Q.store_thm("sum_bind_INR_old",
 `!s f v. sum_bind s f = INR v ==> ?v'. s = INR v'`,
 rw [sum_bind_INR]);

val sum_check_def = Define `
 sum_check b err = if b then INR () else INL err`;

Theorem sum_check_INR:
 !b err. sum_check b err = INR () <=> b
Proof
 rw [sum_check_def]
QED
           
(* There's also a "map" in sumTheory, called ++ I think, but it takes two functions *)
val sum_map_def = Define `
  (sum_map f (INR r) = INR (f r)) /\
  (sum_map _ (INL v) = INL v)`;

val sum_map_INR = Q.store_thm("sum_map_INR",
 `!x f v. sum_map f x = INR v <=> ?v'. x = INR v' /\ f v' = v`,
 Cases \\ simp [sum_map_def]);

val sum_map_INR_old = Q.store_thm("sum_map_INR_old",
 `!s f v. sum_map f s = INR v ==> ?v'. s = INR v'`,
 rw [sum_map_INR]);

Theorem sum_map_cong:
 ∀x1 x2 f1 f2. (∀x. f1 x = f2 x) ∧ x1 = x2 ⇒ sum_map f1 x1 = sum_map f2 x2
Proof
 rw [GSYM FUN_EQ_THM]
QED

val sum_for_def = Define `
  sum_for s f = sum_map f s`;

val sum_for_INR = Q.store_thm("sum_for_INR",
 `!s f v. sum_for s f = INR v <=> ?v'. s = INR v' /\ f v' = v`,
 rw [sum_for_def, sum_map_INR]);

val sum_for_INR_old = Q.store_thm("sum_for_INR_old",
 `!s f v. sum_for s f = INR v ==> ?v'. s = INR v'`,
 rw [sum_for_INR]);

val sum_alookup_def = Define `
 sum_alookup env var =
  case ALOOKUP env var of
    NONE => INL UnknownVariable
  | SOME t => INR t`;

Theorem sum_alookup_INR:
 !env k v. sum_alookup env k = INR v <=> ALOOKUP env k = SOME v
Proof
 rw [sum_alookup_def] \\ TOP_CASE_TAC
QED

Theorem sum_alookup_INL:
 !env k e. sum_alookup env k = INL e <=> ALOOKUP env k = NONE ∧ e = UnknownVariable
Proof
 rw [sum_alookup_def] \\ TOP_CASE_TAC \\ simp []
QED

Theorem sum_alookup_nil[simp]:
 !k. sum_alookup [] k = INL UnknownVariable
Proof
 rw [sum_alookup_def]
QED

Theorem sum_alookup_cons:
 !k1 k2 v env. sum_alookup ((k1, v)::env) k2 = if k1 = k2 then INR v else sum_alookup env k2
Proof
 rw [sum_alookup_def]
QED

Theorem sum_alookup_append:
 !var env1 env2.
   sum_alookup (env1 ++ env2) var =
    case sum_alookup env1 var of
      INL e => sum_alookup env2 var
    | INR v => INR v
Proof
 rw [sum_alookup_def, ALOOKUP_APPEND] \\ every_case_tac \\ simp []
QED

(* mapM for sum: mapM :: Monad m => (a -> m b) -> t a -> m (t b) *)
(* TODO: The middle can be replaced by a sum_bind *)
val sum_mapM_def = Define `
  (sum_mapM _ [] = INR []) /\
  (sum_mapM f (x::xs) = case (f x) of
                          | INL l => INL l
                          | INR r => sum_map (CONS r) (sum_mapM f xs))`;

(* For proving termination *)
val sum_mapM_cong = Q.store_thm("sum_mapM_cong",
  `!l1 l2 f f'. (l1 = l2) /\ (!x. MEM x l2 ==> (f x = f' x)) ==> (sum_mapM f l1 = sum_mapM f' l2)`,
  Induct \\ rw [sum_mapM_def] \\ rw [sum_mapM_def] \\ TOP_CASE_TAC \\ match_mp_tac f_equals2 \\ rw []);

(* DefnBase.add_cong sum_mapM_cong; *)
DefnBase.export_cong "sum_mapM_cong";

Theorem sum_mapM_INR:
 (!f v. sum_mapM f [] = INR v <=> v = []) ∧
 (!f x xs v. sum_mapM f (x::xs) = INR v <=> ?x' xs'. f x = INR x' /\ sum_mapM f xs = INR xs' /\ v = x'::xs')
Proof
 rw [sum_mapM_def] \\ CASE_TAC \\ simp [sum_map_INR] \\ metis_tac []
QED

Theorem length_sum_mapM:
 ∀l l' f. sum_mapM f l = INR l' ⇒ LENGTH l' = LENGTH l
Proof
 Induct >- rw [sum_mapM_def] \\ rw [sum_mapM_INR] \\ drule_first \\ simp []
QED

Theorem sum_mapM_append:
 !l1 l2 l3 f.
 sum_mapM f (l1 ++ l2) = INR l3 <=> ?l1' l2'. sum_mapM f l1 = INR l1' /\ sum_mapM f l2 = INR l2' ∧ l3 = l1' ++ l2'
Proof
 Induct >- rw [sum_mapM_def] \\ rw [sum_mapM_INR] \\ eq_tac \\ rw [PULL_EXISTS]
QED

Theorem sum_mapM_EL:
 ∀l l' f. sum_mapM f l = INR l' ⇔ (LENGTH l' = LENGTH l ∧ ∀i. i < LENGTH l ⇒ f (EL i l) = INR (EL i l'))
Proof
 Induct \\ rw [sum_mapM_INR] \\ eq_tac
 >- (rpt strip_tac \\ fs [] \\ Cases_on ‘i’ \\ fs [])
 \\ rpt strip_tac \\ Cases_on ‘l'’ \\ fs [] \\ rw []
    >- (first_x_assum (qspec_then ‘0’ mp_tac) \\ simp [])
    \\ first_x_assum (qspec_then ‘SUC i’ mp_tac) \\ simp []
QED

Theorem sum_mapM_MEM:
 ∀l l' f x. sum_mapM f l = INR l' ∧ MEM x l' ⇒ ∃y. f y = INR x ∧ MEM y l
Proof
 simp [sum_mapM_EL, MEM_EL] \\ metis_tac []
QED
     
Theorem sum_mapM_EVERY:
 !l l' f. sum_mapM f l = INR l' ==> EVERY (\e. ∃x. f e = INR x) l
Proof
 Induct \\ rw [sum_mapM_INR] \\ metis_tac []
QED

val sum_mapM__def = Define `
 (sum_mapM_ _ [] = INR ()) /\
 (sum_mapM_ f (x::xs) =
  case f x of
    INL l => INL l
  | INR r => sum_mapM_ f xs)`;

Theorem sum_mapM__INR:
 !f x xs v. sum_mapM_ f (x::xs) = INR v <=> ?v'. f x = INR v' /\ sum_mapM_ f xs = INR v
Proof
 rw [sum_mapM__def] \\ CASE_TAC
QED

Theorem sum_mapM__EVERY:
 !ps f. sum_mapM_ f ps = INR () ==> EVERY (\p. f p = INR ()) ps
Proof
 Induct \\ rw [sum_mapM__INR]
QED

(* TODO: Might be useful *)
(*val sum_filterM_def = Define `
 (sum_filterM P [] = return []) /\
 (sum_filterM P (x::xs) = do
  xs' <- sum_filterM P xs;
  return (if P x then xs' else x :: xs)
 od)`;*)

(* listTheory.MAP2 for sums *)
(*val sum_map2M_def = Define `
  (sum_map2M _ [] [] = INR []) /\
  (sum_map2M f (x::xs) (y::ys) = sum_bind (f x y) (\xy. sum_map (CONS xy) (sum_map2M f xs ys)))`;*)

(* Monomorphic liftM2 *)
val sum_liftM2_def = Define `
  sum_liftM2 f mx my = sum_bind mx (\x. sum_bind my (\y. INR (f x y)))`;

val sum_liftMM2_def = Define `
  sum_liftMM2 f mx my = sum_bind mx (\x. sum_bind my (\y. f x y))`;

(*
val sum_liftM3_def = Define `
  sum_liftM3 f mx my mz = sum_bind mx (\x. sum_bind my (\y. sum_bind mz (\z. INR (f x y z))))`;
*)

val sum_foldM_def = Define `
  (sum_foldM f z [] = INR z) /\
  (sum_foldM f z (x::xs) = sum_bind (f z x) (\fx. sum_foldM f fx xs))`;

Theorem sum_foldM_INR:
 (!acc f. sum_foldM f acc [] = INR acc) ∧
 (!x xs acc f v. sum_foldM f acc (x::xs) = INR v <=> ?v'. f acc x = INR v' /\ sum_foldM f v' xs = INR v)
Proof
 rw [sum_foldM_def, sum_bind_INR]
QED

Theorem sum_foldM_append:
 !xs ys i f. sum_foldM f i (xs ++ ys) = sum_bind (sum_foldM f i xs) (\i. sum_foldM f i ys)
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_def] \\ Cases_on `f i h` \\ rw [sum_bind_def]
QED

Theorem sum_foldM_SNOC:
 !xs x y f. sum_foldM f y (SNOC x xs) = sum_bind (sum_foldM f y xs) (combin$C f x)
Proof
 rw [SNOC_APPEND, sum_foldM_append, sum_foldM_def] \\
 Cases_on `sum_foldM f y xs` \\ rw [sum_bind_def, sum_bind_id, ETA_THM]
QED

Theorem sum_foldM_cong:
 ∀l l' b b' f f'.
 l = l' ∧ b = b' ∧ (∀x a. MEM x l' ⇒ f a x = f' a x) ⇒
 sum_foldM f b l = sum_foldM f' b' l'
Proof
 Induct >- simp [sum_foldM_def] \\ Cases_on ‘l'’ \\ rw [sum_foldM_def] \\
 f_equals_tac \\ rw [FUN_EQ_THM]
QED

DefnBase.export_cong "sum_foldM_cong";

(* Name from arithmeticTheory.FUNPOW *)
val sum_funpowM = Define `
  (sum_funpowM f 0 x = INR x) /\
  (sum_funpowM f (SUC n) x = sum_bind (f x) (\fx. sum_funpowM f n fx))`;

val sum_option_map_def = Define ‘
 (sum_option_map f (SOME x) = sum_map SOME (f x)) /\
 (sum_option_map f NONE = return NONE)’;

Theorem sum_option_map_INR:
 !f x x'.
 sum_option_map f x = INR x' <=> (x = NONE /\ x' = NONE) \/ (?y y'. x = SOME y /\ x' = SOME y' /\ f y = INR y')
Proof
 Cases_on ‘x’ \\ rw [sum_option_map_def, sum_map_INR] \\ metis_tac []
QED

Theorem sum_option_map_cong:
 !o1 o2 f1 f2. (o1 = o2) ∧ (∀x. o1 = SOME x ⇒ f1 x = f2 x) ⇒ sum_option_map f1 o1 = sum_option_map f2 o2
Proof
 Cases \\ simp [sum_option_map_def]
QED

DefnBase.export_cong "sum_option_map_cong";

(* Same as listTheory.EL but returns sum monad on out of bounds *)
val sum_EL_def = Define `
  (sum_EL _ [] = INL InvalidIndex) /\
  (sum_EL 0 (h::t) = INR h) /\
  (sum_EL (SUC i) (_::t) = sum_EL i t)`;

(* Cleanup? *)
val sum_EL_INR_EL = Q.store_thm("sum_EL_INR_EL",
 `!i l e. EL i l = e /\ i < LENGTH l ==> sum_EL i l = INR e`,
 Induct \\ rpt strip_tac
 >- (Cases_on `l` \\ fs [sum_EL_def])
 \\ Cases_on `i = LENGTH l` >- fs [] \\
    `i < LENGTH l` by DECIDE_TAC \\ Cases_on `l` >- fs [] \\
     fs [sum_EL_def]);

val sum_EL_INR_EL2 = Q.store_thm("sum_EL_INR_EL2",
 `!i l. i < LENGTH l ==> sum_EL i l = INR (EL i l)`,
 metis_tac [sum_EL_INR_EL]);

(* Same as sum_EL, but in reverse *)
val sum_revEL_def = Define `
  sum_revEL i vs = let l = LENGTH vs in
                     if i < l
                     then sum_EL (l - 1 - i) vs
                     else INL InvalidIndex`;

(** Some simpl thms about the sum type **)

Theorem sum_EL_INR:
 !l e i. sum_EL i l = INR e <=> e = EL i l /\ i < LENGTH l
Proof
 Induct >- rw [sum_EL_def] \\ Cases_on ‘i’ \\ rw [sum_EL_def] \\ metis_tac []
QED

Theorem sum_EL_EL:
 !i l. i < LENGTH l ==> sum_EL i l = INR (EL i l)
Proof
 rw [sum_EL_INR]
QED

val sum_EL_eq_EL = Q.store_thm("sum_EL_eq_EL",
 `!i l e. i < LENGTH l ==> (sum_EL i l = INR e <=> EL i l = e)`,
 Induct \\ rpt strip_tac \\ Cases_on `l` \\ fs [sum_EL_def]);

val sum_EL_LENGTH = Q.store_thm("sum_EL_LENGTH",
 `!xs x y. sum_EL (LENGTH xs) (xs ++ [x]) = INR x`,
 Induct \\ rw [sum_EL_def]);

(*
val sum_revEL_0 = Q.store_thm("sum_revEL_0",
 `!xs x y. sum_revEL 0 (xs ++ [x]) = INR y ==> x = y`,
 rw [sum_revEL_def, sum_EL_def] \\ metis_tac [sum_EL_LENGTH]);
*)

val sum_EL_LENGTH_INR_LENGTH = Q.store_thm("sum_EL_LENGTH_INR_LENGTH",
 `!n xs x y. n < LENGTH xs /\ sum_EL (LENGTH xs − n) (x::xs) = INR y ==>
             sum_EL (LENGTH xs − (n + 1)) xs = INR y`,
 rpt strip_tac \\ `LENGTH xs − (n + 1) = LENGTH xs − n - 1` by DECIDE_TAC \\
 pop_assum (fn th => REWRITE_TAC [th]) \\
 Cases_on `LENGTH xs − n` \\ fs [sum_EL_def]);

val sum_EL_APPEND_EQN = Q.store_thm("sum_EL_APPEND_EQN",
 `!l1 l2 n.
   sum_EL n (l1 ++ l2) = if n < LENGTH l1 then sum_EL n l1 else sum_EL (n − LENGTH l1) l2`,
 Induct \\ rw [] \\ Cases_on `n` \\ fs [sum_EL_def]);

val sum_revEL_LENGTH = Q.store_thm("sum_revEL_LENGTH",
 `!xs x. sum_revEL (LENGTH xs) (x::xs) = INR x`,
 Induct \\ rw [sum_revEL_def, sum_EL_def]);

val sum_revEL_APPEND_EQN = Q.store_thm("sum_revEL_APPEND_EQN",
 `!l2 l1 n.
   sum_revEL n (l1 ++ l2) =
   if n < LENGTH l2 then sum_revEL n l2 else sum_revEL (n − LENGTH l2) l1`,
 rw [sum_revEL_def] \\ fs [sum_EL_APPEND_EQN]);

(*
val sum_revEL_APPEND_single = Q.store_thm("sum_revEL_APPEND_single",
 `!n xs x. sum_revEL (SUC n) (xs ++ [x]) = sum_revEL n xs`,
 rw [sum_revEL_def, sum_EL_APPEND_EQN, ADD1]);
*)

val sum_revEL_0 = Q.store_thm("sum_revEL_0",
 `!xs x. sum_revEL 0 (xs ++ [x]) = INR x`,
 Induct \\ rw [sum_revEL_def, sum_EL_def, sum_EL_LENGTH]);

Theorem sum_revEL_INR:
 !l e i. sum_revEL i l = INR e <=> e = revEL i l /\ i < LENGTH l
Proof
 rw [sum_revEL_def, revEL_def, sum_EL_INR]
QED

Theorem sum_revEL_revEL:
 !l i. i < LENGTH l ==> sum_revEL i l = INR (revEL i l)
Proof
 rw [sum_revEL_INR]
QED

val sum_revEL_INR_LENGTH = Q.store_thm("sum_revEL_INR_LENGTH",
 `!n xs x y. n < LENGTH xs /\ sum_revEL n (x::xs) = INR y ==> sum_revEL n xs = INR y`,
 rw [sum_revEL_def] \\ metis_tac [sum_EL_LENGTH_INR_LENGTH]);

val MEM_sum_revEL = Q.store_thm("MEM_sum_revEL",
 `!l x. MEM x l <=> ∃n. n < LENGTH l /\ INR x = sum_revEL n l`,
 Induct \\ rw [] \\ eq_tac \\ rw []
 >- (qexists_tac `LENGTH l` \\ rw [sum_revEL_def, sum_EL_def])
 >- (qexists_tac `n` \\ `h::l = [h] ++ l` by simp [] \\
     pop_assum (fn th => rewrite_tac [th]) \\ rewrite_tac [sum_revEL_APPEND_EQN] \\
     simp [])
 \\ Cases_on `n = LENGTH l`
    >- (rveq \\ fs [sum_revEL_LENGTH])
    \\ `n < LENGTH l` by decide_tac \\ metis_tac [sum_revEL_INR_LENGTH]);

Theorem ISR_exists:
 !x. ISR x <=> ?x'. x = INR x'
Proof
 Cases \\ rw [sumTheory.ISR]
QED

(*Definition sum_everyM_def:
 (sum_everyM P [] = INR T) ∧
 (sum_everyM P (h::t) = do
  Ph <- P h;
  if Ph then sum_everyM P t else INR F
 od)
End*)

val _ = export_theory ();
