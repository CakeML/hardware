open hardwarePreamble;

(* Could maybe be renamed to "verilogSum" or similar, because e.g. error_def is specific to Verilog. *)

val _ = new_theory "sumExtra";

(* Error type, should probably have a lot more cases *)
val error_def = Datatype `
 error = UnknownVariable | TypeError | InvalidIndex | NotImplemented | InvalidArgument`;

val sum_bind_def = Define `
  (sum_bind (INL l) _ = INL l) /\
  (sum_bind (INR r) f = f r)`;

(* There's also a "map" in sumTheory, called ++ I think, but it takes two functions *)
val sum_map_def = Define `
  (sum_map f (INR r) = INR (f r)) /\
  (sum_map _ (INL v) = INL v)`;

val sum_for_def = Define `
  sum_for s f = sum_map f s`;

(* imp_res_tac thm for the above three definitions *)
val sum_bind_INR = Q.store_thm("sum_bind_INR",
 `!s f v. sum_bind s f = INR v ==> ?v'. s = INR v'`,
 Cases \\ rw [sum_bind_def]);

val sum_map_INR = Q.store_thm("sum_map_INR",
 `!s f v. sum_map f s = INR v ==> ?v'. s = INR v'`,
 Cases \\ rw [sum_map_def]);

val sum_for_INR = Q.store_thm("sum_for_INR",
 `!s f v. sum_for s f = INR v ==> ?v'. s = INR v'`,
 metis_tac [sum_for_def, sum_map_INR]);

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

(* Name from arithmeticTheory.FUNPOW *)
val sum_funpowM = Define `
  (sum_funpowM f 0 x = INR x) /\
  (sum_funpowM f (SUC n) x = sum_bind (f x) (\fx. sum_funpowM f n fx))`;

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

val sum_EL_EL = Q.store_thm("sum_EL_EL",
 `!i l. i < LENGTH l ==> sum_EL i l = INR (EL i l)`,
 Induct \\ Cases_on `l` \\ fs [sum_EL_def]);

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

val _ = export_theory ();
