(* Must not depend on preamble! *)
open HolKernel Parse boolLib bossLib BasicProvers;

open bitstringTheory listTheory rich_listTheory wordsTheory;

val _ = new_theory "hardwareMisc";

val f_equals1 = Q.store_thm("f_equals1",
  `!(f : 'a -> 'b) x x'. (x = x') ==> (f x = f x')`,
  rw []);

val f_equals2 = Q.store_thm("f_equals2",
  `!(f : 'a -> 'b -> 'c) x x' y y'. (x = x') /\ (y = y') ==> (f x y = f x' y')`,
  rw []);

val MAP_inj = Q.store_thm("MAP_inj",
 `!l1 l2 f.
   (!x y. f x = f y ==> x = y) ==>
   (MAP f l1 = MAP f l2 <=> l1 = l2)`,
 Induct \\ rw [] \\ EQ_TAC \\ rw [] \\ TRY (Cases_on `l2`) \\ fs [] \\ metis_tac []);

(* TODO: Rename *)
val MEM_disj_impl = Q.store_thm("MEM_disj_impl",
 `!A B C. (!x. A x \/ B x ==> C x) <=> (!x. A x ==> C x) /\ (!x. B x ==> C x)`,
 metis_tac []);

(** listTheory extra **)

Definition revEL_def:
 revEL n l = EL (LENGTH l - 1 - n) l
End

Definition revLUPDATE_def:
 revLUPDATE e n l = LUPDATE e (LENGTH l - 1 - n) l
End

Theorem length_revLUPDATE[simp]:
 !e n l. LENGTH (revLUPDATE e n l) = LENGTH l
Proof
 rw [revLUPDATE_def]
QED

Theorem IMP_EVERY_revLUPDATE:
 !xs h i P. P h /\ EVERY P xs ==> EVERY P (revLUPDATE h i xs)
Proof
 rw [revLUPDATE_def, IMP_EVERY_LUPDATE]
QED

Theorem revEL_GENLIST:
 ∀f n x. x < n ⇒ revEL x (GENLIST f n) = f (n - 1 - x)
Proof
 simp [revEL_def]
QED

Theorem dropWhile_MAP:
 !l f P. dropWhile P (MAP f l) = MAP f (dropWhile (P o f) l)
Proof
 Induct \\ rw []
QED

(* Bad rewrite, lhs in rhs *)
Theorem dropWhile_LASTN:
 !l x. dropWhile ($= x) l = LASTN (LENGTH (dropWhile ($= x) l)) l
Proof
 Induct
 >- rw [rich_listTheory.LASTN_def]
 \\ rw [dropWhile_def, rich_listTheory.LASTN_LENGTH_ID, rich_listTheory.LASTN_CONS, LENGTH_dropWhile_LESS_EQ]
QED

(** bitTheory extra **)

Theorem log2_twoexp_sub1:
 !n. n ≠ 0 ==> LOG2 (2 ** n − 1) = n - 1
Proof
 rpt strip_tac \\ match_mp_tac bitTheory.LOG2_UNIQUE \\ Cases_on ‘n’ \\ fs [arithmeticTheory.ADD1, arithmeticTheory.EXP_ADD]
QED

(** bitstringTheory extra **)

Triviality fixwidth_0:
 ∀l. fixwidth 0 l = []
Proof
 rw [fixwidth_def, rich_listTheory.DROP_LENGTH_NIL]
QED

Theorem fixwidth_snoc:
 ∀n xs x.
 fixwidth n (SNOC x xs) = if n = 0 then [] else SNOC x (fixwidth (n - 1) xs)
Proof
 Cases \\ rw [fixwidth_0, arithmeticTheory.ADD1] \\ rw [fixwidth_def] \\ fs []
 >- simp [zero_extend_def, PAD_LEFT]
 \\ simp [rich_listTheory.DROP_APPEND] \\ ‘LENGTH xs − n' − LENGTH xs = 0’ by decide_tac \\ simp []
QED

Theorem fixwidth_append:
 ∀ys xs n.
 fixwidth n (xs ++ ys) = if n ≤ LENGTH ys then fixwidth n ys else fixwidth (n - LENGTH ys) xs ++ ys
Proof
 Induct >- (Cases \\ rw [fixwidth_def, rich_listTheory.DROP_LENGTH_NIL] \\ fs []) \\ rw []
 >- metis_tac [rich_listTheory.CONS_APPEND]
 >- (‘n - LENGTH ys = 1’ by decide_tac \\ simp [fixwidth_def, rich_listTheory.DROP_LENGTH_APPEND])
 >- simp [GSYM SNOC_APPEND, fixwidth_snoc, arithmeticTheory.ADD1]
QED

Triviality length_boolify:
 !l a. LENGTH (boolify a l) = LENGTH a + LENGTH l
Proof
 Induct \\ rw [boolify_def]
QED

Theorem length_n2v:
 !n. LENGTH (n2v n) = if n = 0 then 1 else SUC (LOG 2 n)
Proof
 gen_tac \\ simp [n2v_def, numposrepTheory.num_to_bin_list_def, length_boolify, numposrepTheory.LENGTH_n2l]
QED

Theorem v2n_w2v:
 !w. v2n (w2v w) = w2n w
Proof
 gen_tac \\ bitstringLib.Cases_on_v2w `w` \\ simp [w2v_v2w, w2n_v2w, bitTheory.MOD_2EXP_def, v2n_lt]
QED

(* Should maybe not be moved to main lib? *)
Theorem w2v_not_empty:
 !w. w2v w <> []
Proof
 gen_tac \\ `!(l:bitstring). 0 < LENGTH l ==> l <> []` by (Cases \\ rw []) \\
 pop_assum match_mp_tac \\ rw [DIMINDEX_GT_0]
QED

Theorem zero_extend_id:
 ∀l. zero_extend (LENGTH l) l = l
Proof
 rw [zero_extend_def, PAD_LEFT]
QED

Theorem v2n_zero_extend:
 !n v. v2n (zero_extend n v) = v2n v
Proof
 rw [bitstringTheory.v2n_def, numposrepTheory.num_from_bin_list_def, bitstringTheory.zero_extend_def, PAD_LEFT, bitstringTheory.bitify_reverse_map, REVERSE_APPEND, MAP_GENLIST, REVERSE_GENLIST, numposrepTheory.l2n_APPEND, numposrepTheory.l2n_eq_0, EVERY_GENLIST]
QED

Triviality bitify_lt:
 !v. EVERY ($> 2) (bitify [] v)
Proof
 simp [bitstringTheory.bitify_reverse_map, rich_listTheory.EVERY_REVERSE, EVERY_MAP] \\ rw [EVERY_MEM] \\ rw []
QED

Theorem n2v_v2n:
 !v. n2v (v2n v) = (if EVERY ($= F) v then [F] else dropWhile ($= F) v)
Proof
 gen_tac \\ simp [bitstringTheory.n2v_def, bitstringTheory.v2n_def, numposrepTheory.num_to_bin_list_def, numposrepTheory.num_from_bin_list_def] \\
 dep_rewrite.DEP_REWRITE_TAC [numposrepTheory.n2l_l2n] \\ conj_tac >- simp [bitify_lt] \\
 simp [bitstringTheory.bitify_reverse_map, bitstringTheory.boolify_reverse_map, numposrepTheory.l2n_eq_0] \\
 simp [rich_listTheory.EVERY_REVERSE, EVERY_MAP] \\
 ‘!b. (0 = (if b then 1 else 0) MOD 2) = ~b’ by rw [] \\ simp [] \\ pop_assum kall_tac \\ reverse (rw [])
 >- (dep_rewrite.DEP_REWRITE_TAC [numposrepTheory.LOG_l2n_dropWhile] \\ 
    conj_tac >- (simp [rich_listTheory.EXISTS_REVERSE, EXISTS_MAP, rich_listTheory.EVERY_REVERSE, EVERY_MAP] \\
                 fs [EVERY_MEM, EXISTS_MEM] \\ rw [] \\ goal_assum drule \\ simp []) \\
    dep_rewrite.DEP_REWRITE_TAC [arithmeticTheory.SUC_PRE |> EQ_IMP_RULE |> fst] \\
    conj_tac >- (simp [GSYM rich_listTheory.MAP_REVERSE, GSYM MAP_TAKE, MAP_MAP_o, rich_listTheory.TAKE_REVERSE, dropWhile_MAP, combinTheory.o_DEF] \\ simp [DECIDE “!x. 0 < x <=> x <> 0”, dropWhile_eq_nil] \\ fs [EVERY_MEM, EXISTS_MEM] \\ goal_assum drule \\ rw []) \\
    simp [] \\ dep_rewrite.DEP_REWRITE_TAC [rich_listTheory.TAKE_REVERSE] \\
    conj_tac >- simp [dropWhile_MAP, LENGTH_dropWhile_LESS_EQ] \\
    simp [rich_listTheory.MAP_REVERSE, dropWhile_MAP] \\
    dep_rewrite.DEP_REWRITE_TAC [GSYM rich_listTheory.LASTN_MAP] \\
    conj_tac >- simp [LENGTH_dropWhile_LESS_EQ] \\
    simp [MAP_MAP_o, combinTheory.o_DEF] \\ simp [Once dropWhile_LASTN] \\
    ‘!b. (if b then 1 else 0) ≠ 0 <=> b’ by rw [] \\
    ‘!b. (0 = if b then 1 else 0) <=> ~b’ by rw [] \\
    simp [] \\ rpt (AP_THM_TAC ORELSE AP_TERM_TAC) \\ rw [FUN_EQ_THM])
 \\ full_simp_tac (bool_ss) [dropWhile_eq_nil, EVERY_NOT_EXISTS, combinTheory.o_DEF]
QED

Theorem v2n_snoc:
 ∀x xs. v2n (SNOC x xs) = v2n xs * 2 + (if x then 1 else 0)
Proof
 rw [v2n_def, bitify_reverse_map, MAP_SNOC, REVERSE_SNOC, numposrepTheory.num_from_bin_list_def, numposrepTheory.l2n_def]
QED

Theorem v2n_append:
 ∀ys xs. v2n (xs ++ ys) = v2n xs * 2**(LENGTH ys) + v2n ys
Proof
 listLib.SNOC_INDUCT_TAC \\ rw [EVAL “v2n []”] \\
 ‘xs ⧺ SNOC x ys = SNOC x (xs ⧺ ys)’ by fs [] \\ pop_assum (once_rewrite_tac o single) \\
 simp [v2n_snoc, arithmeticTheory.EXP] \\ decide_tac
QED

Theorem fixwidth_F:
 ∀n. fixwidth n [F] = GENLIST (K F) n
Proof
 rw [fixwidth_def]
 >- (rw [zero_extend_def, PAD_LEFT] \\ ‘n = SUC (n - 1)’ by decide_tac \\
    pop_assum (once_rewrite_tac o single) \\ simp [GENLIST])
 \\ ‘n = 0 ∨ n = 1’ by decide_tac \\ simp []
QED

(** Automatic rewrites **)

val DIMWORD_GT_0 = Q.store_thm("DIMWORD_GT_0",
 `0 < dimword (:α)`,
 simp [dimword_def]);

val DIMINDEX_NEQ_0 = Q.store_thm("DIMINDEX_NEQ_0[simp]",
 `dimindex (:'a) <> 0`,
 assume_tac DIMINDEX_GT_0 \\ DECIDE_TAC);

val _ = export_theory ();
