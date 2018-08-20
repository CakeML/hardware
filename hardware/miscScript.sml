(* Must not depend on preamble! *)
open HolKernel Parse boolLib bossLib BasicProvers;

open bitstringTheory rich_listTheory wordsTheory;

val _ = new_theory "misc";

val _ = ParseExtras.tight_equality ();

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

val MEM_disj_impl = Q.store_thm("MEM_disj_impl",
 `!A B C. (!x. A x \/ B x ==> C x) <=> (!x. A x ==> C x) /\ (!x. B x ==> C x)`,
 metis_tac []);

(* Defined in the standard library somewhere? *)
val elems_not_in_def = Define `
 elems_not_in l1 l2 = !e. MEM e l1 ==> ~MEM e l2`;

val elems_not_in_APPEND = Q.store_thm("elems_not_in_APPEND",
 `!l1 l2 l3. elems_not_in l1 (l2 ++ l3) = (elems_not_in l1 l2 /\ elems_not_in l1 l3)`,
 rpt gen_tac \\ EQ_TAC \\ rw [elems_not_in_def]);

val elems_not_in_FLAT = Q.store_thm("elems_not_in_FLAT",
 `!ll l. elems_not_in l (FLAT ll) = EVERY (elems_not_in l) ll`,
 Induct >- fs [elems_not_in_def] \\ fs [elems_not_in_APPEND]);

(* TODO: This is from miscScript in cakeml, move to HOL *)
val MAP_DROP = Q.store_thm("MAP_DROP",
  `!l i f. MAP f (DROP i l) = DROP i (MAP f l)`,
  Induct \\ rw [] \\ Cases_on `i` \\ rw []);

(** bitstringTheory extra **)

val v2n_w2v = Q.store_thm("v2n_w2v",
 `!w. v2n (w2v w) = w2n w`,
 gen_tac \\ bitstringLib.Cases_on_v2w `w` \\ fs [w2v_v2w, w2n_v2w, bitTheory.MOD_2EXP_def, v2n_lt]);

val w2v_not_empty = Q.store_thm("w2v_not_empty",
 `!w. w2v w <> []`,
 gen_tac \\ `!(l:bitstring). 0 < LENGTH l ==> l <> []` by (Cases \\ rw []) \\
 pop_assum match_mp_tac \\ rw [DIMINDEX_GT_0]);

(** Automatic rewrites **)

val DIMINDEX_NEQ_0 = Q.store_thm("DIMINDEX_NEQ_0[simp]",
 `dimindex (:'a) <> 0`,
 assume_tac DIMINDEX_GT_0 \\ DECIDE_TAC);

val _ = export_theory ();
