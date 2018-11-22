open hardwarePreamble;

open dep_rewrite;

open arithmeticTheory combinTheory fcpTheory wordsTheory;

val _ = new_theory "wordsExtra";

val w2w_fcp_index_id = Q.store_thm("w2w_fcp_index_id",
 `!i (w:'a word).
   i < dimindex (:'a) /\ i < dimindex (:'b) ==>
   (w2w w):'b word ' i = w ' i`,
 rw [w2w]);

val w2w_fcp_index_shrink = Q.store_thm("w2w_fcp_index_shrink",
 `!i (w:'a word).
   i < dimindex (:'a) /\ i < dimindex (:'b) /\ i < dimindex (:'c) ==>
   (w2w w):'b word ' i = (w2w w):'c word ' i`,
 rw [w2w]);

val w2w_fcp_index_shrink2 = Q.store_thm("w2w_fcp_index_shrink2",
 `!i w.
   dimindex (:'b) <= dimindex (:'a) /\ i < dimindex (:'b) ==>
   (w2w w):'a word ' i = (w2w w):'b word ' i`,
 rw [w2w]);

val word_bits_fcp_index_id = Q.store_thm("word_bits_fcp_index_id",
 `!h l (w:'a word) i.
   i < dimindex (:'a) /\ l <= i /\ i <= h ==>
   (h -- l) w ' (i − l) = w ' i`,
 rw [word_bits_def, FCP_BETA]);

val word_extract_fcp_index_id = Q.store_thm("word_extract_fcp_index_id",
 `!h l (w:'a word) i.
   i < dimindex (:'a) /\
   dimindex (:'b) <= dimindex (:'a) /\
   dimindex (:'b) = h - l + 1 /\
   l <= i /\ i <= h
   ==> ((h >< l) w):'b word ' (i − l) = w ' i`,
 rw [word_extract_def, w2w_fcp_index_id, word_bits_fcp_index_id]);

val word_concat_index = Q.store_thm("word_concat_index",
 `!i v:'a word w:'b word.
   FINITE (UNIV:'a set) /\ FINITE (UNIV:'b set) /\
   dimindex(:'c) = dimindex(:'a) + dimindex(:'b) /\ i < dimindex(:'b) ==>
   (v @@ w):'c word ' i = w ' i`,
 rpt strip_tac \\ simp [word_concat_def] \\
 DEP_REWRITE_TAC [w2w_fcp_index_id] \\ simp [fcpTheory.index_sum] \\
 DEP_REWRITE_TAC [word_join_index] \\ simp [fcpTheory.index_sum]);

val word_extract_concat_right = Q.store_thm("word_extract_concat_right",
 `!v:'a word w:'b word a b.
   FINITE (UNIV:'a set) /\ FINITE (UNIV:'b set) /\
   a < dimindex(:'b) /\ b < dimindex(:'b) /\
   dimindex(:'c) = dimindex(:'a) + dimindex(:'b) /\
   dimindex(:'d) = a - b + 1 ==>
   (a >< b) ((v @@ w):'c word) = ((a >< b) w):'d word`,
 rpt strip_tac \\ rewrite_tac [GSYM WORD_EQ] \\ rpt strip_tac \\
 simp [word_bit_def, word_extract_def, w2w_fcp_index_id, word_bits_def,
       fcpTheory.FCP_BETA, word_concat_index]);

val word_extract_concat_right0 = Q.store_thm("word_extract_concat_right0",
 `!v:'a word w:'b word a.
   FINITE (UNIV:'a set) /\ FINITE (UNIV:'b set) /\
   dimindex(:'a) + dimindex(:'b) <= dimindex(:'c) /\
   a = dimindex(:'b) - 1 ==>
   (a >< 0) ((v @@ w):'c word) = w`,
 rw [EXTRACT_CONCAT]);

val word_extract_concat_left = Q.store_thm("word_extract_concat_left",
 `!v:'a word w:'b word a b.
   FINITE (UNIV:'a set) /\ FINITE (UNIV:'b set) /\
   dimindex(:'a) + dimindex(:'b) <= dimindex(:'c) /\
   a = dimindex(:'a) + dimindex(:'b) - 1 /\ b = dimindex(:'b) ==>
   (a >< b) ((v @@ w):'c word) = v`,
 rw [EXTRACT_CONCAT]);

(* See also WORD_EXTRACT_ID *)
val word_extract_id = Q.store_thm("word_extract_id",
 `!(w:'a word) h. h = dimindex (:'a) - 1 ==> (h >< 0) w = w`,
 simp [GSYM WORD_w2w_EXTRACT]);

val bit_field_insert_overwrite = Q.store_thm("bit_field_insert_overwrite",
 `!(wnew:'a word) (wold:'a word) h.
   h = dimindex (:'a) - 1 ==> bit_field_insert h 0 wnew wold = wnew`,
 rw [bit_field_insert_def, word_modify_def, CART_EQ, FCP_BETA]);

val bit_field_insert_nest = Q.store_thm("bit_field_insert_nest",
 `!i0 i1 i2 i3 (f : 'e word -> 'a word) addr (w:'a word).
   i0 <= i1 /\ i2 = i1 + 1 /\ i2 <= i3 /\

   dimindex (:'b) = i3 - i2 + 1 /\
   dimindex (:'c) = i1 - i0 + 1 /\
   dimindex (:'d) = i3 - i0 + 1 /\

   dimindex (:'b) <= dimindex (:'a) /\
   dimindex (:'c) <= dimindex (:'a) /\
   dimindex (:'d) <= dimindex (:'a)
   ==>
   bit_field_insert i3 i2
   (((i3 >< i2) w):'b word)
   ((addr =+ bit_field_insert i1 i0 (((i1 >< i0) w):'c word) (f addr)) f addr)
   =
   bit_field_insert i3 i0 (((i3 >< i0) w):'d word) (f addr)`,
 rpt strip_tac \\ simp [UPDATE_def] \\ simp [bit_field_insert_def, word_modify_def, CART_EQ] \\
 rw [FCP_BETA] \\ fs [word_extract_fcp_index_id]);

val v2w_single = Q.store_thm("v2w_single",
 `!b. v2w [b] = if b then (1w:word1) else 0w`,
 Cases \\ EVAL_TAC);

val v2w_single_0w = Q.store_thm("v2w_single_0w",
 `!b. v2w [b] = (0w:word1) <=> ~b`,
 rw [v2w_single]);

val v2w_single_not_0w = Q.store_thm("v2w_single_not_0w",
 `!b. v2w [b] <> (0w:word1) <=> b`,
 rw [v2w_single]);

val v2w_single_1w = Q.store_thm("v2w_single_1w",
 `!b. v2w [b] = (1w:word1) <=> b`,
 rw [v2w_single]);

val v2w_single_not_1w = Q.store_thm("v2w_single_not_1w",
 `!b. v2w [b] <> (1w:word1) <=> ~b`,
 rw [v2w_single]);

val _ = export_theory ();
