open hardwarePreamble;

open balanced_mapTheory comparisonTheory;

val _ = new_theory "balanced_mapExtra";

Theorem string_cmp_sym:
 !x. string_cmp x x = Equal
Proof
 metis_tac [good_cmp_def, string_cmp_good]
QED

Theorem string_cmp_Greater_trans:
 !a b c. string_cmp a b = Greater /\ string_cmp b c = Greater ==> string_cmp a c = Greater
Proof
 metis_tac [string_cmp_good, good_cmp_def]
QED

Theorem string_cmp_Less_trans:
 !a b c. string_cmp a b = Less /\ string_cmp b c = Less ==> string_cmp a c = Less
Proof
 metis_tac [string_cmp_good, good_cmp_def]
QED

Theorem lookup_key_Greater:
 !t k. key_ordered string_cmp k t Greater ==> lookup string_cmp k t = NONE
Proof
 Induct \\ rw [lookup_def, key_ordered_def]
QED

Theorem lookup_key_Greater_x2:
 !t k1 k2.
 string_cmp k1 k2 = Greater /\ key_ordered string_cmp k2 t Greater ==>
 lookup string_cmp k1 t = NONE
Proof
 Induct \\ rw [lookup_def, key_ordered_def] \\ imp_res_tac string_cmp_Greater_trans \\ simp [] \\ metis_tac []
QED

Theorem lookup_key_Less:
 !t k. key_ordered string_cmp k t Less ==> lookup string_cmp k t = NONE
Proof
 Induct \\ rw [lookup_def, key_ordered_def]
QED

Theorem lookup_key_Less_x2:
 !t k1 k2.
 string_cmp k1 k2 = Less /\ key_ordered string_cmp k2 t Less ==>
 lookup string_cmp k1 t = NONE
Proof
 Induct \\ rw [lookup_def, key_ordered_def] \\ imp_res_tac string_cmp_Less_trans \\ simp [] \\ metis_tac []
QED

Theorem string_cmp_Greater_not_eq:
 !s1 s2. string_cmp s1 s2 = Greater ==> s1 <> s2
Proof
 metis_tac [string_cmp_antisym, cmp_thms]
QED

Theorem string_cmp_Less_not_eq:
 !s1 s2. string_cmp s1 s2 = Less ==> s1 <> s2
Proof
 metis_tac [string_cmp_antisym, cmp_thms]
QED

Theorem lookup_Bin_NONE:
 !n k v t t' var.
 invariant string_cmp (Bin n k v t t') /\ lookup string_cmp var (Bin n k v t t') = NONE ==>
 lookup string_cmp var t = NONE /\ k <> var /\ lookup string_cmp var t' = NONE
Proof
 simp [invariant_def, lookup_def] \\ rpt gen_tac \\ TOP_CASE_TAC \\
 metis_tac [lookup_key_Greater_x2, lookup_key_Less_x2, string_cmp_Greater_not_eq, string_cmp_Less_not_eq]
QED

Theorem foldrWithKey_nothing:
 !atree f st.
 invariant string_cmp atree /\ (!k. lookup string_cmp k atree = NONE) ==> foldrWithKey f st atree = st
Proof
 Induct \\ rw [foldrWithKey_def] \\ metis_tac [lookup_def, lookup_Bin_NONE]
QED

val _ = export_theory ();
