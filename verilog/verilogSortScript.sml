open hardwarePreamble;

open indexedListsTheory sptreeTheory;

open balanced_mapTheory topological_sortTheory;

open sumExtraTheory verilogTheory verilogWriteCheckerTheory;

val _ = new_theory "verilogSort";

Definition writes_to_size_def:
 (writes_to_size (INL (_, p)) = vprog_size p) ∧
 (writes_to_size (INR (INL (_, ps))) = vprog1_size ps) ∧
 (writes_to_size (INR (INR (_, p))) = vprog3_size p)
End

Definition writes_to_def:
 (writes_to var Skip ⇔ F) ∧
 (writes_to var (Seq p1 p2) ⇔ writes_to var p1 ∨ writes_to var p2) ∧
 (writes_to var (IfElse _ p1 p2) ⇔ writes_to var p1 ∨ writes_to var p2) ∧
 (writes_to var (Case _ _ cs ds) ⇔ writes_to_Case var cs ∨ writes_to_opt var ds) ∧
 (writes_to var (BlockingAssign lhs _) ⇔ var = evwrites lhs) ∧
 (writes_to var (NonBlockingAssign lhs _) ⇔ F) ∧

 (writes_to_Case var [] ⇔ F) ∧
 (writes_to_Case var ((_, p) :: xs) ⇔ writes_to var p ∨ writes_to_Case var xs) ∧

 (writes_to_opt var NONE ⇔ F) ∧
 (writes_to_opt var (SOME p) ⇔ writes_to var p)
Termination
 WF_REL_TAC `measure writes_to_size` \\ rw [writes_to_size_def, vprog_size_def]
End

Theorem writes_to_correct:
 (∀var p. writes_to var p ⇔ MEM var (vwrites p)) ∧
 (∀var ps. writes_to_Case var ps ⇔ MEM var (FLAT (MAP vwrites (MAP SND ps)))) ∧
 (∀var ps. OPTION_ALL (λp. writes_to var p ⇔ MEM var (vwrites p)) ps)
Proof
 ho_match_mp_tac writes_to_ind \\ simp [writes_to_def, vwrites_def] \\ rpt strip_tac \\
 CASE_TAC \\ fs [writes_to_def, MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]
QED

Definition compute_writers_def:
 compute_writers var idx_to_proc = map (K ()) (filter_v (writes_to var) idx_to_proc)
End

(* Called mapWithKey in Data.Map in Haskell *)
Definition mapi_def:
 (mapi _ Tip = Tip) ∧
 (mapi f (Bin sx kx x l r) = Bin sx kx (f kx x) (mapi f l) (mapi f r))
End

Theorem lookup_mapi:
 !t.
 good_cmp cmp ∧ (!x y. cmp x y = Equal <=> x = y) ∧ invariant cmp t ⇒
 lookup cmp k (mapi f t) = OPTION_MAP (f k) (lookup cmp k t)
Proof
 Induct \\ rw [mapi_def, lookup_def] \\ TOP_CASE_TAC \\ gs [invariant_def]
QED

val lookup_mapi_string_cmp =
 lookup_mapi
 |> REWRITE_RULE [GSYM AND_IMP_INTRO] 
 |> flip MATCH_MP comparisonTheory.string_cmp_good
 |> flip MATCH_MP comparisonTheory.string_cmp_antisym;

(*Theorem lookup_map:
 good_cmp cmp ∧ invariant cmp t ⇒
 lookup cmp k (map f t) = OPTION_MAP f (lookup cmp k t)
Proof
 rw [lookup_thm, map_thm, finite_mapTheory.FLOOKUP_o_f] \\ CASE_TAC \\ simp []
QED*)

Definition option_get_def:
 (option_get d NONE = d) ∧
 (option_get d (SOME x) = x)
End

Theorem option_get_alt:
 ∀d opt.
 option_get d opt = case opt of
                      NONE => d
                    | SOME x => x
Proof
 rpt gen_tac \\ TOP_CASE_TAC \\ simp [option_get_def]
QED

Definition read_deps_exp_def:
 read_deps_exp var_to_writers e =
 FOLDR (λr acc. union acc (option_get LN (lookup string_cmp r var_to_writers))) LN (evreads e)
End

Triviality read_deps_exp_correct_lem:
 ∀writes idx var_to_writers.
 IS_SOME (lookup idx (FOLDR (λr acc. union acc (option_get LN (lookup string_cmp r var_to_writers))) LN writes)) ⇔
 ∃var writers. MEM var writes ∧ lookup string_cmp var var_to_writers = SOME writers ∧ IS_SOME (lookup idx writers)
Proof
 Induct >- simp [sptreeTheory.lookup_def] \\ rw [sptreeTheory.lookup_union] \\ TOP_CASE_TAC
 >- (simp [option_get_alt] \\ TOP_CASE_TAC \\ rw [sptreeTheory.lookup_def] \\
     metis_tac [optionTheory.IS_SOME_DEF, optionTheory.option_CLAUSES]) \\
 metis_tac [optionTheory.IS_SOME_DEF]
QED

Theorem read_deps_exp_correct:
 ∀e idx var_to_writers.
 IS_SOME (lookup idx (read_deps_exp var_to_writers e)) ⇔
 ∃var writers. MEM var (evreads e) ∧ lookup string_cmp var var_to_writers = SOME writers ∧ IS_SOME (lookup idx writers)
Proof
 simp [read_deps_exp_def, read_deps_exp_correct_lem]
QED

Definition read_deps_index_def:
 (read_deps_index var_to_writers (Indexing _ _ i) = read_deps_exp var_to_writers i) ∧
 (read_deps_index var_to_writers _ = LN)
End

Theorem read_deps_index_correct:
 ∀i idx var_to_writers.
 IS_SOME (lookup idx (read_deps_index var_to_writers i)) ⇔
 ∃var writers. MEM var (evreads_index i) ∧ lookup string_cmp var var_to_writers = SOME writers ∧ IS_SOME (lookup idx writers)
Proof
 Cases \\ simp [read_deps_index_def, evreads_index_def, read_deps_exp_correct, sptreeTheory.lookup_def]
QED

Definition read_deps_size_def:
 (read_deps_size (INL (_, p)) = vprog_size p) ∧
 (read_deps_size (INR (INL (_, ps))) = vprog1_size ps) ∧
 (read_deps_size (INR (INR (_, ps))) = vprog3_size ps)
End

Definition read_deps_def:
 (read_deps (var_to_writers : (string, num_set) balanced_map) Skip = LN) ∧
 (read_deps var_to_writers (Seq p1 p2) =
  union (read_deps var_to_writers p1) (read_deps var_to_writers p2)) ∧
 (read_deps var_to_writers (IfElse c p1 p2) =
  union (read_deps_exp var_to_writers c) 
        (union (read_deps var_to_writers p1) (read_deps var_to_writers p2))) ∧
 (read_deps var_to_writers (Case _ c ps d) =
  union (read_deps_exp var_to_writers c)
        (union (read_deps_Case var_to_writers ps) (read_deps_opt var_to_writers d))) ∧
 (read_deps var_to_writers (BlockingAssign lhs NONE) = read_deps_index var_to_writers lhs) ∧
 (read_deps var_to_writers (BlockingAssign lhs (SOME e)) = union (read_deps_index var_to_writers lhs)
                                                                 (read_deps_exp var_to_writers e)) ∧
 (read_deps var_to_writers (NonBlockingAssign lhs NONE) = read_deps_index var_to_writers lhs) ∧
 (read_deps var_to_writers (NonBlockingAssign lhs (SOME e)) = union (read_deps_index var_to_writers lhs)
                                                                    (read_deps_exp var_to_writers e)) ∧

 (read_deps_Case var_to_writers [] = LN) ∧
 (read_deps_Case var_to_writers ((e,p)::ps) =
  union (read_deps_exp var_to_writers e) 
        (union (read_deps var_to_writers p) (read_deps_Case var_to_writers ps))) ∧
 
 (read_deps_opt var_to_writers NONE = LN) ∧
 (read_deps_opt var_to_writers (SOME p) = read_deps var_to_writers p)
Termination
 WF_REL_TAC `measure read_deps_size` \\ rw [read_deps_size_def, vprog_size_def]
End

Theorem read_deps_correct:
 (∀var_to_writers p idx.
   IS_SOME (lookup idx (read_deps var_to_writers p)) ⇔
   ∃r writers. MEM r (vreads p) ∧ lookup string_cmp r var_to_writers = SOME writers ∧ IS_SOME (lookup idx writers))
 ∧
 (∀var_to_writers ps idx.
   IS_SOME (lookup idx (read_deps_Case var_to_writers ps)) ⇔
   ∃r writers. MEM r (FLAT (MAP (λ(cc,cb). evreads cc ⧺ vreads cb) ps)) ∧ lookup string_cmp r var_to_writers = SOME writers ∧ IS_SOME (lookup idx writers))
 ∧
 (∀var_to_writers ps idx.
   IS_SOME (lookup idx (read_deps_opt var_to_writers ps)) ⇔
   case ps of
     NONE => F
   | SOME p => ∃r writers. MEM r (vreads p) ∧ lookup string_cmp r var_to_writers = SOME writers ∧ IS_SOME (lookup idx writers))
Proof
 ho_match_mp_tac read_deps_ind \\ rw [read_deps_def, vreads_def] \\
 simp [sptreeTheory.lookup_def, sptreeTheory.lookup_union] \\ every_case_tac \\ fs [] \\
 metis_tac [optionTheory.IS_SOME_DEF, optionTheory.option_CLAUSES, read_deps_exp_correct, read_deps_index_correct]
QED

Definition sort_by_deps_def:
 sort_by_deps ps = let
  idx_to_proc = fromList ps;
  allwrites = compute_writes_bw ps;
  var_to_writers = mapi (λvar _. compute_writers var idx_to_proc) allwrites;
  deps = MAPi (λidx proc. (idx, read_deps var_to_writers proc)) ps;
  deps = top_sort deps in
 case deps of
   NONE => INL CycleError
 | SOME deps => INR $ MAP (λidx. THE (lookup idx idx_to_proc)) deps
End

Triviality MAPi_ignore_second:
 MAPi (λi _. i) l = GENLIST I (LENGTH l)
Proof
 simp [MAPi_GENLIST, GENLIST_FUN_EQ]
QED

Triviality PERM_GENLIST_I_EVERY_lt:
 ∀n l. PERM l (GENLIST I n) ⇒ EVERY (λx. x < n) l ∧ LENGTH l = n
Proof
 rpt strip_tac' \\
 drule_strip sortingTheory.PERM_LENGTH \\
 drule_strip sortingTheory.PERM_MEM_EQ \\
 fs [MEM_GENLIST, EVERY_MEM]
QED

Triviality EVERY_lt_MAP_THE_if_lem:
 ∀l (n:num) f. EVERY (λx. x < n) l ⇒ MAP (λx. THE (if x < n then SOME (f x) else NONE)) l = MAP f l
Proof
 Induct \\ simp []
QED

Triviality FILTER_GENLIST_I:
 ∀n x. FILTER ($= x) (GENLIST I n) = if x < n then [x] else []
Proof
 Induct \\ rw [GENLIST, rich_listTheory.FILTER_APPEND]
QED

Triviality MAP_to_GENLIST:
 ∀l f. MAP f l = GENLIST (λi. f (EL i l)) (LENGTH l)
Proof
 Induct \\ simp [GENLIST_CONS, combinTheory.o_DEF]
QED

Triviality ALL_DISTINCT_GENLIST_I:
 ∀n. ALL_DISTINCT (GENLIST I n)
Proof
 simp [EL_ALL_DISTINCT_EL_EQ]
QED

Triviality PERM_GENLIST_MAP_EL_lem:
 ∀ps is. PERM is (GENLIST I (LENGTH ps)) ⇒ PERM ps (MAP (λidx. EL idx ps) is)
Proof
 rpt strip_tac \\
 rw [sortingTheory.PERM_BIJ_IFF, MAP_to_GENLIST, GENLIST_FUN_EQ_gen] \\
 drule_strip sortingTheory.PERM_LENGTH \\
 qexists_tac ‘λi. EL i is’ \\ simp [] \\
 rw [pred_setTheory.BIJ_DEF]
 >- (rw [pred_setTheory.INJ_DEF]
     >- (drule_strip PERM_GENLIST_I_EVERY_lt \\ fs [EVERY_EL])
     >- (fs [] \\ metis_tac [ALL_DISTINCT_GENLIST_I, sortingTheory.ALL_DISTINCT_PERM, EL_ALL_DISTINCT_EL_EQ]))
 >- (rw [pred_setTheory.SURJ_DEF]
     >- (drule_strip PERM_GENLIST_I_EVERY_lt \\ fs [EVERY_EL])
     >- (fs [] \\ drule_strip sortingTheory.PERM_MEM_EQ \\
         first_x_assum (qspec_then ‘x’ assume_tac) \\
         fs [MEM_GENLIST] \\ fs [MEM_EL] \\ metis_tac []))
QED

Triviality ALOOKUP_MAPi_lem:
 ∀f l k j.
 ALOOKUP (MAPi (λi x. (i + j, f x)) l) k =
 if j ≤ k ∧ k < j + LENGTH l then SOME $ f (EL (k-j) l) else NONE
Proof
 gen_tac \\ Induct \\ rw [combinTheory.o_DEF]

 >- (first_x_assum (qspecl_then [‘k’, ‘j + 1’] mp_tac) \\ simp [arithmeticTheory.ADD1] \\
     Cases_on ‘k − j’ \\ fs [arithmeticTheory.ADD1] \\
     ‘k - (j + 1) = n’ by decide_tac \\ 
     ‘∀(i:num). i + (j + 1) = j + (i + 1)’ by decide_tac \\
     simp [] \\ asm_rewrite_tac []) \\

 first_x_assum (qspecl_then [‘k’, ‘j + 1’] mp_tac) \\ simp [arithmeticTheory.ADD1] \\
 ‘∀(i:num). i + (j + 1) = j + (i + 1)’ by decide_tac \\ asm_rewrite_tac []
QED

Triviality ALOOKUP_MAPi:
 ∀f l k j. ALOOKUP (MAPi (λi x. (i, f x)) l) k = if k < LENGTH l then SOME $ f (EL k l) else NONE
Proof
 rpt gen_tac \\ qspecl_then [‘f’, ‘l’, ‘k’, ‘0’] mp_tac ALOOKUP_MAPi_lem \\ simp []
QED

Triviality IS_SOME_unit:
 ∀opt. IS_SOME opt ⇔ opt = SOME ()
Proof
 simp [optionTheory.IS_SOME_EXISTS]
QED

Triviality lookup_unit:
 ∀t var. invariant string_cmp t ⇒ lookup string_cmp var t = if member string_cmp var t then SOME () else NONE
Proof
 simp [lookup_thm, member_thm, comparisonTheory.string_cmp_good, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem sort_by_deps_correct_lemma:
 ∀ps ps'.
 sort_by_deps ps = INR ps' ⇒
 PERM ps ps' ∧
 ∀var i j. i < LENGTH ps' ∧ j < LENGTH ps' ∧ i < j ∧ MEM var (vreads (EL i ps')) ⇒ ~MEM var (vwrites (EL j ps'))
Proof
 simp [sort_by_deps_def] \\ rpt gen_tac \\ TOP_CASE_TAC \\ strip_tac \\ rveq \\ simp [] \\ 

 drule_strip top_sort_correct \\ fs [MAP_MAPi, combinTheory.o_DEF, MAPi_ignore_second] \\
 impl_tac >- simp [EL_ALL_DISTINCT_EL_EQ] \\ strip_tac \\

 simp [lookup_fromList] \\
 drule_strip PERM_GENLIST_I_EVERY_lt \\
 dep_rewrite.DEP_REWRITE_TAC [EVERY_lt_MAP_THE_if_lem] \\ simp [] \\

 conj_tac >- simp [PERM_GENLIST_MAP_EL_lem] \\

 simp [EL_MAP] \\ fs [ALOOKUP_MAPi] \\
 rpt strip_tac \\ first_x_assum (qspecl_then [‘i’, ‘j’] mp_tac) \\
 impl_tac >- fs [EVERY_EL] \\
 impl_tac >- (gs [GSYM IS_SOME_unit, read_deps_correct, EL_MAP] \\
              asm_exists_tac \\
              dep_rewrite.DEP_REWRITE_TAC [lookup_mapi_string_cmp] \\
              conj_tac >- simp [invariant_compute_writes_bw] \\
              simp [compute_writes_bw_correct] \\
              simp [invariant_compute_writes_bw, lookup_unit] \\

              conj_tac >- (simp [compute_writes_bw_correct] \\
                           gvs [MEM_EL, MEM_FLAT, MEM_MAP, EVERY_MEM] \\ metis_tac []) \\
              
              simp [compute_writers_def, lookup_map, lookup_filter_v, lookup_fromList, optionTheory.IS_SOME_MAP] \\
              fs [EVERY_EL] \\ simp [writes_to_correct]) \\
 strip_tac
QED

(** Other lemmas we need **)

Theorem PERM_vwrites:
 ∀ps ps'. PERM ps ps' ⇒ (∀var. MEM var (FLAT (MAP vwrites ps')) ⇔ MEM var (FLAT (MAP vwrites ps)))
Proof
 rpt strip_tac' \\ drule_strip sortingTheory.PERM_MEM_EQ \\ simp [MEM_FLAT, MEM_MAP]
QED

Theorem PERM_vnwrites:
 ∀ps ps'. PERM ps ps' ⇒ (∀var. MEM var (FLAT (MAP vnwrites ps')) ⇔ MEM var (FLAT (MAP vnwrites ps)))
Proof
 rpt strip_tac' \\ drule_strip sortingTheory.PERM_MEM_EQ \\ simp [MEM_FLAT, MEM_MAP]
QED

Theorem sort_by_deps_module_ok:
 ∀m combs. sort_by_deps m.combs = INR combs ∧ module_ok m ⇒ module_ok (m with combs := combs)
Proof
 rw [module_ok_def, writes_ok_def, writes_overlap_ok_def] \\
 metis_tac [sort_by_deps_correct_lemma, PERM_vwrites, PERM_vnwrites]
QED

(** Verilog semantics that sorts by deps **)

Definition sort_run_def:
 sort_run fext fbits m n = do
  combs <- sort_by_deps m.combs;
  run fext fbits (m with combs := combs) n
 od
End

Theorem sort_by_deps_correct:
 ∀fext fbits m n combs.
 sort_by_deps m.combs = INR combs ⇒
 sort_run fext fbits m n = run fext fbits (m with combs := combs) n ∧
 ∀var. MEM var (FLAT (MAP vwrites combs)) ⇔ MEM var (FLAT (MAP vwrites m.combs))
Proof
 rw [sort_run_def, sum_bind_def] \\ metis_tac [sort_by_deps_correct_lemma, PERM_vwrites]
QED

Theorem already_sorted_sort_run:
 ∀m fext fbits n.
 sort_by_deps m.combs = INR m.combs ⇒
 sort_run fext fbits m n = run fext fbits m n
Proof
 rw [sort_run_def, sum_bind_def] \\ f_equals_tac \\ simp [module_component_equality]
QED

val _ = export_theory ();
