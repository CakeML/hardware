open hardwarePreamble;

open alistTheory sptreeTheory;

val _ = new_theory "topological_sort";

infix THEN2;

Definition get_first_without_deps_def:
 (get_first_without_deps [] = NONE) ∧
 (get_first_without_deps ((k, deps) :: ds) =
  if size deps = 0 then
   SOME (k, ds)
  else
   case get_first_without_deps ds of
     NONE => NONE
   | SOME (hit, rem) => SOME (hit, (k, deps) :: rem))
End

Theorem get_first_without_deps_rem_length:
 ∀deps hit rem. get_first_without_deps deps = SOME (hit, rem) ⇒ LENGTH rem < LENGTH deps
Proof
 Induct \\ TRY PairCases \\ simp [get_first_without_deps_def] \\ every_case_tac \\ simp []
QED

Definition top_sort_aux_def:
 top_sort_aux (deps : (num (* name *) # num_set (* deps *)) list) =
  if deps = [] then
   SOME []
  else
   case get_first_without_deps deps of
     NONE => NONE
   | SOME (hit, rem) =>
    (case top_sort_aux (MAP (λ(d, deps). (d, delete hit deps)) rem) of
       NONE => NONE
     | SOME topo => SOME $ hit :: topo)
Termination
 WF_REL_TAC `measure LENGTH` \\ simp [get_first_without_deps_rem_length]
End

(* Wrapper to remove self dependencies *)
Definition top_sort_def:
 top_sort deps = top_sort_aux (MAP (λ(d, deps). (d, delete d deps)) deps)
End

(*
Triviality top_sort_example:
   top_sort
     [(0,fromAList[(5,())]);         (* 0 has no deps *)
      (1,fromAList[]);               (* 1 depends on 0 *)
      (5,fromAList[(3,())]);
      (2,fromAList[(0,())]);         (* 2 depends on 0 *)
      (3,fromAList[(1,())])]         (* 3 depends on 0 *)
   = ARB
Proof
 EVAL_TAC
QED
*)

Theorem get_first_without_deps_correct:
 ∀deps d deps'.
 get_first_without_deps deps = SOME (d, deps') ∧
 ALL_DISTINCT (MAP FST deps) ⇒
 ∃ddeps deps1 deps2.
  deps = deps1 ++ [(d, ddeps)] ++ deps2 ∧
  (*ALOOKUP deps d = SOME ddeps ∧*) size ddeps = 0 ∧
  deps' = deps1 ++ deps2
Proof
 Induct \\ TRY PairCases \\ simp [get_first_without_deps_def] \\ rpt gen_tac \\
 IF_CASES_TAC >- (rw [] \\ qexistsl_tac [‘h1’, ‘[]’, ‘deps’] \\ simp []) \\
 rpt TOP_CASE_TAC \\ rw [] \\ drule_first \\ rveq \\
 qexistsl_tac [‘ddeps’, ‘(h0, h1)::deps1’, ‘deps2’] \\ simp []
QED

Triviality all_distinct_perm_middle_lem:
 ALL_DISTINCT (MAP FST deps1 ⧺ [q] ⧺ MAP FST deps2) ∧
 PERM x (MAP FST deps1 ⧺ MAP FST deps2) ∧
 n < LENGTH x ⇒
 (*~MEM q x*)
 q ≠ EL n x
Proof
 rpt strip_tac \\ drule_strip sortingTheory.PERM_MEM_EQ \\
 fs [ALL_DISTINCT_APPEND, MEM_MAP] \\ metis_tac [MEM_EL]
QED

Triviality domain_lookup_NONE:
 ∀t k. lookup k t = NONE ⇔ k ∉ domain t
Proof
 metis_tac [domain_lookup, optionTheory.option_CLAUSES]
QED

Triviality lookup_size_0:
 ∀t n. size t = 0 ⇒ lookup n t = NONE
Proof
 simp [size_zero_empty, domain_lookup_NONE]
QED

Theorem top_sort_aux_correct:
 ∀deps sort.
 top_sort_aux deps = SOME sort ∧ ALL_DISTINCT (MAP FST deps) ⇒
 PERM sort (MAP FST deps) ∧
 ∀i j d ideps idep. i < j ∧
                    i < LENGTH sort ∧
                    j < LENGTH sort ∧
                    ALOOKUP deps (EL i sort) = SOME ideps ∧
                    lookup idep ideps = SOME () ⇒
                    EL j sort ≠ idep
Proof
 measureInduct_on ‘LENGTH deps’ \\ gen_tac \\
 rewrite_tac [Once top_sort_aux_def] \\ IF_CASES_TAC >- simp [] \\
 (*rpt TOP_CASE_TAC \\ strip_tac \\ rveq \\*)
 PURE_CASE_TAC >- simp [] \\ CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [])) \\
 PURE_CASE_TAC \\ CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [])) \\
 PURE_CASE_TAC >- simp [] \\ CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [])) \\
 strip_tac \\ rveq \\
 (* ... *)

 drule_strip get_first_without_deps_correct \\
 
 qmatch_asmsub_abbrev_tac ‘top_sort_aux deps = _’ \\
 first_x_assum (qspec_then ‘deps’ mp_tac) \\
 unabbrev_all_tac \\
 impl_tac >- simp [] \\ strip_tac \\ drule_first \\
 impl_tac >- (fs [ALL_DISTINCT_APPEND, MEM_MAP] \\ rw []
              THEN2 fs [MAP_MAP_o, FST_o] \\
              rpt (pairarg_tac \\ gvs []) \\
              gvs [pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] \\
              metis_tac []) \\
 strip_tac  \\
 conj_tac >- (simp [sortingTheory.PERM_CONS_EQ_APPEND] \\
              qexistsl_tac [‘MAP FST deps1’, ‘MAP FST deps2’] \\
              fs [MAP_MAP_o, FST_o]) \\
 rpt strip_tac \\
 Cases_on ‘i’
 >- (Cases_on ‘j’ \\ gvs [ALL_DISTINCT_APPEND, ALOOKUP_APPEND, GSYM ALOOKUP_NONE] \\
     fs [MAP_MAP_o, FST_o] \\
     gvs [ALOOKUP_MAP] \\ drule_strip lookup_size_0 \\ fs []) \\     

 Cases_on ‘j’ >- fs [] \\ first_x_assum (qspecl_then [‘n’, ‘n'’] mp_tac) \\ fs [] \\
 fs [ALOOKUP_APPEND, ALOOKUP_MAP] \\ CASE_TAC
 >- (fs [MAP_MAP_o, FST_o] \\ every_case_tac \\fs [lookup_delete] \\ 
     metis_tac [all_distinct_perm_middle_lem]) \\
 gvs [MAP_MAP_o, FST_o, lookup_delete] \\ metis_tac [all_distinct_perm_middle_lem]
QED

Theorem top_sort_correct:
 top_sort deps = SOME sort ∧ ALL_DISTINCT (MAP FST deps) ⇒
 PERM sort (MAP FST deps) ∧
 ∀i j d ideps idep. i < j ∧
                    i < LENGTH sort ∧
                    j < LENGTH sort ∧
                    ALOOKUP deps (EL i sort) = SOME ideps ∧
                    lookup idep ideps = SOME () ⇒
                    (*MEM var (vreads (EL i ps')) ⇒ ~MEM var (vwrites (EL j ps'))*)
                    EL j sort ≠ idep
Proof
 rewrite_tac [top_sort_def] \\ rpt strip_tac' \\ drule_strip top_sort_aux_correct \\ 
 impl_tac >- simp [MAP_MAP_o, FST_o] \\ strip_tac \\
 conj_tac >- fs [MAP_MAP_o, FST_o] \\
 rpt strip_tac \\ first_x_assum (qspecl_then [‘i’, ‘j’] mp_tac) \\
 simp [ALOOKUP_MAP_2, lookup_delete] \\
 gvs [MAP_MAP_o, FST_o] \\
 drule_strip (GSYM sortingTheory.ALL_DISTINCT_PERM) \\
 Cases_on ‘i = j’ \\
 fs [EL_ALL_DISTINCT_EL_EQ]
QED

val _ = export_theory ();
