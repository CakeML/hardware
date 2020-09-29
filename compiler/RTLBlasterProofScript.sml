open hardwarePreamble;

open balanced_mapTheory bitstringTheory numposrepTheory rich_listTheory;

open sumExtraTheory oracleTheory RTLTheory RTLTypeTheory RTLPropsTheory RTLBlasterTheory;

open dep_rewrite;

open RTLSyntax RTLLib;

val _ = new_theory "RTLBlasterProof";

(* this proof/file is kind of a mess after some refactorings... but it works *)

Definition blasted_cell_def:
 blasted_cell min max cell ⇔ EVERY (λout. min ≤ out ∧ out < max) (cell_output cell)
End

Definition blasted_netlist_ranges_def:
 blasted_netlist_ok min max nlold nl ⇔
 EVERY (λc. MEM c nlold ∨ blasted_cell min max c) nl
End

Definition netlist_distinct_def:
 netlist_distinct nl ⇔ ALL_DISTINCT (FLAT (MAP cell_output nl))
End

Definition blasted_circuit_def:
 blasted_circuit (Circuit _ regs nl) ⇔
 blast_regs_distinct regs ∧ deterministic_netlist nl
End

val lookup_insert_var_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) lookup_insert) var_cmp_good
 |> REWRITE_RULE [var_cmp_antisym];

val lookup_delete_var_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) lookup_delete) var_cmp_good
 |> REWRITE_RULE [var_cmp_antisym];

val insert_thm_var_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) (SPEC_ALL insert_thm)) var_cmp_good;

val delete_thm_var_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) (SPEC_ALL delete_thm)) var_cmp_good;

val fromList_thm_var_cmp =
 MATCH_MP fromList_thm var_cmp_good;

Triviality lt1:
 ∀n. n < 1 ⇔ n = 0
Proof
 decide_tac
QED

Triviality lt2:
 ∀b. b < 2 ⇔ b = 0 ∨ b = 1
Proof
 decide_tac
QED

Triviality lt4:
 ∀n. n < 4 ⇔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3
Proof
 decide_tac
QED

Triviality le4:
 ∀n. n ≤ 4 ⇔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4
Proof
 decide_tac
QED

Triviality le12:
 ∀n. n ≤ 12 ⇔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
              n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12
Proof
 Cases >- simp [] \\ ntac 6 (Cases_on ‘n'’ >- simp [] \\ Cases_on ‘n’ >- simp []) \\ simp []
QED

(* to remember: we only blast deterministic netlists ... <-- does this matter? *)

(* benv for "blast env" *)
val blast_rel_def = Define `
 blast_rel fext si tmpnum s bs <=> (* <-- tmpnum here is tmpnum from compiler (not blaster!) *)
  bs.fbits = s.fbits /\
  !var. var_lt var tmpnum ==> (* <-- probably redundant when we assume netlist_lt ... *)
        case cget_var s var of
          INL e => T
        | INR (CBool b) =>
           (lookup var_cmp var si = NONE /\ cget_var bs var = INR (CBool b)) ∨
           (∃inp. lookup var_cmp var si = SOME (BoolInp inp) /\ cell_inp_run fext bs inp = INR (CBool b))
        | INR (CArray b) =>
           ?inps. lookup var_cmp var si = SOME (ArrayInp inps) /\
                  LENGTH inps = LENGTH b /\
                  !i. i < LENGTH inps ==>
                      cell_inp_run fext bs (EL i inps) = INR (CBool (EL i b))`;

val blast_reg_rel_def = Define `
 blast_reg_rel si s bs <=>
  bs.fbits = s.fbits /\
  !reg. case cget_var s (RegVar reg 0) of
          INL e => T
        | INR (CBool b) => lookup var_cmp (RegVar reg 0) si = NONE /\ cget_var bs (RegVar reg 0) = INR (CBool b)
        | INR (CArray b') =>
           (?inps. lookup var_cmp (RegVar reg 0) si = SOME (ArrayInp inps) /\ LENGTH inps = LENGTH b') /\
           !i. i < LENGTH b' ==> cget_var bs (RegVar reg i) = INR (CBool (EL i b'))`;

(* regs ok in si ... todo: why are there type annotations here? *)
val si_prefilled_def = Define `
 si_prefilled si (t, reg, i, v : value option, inp : cell_input option) <=>
  case t of
    CBool_t => lookup var_cmp (RegVar reg i) si = NONE
  | CArray_t l => ?inps. lookup var_cmp (RegVar reg i) si = SOME (ArrayInp inps) /\ LENGTH inps = l`;

val si_prefilleds_def = Define `
 si_prefilleds si regs <=> EVERY (si_prefilled si) regs`;

Theorem si_prefilleds_cong:
 !regs si si'.
 (!reg i. lookup var_cmp (RegVar reg i) si' = lookup var_cmp (RegVar reg i) si) ==>
 si_prefilleds si' regs = si_prefilleds si regs
Proof
 rw [si_prefilleds_def] \\ match_mp_tac EVERY_CONG \\ rw [] \\ PairCases_on ‘x’ \\ rw [si_prefilled_def]
QED

val blasterstate_ok_def = Define `
 blasterstate_ok si min max <=>
  min <= max /\
  invariant var_cmp si /\
  (!var inp. lookup var_cmp var si = SOME (BoolInp inp) ==> cell_input_lt inp max) ∧
  (!var inps. lookup var_cmp var si = SOME (ArrayInp inps) ==> EVERY (\inp. cell_input_lt inp max) inps)`;

Theorem sorted_all_distinct_lt:
 !(l:num list). SORTED ($<) l ==> ALL_DISTINCT l
Proof
 rpt strip_tac' \\ irule sortingTheory.SORTED_ALL_DISTINCT \\ asm_exists_any_tac \\ 
 rw [relationTheory.irreflexive_def]
QED

val only_regs_def = Define ‘
 only_regs s <=>
 !var. case var of
         RegVar reg i => if i = 0 then T else cget_var s var = INL UnknownVariable
       | NetVar n => cget_var s var = INL UnknownVariable’;

Theorem only_regs_fbits:
 !s fbits. only_regs (s with fbits := fbits) = only_regs s
Proof
 rw [only_regs_def, cget_var_fbits]
QED

Theorem only_regs_cset_var_RegVar:
 !s reg v. only_regs (cset_var s (RegVar reg 0) v) = only_regs s
Proof
 rw [only_regs_def, cget_var_cset_var] \\ eq_tac \\ rpt strip_tac \\ first_x_assum (qspec_then ‘var’ mp_tac) \\ TOP_CASE_TAC \\ rw []
QED

Definition var_ge_def:
 (var_ge (RegVar _ _) n <=> T) /\
 (var_ge (NetVar m) n <=> n <= m)
End

Theorem var_ge_le:
 ∀var n m. var_ge var n ∧ m ≤ n ⇒ var_ge var m
Proof
 Cases \\ rw [var_ge_def]
QED

Definition cell_input_ge_def:
 (cell_input_ge (ConstInp _) n <=> T) /\
 (cell_input_ge (ExtInp _ _) n <=> T) /\
 (cell_input_ge (VarInp var _) n <=> var_ge var n)
End

Theorem cell_input_ge_le:
 ∀inp n m. cell_input_ge inp n ∧ m ≤ n ⇒ cell_input_ge inp m
Proof
 Cases \\ rw [cell_input_ge_def] \\ drule_strip var_ge_le
QED

Theorem EVERY_cell_input_ge_le:
 !l n m. EVERY (λinp. cell_input_ge inp n) l /\ m <= n ==> EVERY (λinp. cell_input_ge inp m) l
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [] \\
 match_mp_tac cell_input_ge_le \\ rpt asm_exists_tac
QED

(* tmpnum here is tmpnum from compiler *)
Definition bsi_cell_input_ok_def:
 bsi_cell_input_ok out tmpnum inp <=> cell_input_lt inp out \/ cell_input_ge inp tmpnum
End

(** si wf things **)

val si_wf_def = Define `
 si_wf si <=> (!inps reg. lookup var_cmp (RegVar reg 0) si = SOME (ArrayInp inps) ==>
                          inps = GENLIST (\i. VarInp (RegVar reg i) NONE) (LENGTH inps)) /\
              (!reg idx. idx <> 0 ==> lookup var_cmp (RegVar reg idx) si = NONE) ∧
              (∀reg idx inp. lookup var_cmp (RegVar reg idx) si ≠ SOME (BoolInp inp))`;

Theorem si_wf_shape:
 !var inps si.
 si_wf si /\ lookup var_cmp var si = SOME (ArrayInp inps) ==>
 (?reg. var = RegVar reg 0 /\ inps = GENLIST (\i. VarInp (RegVar reg i) NONE) (LENGTH inps)) \/
 (?n. var = NetVar n)
Proof
 simp [si_wf_def] \\ Cases \\ rpt strip_tac'
 >- (Cases_on ‘n’ \\ rfs [])
 \\ metis_tac []
QED

Theorem blast_rel_only_regs:
 !fext fext' si si' tmpnum s bs.
 only_regs s /\ si_wf si /\ si_wf si' /\
 (!reg i. lookup var_cmp (RegVar reg i) si' = lookup var_cmp (RegVar reg i) si) ==>
 blast_rel fext' si' tmpnum s bs = blast_rel fext si tmpnum s bs
Proof
 rw [blast_rel_def, only_regs_def] \\ eq_tac \\ rw [] \\ drule_first \\ first_x_assum (qspec_then ‘var’ mp_tac) \\
 TOP_CASE_TAC \\ fs [] \\ rw [] \\ fs [] \\ rpt TOP_CASE_TAC \\ fs []
 >- metis_tac []
 >- rfs [si_wf_def]
 >- (qexists_tac ‘inps’ \\ conj_tac >- metis_tac [] \\ conj_tac >- simp [] \\ rpt strip_tac \\
    first_x_assum (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\
    drule_strip si_wf_shape \\ fs [] \\ rveq \\ first_assum (once_rewrite_tac o sing) \\
    simp [EL_GENLIST, cell_inp_run_def])
 >- rfs [si_wf_def]
 \\ (* proof duplication that is easy to fix: *)
    rpt strip_tac \\
    first_x_assum (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\
    qpat_x_assum ‘si_wf si’ assume_tac \\
    drule_strip si_wf_shape \\ fs [] \\ rveq \\ first_assum (once_rewrite_tac o sing) \\
    simp [EL_GENLIST, cell_inp_run_def]
QED

Theorem blast_rel_blast_reg_rel:
 !fext si tmpnum s bs. blast_rel fext si tmpnum s bs /\ si_wf si ==> blast_reg_rel si s bs
Proof
 rw [blast_rel_def, si_wf_def, blast_reg_rel_def] \\
 first_x_assum (qspec_then `RegVar reg 0` mp_tac) \\
 impl_tac >- simp [var_lt_def] \\ rpt TOP_CASE_TAC \\
 rpt strip_tac \\ drule_first \\
 first_x_assum (qspec_then `i` mp_tac) \\ rfs [cell_inp_run_def, sum_bind_INR, cget_fext_var_def]
QED

Theorem blast_reg_rel_blast_rel:
 !fext si tmpnum s bs. blast_reg_rel si s bs /\ only_regs s /\ si_wf si ==> blast_rel fext si tmpnum s bs
Proof
 rw [blast_reg_rel_def, only_regs_def, blast_rel_def] \\
 first_x_assum (qspec_then `var` mp_tac) \\ TOP_CASE_TAC \\ strip_tac
 >- (rveq \\ first_x_assum (qspec_then ‘s'’ assume_tac) \\ rpt TOP_CASE_TAC \\ fs [] \\
    rpt strip_tac \\ drule_first \\ drule_strip si_wf_shape \\ fs [] \\ rveq \\
    first_assum (once_rewrite_tac o sing) \\ simp [EL_GENLIST, cell_inp_run_def, sum_bind_def, cget_fext_var_def])
 \\ simp []
QED

Theorem blast_reg_rel_only_regs:
 !fext fext' si si' tmpnum s bs.
 only_regs s /\ si_wf si /\ si_wf si' /\
 (!reg i. lookup var_cmp (RegVar reg i) si' = lookup var_cmp (RegVar reg i) si) ==>
 blast_reg_rel si' s bs = blast_reg_rel si s bs
Proof
 metis_tac [blast_reg_rel_blast_rel, blast_rel_blast_reg_rel, blast_rel_only_regs]
QED

Theorem blast_rel_cset_var_reg_bool:
 !fext si tmpnum s bs reg b.
 blast_rel fext si tmpnum s bs /\
 si_wf si /\
 only_regs s /\
 lookup var_cmp (RegVar reg 0) si = NONE ==>
 blast_rel fext si tmpnum (cset_var s (RegVar reg 0) (CBool b))
                          (cset_var bs (RegVar reg 0) (CBool b))
Proof
 rw [blast_rel_def, cset_var_fbits, cget_var_cset_var] \\ 
 IF_CASES_TAC >- fs [] \\ drule_first \\ rpt TOP_CASE_TAC \\ fs [] \\
 rpt strip_tac \\

 fs [only_regs_def] \\ first_x_assum (qspec_then ‘var’ mp_tac) \\ TOP_CASE_TAC \\ fs [] \\ strip_tac \\ rveq
 >- rfs [si_wf_def] \\
 drule_strip si_wf_shape \\ fs [] \\ rveq \\

 first_x_assum (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\
 first_assum (once_rewrite_tac o sing) \\ simp [EL_GENLIST, cell_inp_run_cset_var] \\ fs []
QED

Theorem blast_cell_inp_run_correct_bool:
 !inp tmpnum inp' fext s bs v blast_s n.
 blast_cell_input blast_s inp = BoolInp inp' /\
 cell_inp_run fext s inp = INR v /\
 rtltype_extenv_n blast_s.extenv fext /\
 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum /\
 blast_rel fext blast_s.si tmpnum s bs /\
 cell_input_lt inp n /\
 cell_input_covered_by_extenv blast_s.extenv inp /\
 n <= tmpnum ==>
 cell_inp_run fext bs inp' = INR v /\
 ?b. v = CBool b
Proof
 rewrite_tac [blast_rel_def] \\ Cases
 >- (Cases_on `v` \\ simp [cell_inp_run_def, blast_cell_input_def])

 >- (simp [cell_inp_run_def, sum_bind_INR, blast_cell_input_def, rtltype_extenv_n_def] \\
     rpt strip_tac' \\ every_case_tac \\ fs [cget_fext_var_def]
     >- (fs [cell_input_covered_by_extenv_def] \\ fs [])
     >- (fs [cell_input_covered_by_extenv_def] \\ fs [])
     >- (drule_first \\ fs [] \\ rveq \\ simp [cell_inp_run_def, sum_bind_def, cget_fext_var_def] \\ fs [rtltype_v_cases])
     \\ every_case_tac \\ fs [] \\ drule_first \\ fs [] \\ rveq \\ fs [sum_map_INR] \\
        rw [cell_inp_run_def, sum_bind_def, cget_fext_var_def, sum_map_def])

 \\ simp [cell_inp_run_def, blast_cell_input_def, cell_input_lt_def] \\
    rpt strip_tac' \\ first_x_assum (qspec_then `v` mp_tac) \\
    impl_tac >- (match_mp_tac var_lt_le \\ asm_exists_tac \\ fs [blasterstate_ok_def]) \\
    rpt TOP_CASE_TAC
    >- fs [sum_bind_INR]
    >- (fs [sum_bind_INR] \\ every_case_tac \\ fs [] \\ rveq
       >- (fs [cell_inp_run_def, sum_bind_def, cget_fext_var_def] \\ rw [])
       \\ fs [cget_fext_var_def] \\ rw [])
    \\ strip_tac \\ every_case_tac \\ fs [] \\ rveq \\ fs [sum_bind_def, cget_fext_var_def, sum_map_INR] \\ rveq \\
       fs [sum_revEL_INR, revEL_def]
QED

Theorem blast_cell_inp_run_correct_array:
 !inp n tmpnum fext s bs v blast_s inps.
 blast_cell_input blast_s inp = ArrayInp inps /\
 cell_inp_run fext s inp = INR v /\
 rtltype_extenv_n blast_s.extenv fext /\
 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum /\
 blast_rel fext blast_s.si tmpnum s bs /\
 cell_input_lt inp n /\
 n <= tmpnum ==>
 ?b. v = CArray b /\ LENGTH b = LENGTH inps /\
     (!i. i < LENGTH inps ==> cell_inp_run fext bs (EL i inps) = INR (CBool (EL i b)))
Proof
 rewrite_tac [blast_rel_def] \\ Cases
 >- (Cases_on `v` \\ simp [cell_inp_run_def, blast_cell_input_def, EL_MAP])

 >- (simp [cell_inp_run_def, sum_bind_INR, blast_cell_input_def, rtltype_extenv_n_def] \\
     rpt strip_tac \\ every_case_tac \\ fs [cget_fext_var_def] \\ rveq \\
     drule_first \\ fs [rtltype_v_CArray_t] \\ rveq \\
     simp [cell_inp_run_def, sum_bind_def, cget_fext_var_def, sum_revEL_revEL, revEL_def, sum_map_def])

 \\ simp [cell_inp_run_def, blast_cell_input_def, cell_input_lt_def] \\
    rpt strip_tac' \\ first_x_assum (qspec_then `v` mp_tac) \\
    impl_tac >- (match_mp_tac var_lt_le \\ asm_exists_tac \\ fs [blasterstate_ok_def]) \\
    TOP_CASE_TAC \\ fs [sum_bind_INR] \\ every_case_tac \\ fs [] \\ rveq \\ strip_tac \\
    fs [cget_fext_var_def] \\ rw []
QED

Theorem blasterstate_ok_insert:
 !si min max out l.
 blasterstate_ok si min max ==>
 blasterstate_ok (insert var_cmp (NetVar out) (ArrayInp (GENLIST (λi. VarInp (NetVar (i + max)) NONE) l)) si) min (l + max)
Proof
 rw [blasterstate_ok_def, lookup_insert_var_cmp, insert_thm_var_cmp] \\
 every_case_tac
 >- rw [EVERY_GENLIST, cell_input_lt_def, var_lt_def]
 >- (drule_first \\ match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])
 >- rw [EVERY_GENLIST, cell_input_lt_def, var_lt_def]
 \\ drule_first \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\
 rw [] \\ match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp []
QED

(* TODO: rename *)
Theorem EVERY_output_not_in_si_not_NetVar:
 !inps out tmpnum idx i.
 EVERY (bsi_cell_input_ok out tmpnum) inps /\ i < LENGTH inps /\ out < tmpnum ==>
 EL i inps <> VarInp (NetVar out) idx
Proof
 rw [EVERY_EL] \\ first_x_assum (qspec_then `i` mp_tac) \\
 Cases_on `EL i inps` \\ simp [bsi_cell_input_ok_def] \\
 Cases_on ‘v’ \\ simp [cell_input_lt_def, cell_input_ge_def, var_lt_def, var_ge_def]
QED

Theorem cell1_bitwise_correct:
 !fext inps tmpnum b s.
 EVERY (\inp. cell_input_lt inp tmpnum) inps /\
 (!i. i < LENGTH inps ==> cell_inp_run fext s (EL i inps) = INR (CBool (EL i b))) /\
 LENGTH b = LENGTH inps ==>
 ?s'. sum_foldM (cell_run fext) s (MAPi (λi inp. Cell1 CNot (i + tmpnum) inp) inps) =
      INR s' /\
      s'.fbits = s.fbits /\ (* <-- follows from general determinism thm... *)
      (!inp. cell_input_lt inp tmpnum ==> cell_inp_run fext s' inp = cell_inp_run fext s inp) /\
      (!i. i < LENGTH inps ==> cell_inp_run fext s' (VarInp (NetVar (i + tmpnum)) NONE) =
                               INR (CBool ~(EL i b)))
Proof
 gen_tac \\ Induct \\ rw [sum_foldM_def, sum_bind_INR, cell_run_def] \\
 Cases_on `b` \\ fs [] \\
 first_assum (qspec_then `0` mp_tac) \\ impl_tac >- simp [] \\ PURE_REWRITE_TAC [EL, HD] \\
 strip_tac \\ simp [PULL_EXISTS, cell1_run_def] \\

 qmatch_goalsub_abbrev_tac `sum_foldM _ s' _` \\
 first_x_assum (qspecl_then [`SUC tmpnum`, `t`, `s'`] mp_tac) \\
 unabbrev_all_tac \\
 impl_tac >- (
 conj_tac >- (irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [cell_input_lt_SUC]) \\
 reverse conj_tac >- simp [] \\
 rpt strip_tac \\
 first_x_assum (qspec_then `SUC i` mp_tac) \\ simp [] \\
 Cases_on `EL i inps` \\ simp [cell_inp_run_def, cget_var_cset_var] \\
 fs [EVERY_EL] \\ drule_first \\ rfs [cell_input_lt_def] \\
 Cases_on `v` \\ fs [var_lt_def]) \\ strip_tac \\

 `((λi inp. Cell1 CNot (i + tmpnum) inp) ∘ SUC) = (λi inp. Cell1 CNot (i + SUC tmpnum) inp)` by
 simp [FUN_EQ_THM] \\ pop_assum (fn th => rewrite_tac [th]) \\ simp [cset_var_fbits] \\

 conj_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `inp` mp_tac) \\
              simp [cell_input_lt_SUC, cell_input_lt_cell_inp_run_cset_var]) \\

 Cases >- (simp [] \\ first_x_assum (qspec_then `VarInp (NetVar tmpnum) NONE` mp_tac) \\
          simp [cell_input_lt_def, var_lt_def, cell_inp_run_cset_var]) \\

 simp [] \\ strip_tac \\ drule_first \\ fs [arithmeticTheory.ADD1]
QED

Theorem blast_cellMux_correct:
 !lhs rhs lhs' rhs' c c' tmpnum s fext.
 cell_inp_run fext s c = INR (CBool c') ∧
 LENGTH lhs = LENGTH rhs ∧
 LENGTH lhs' = LENGTH lhs ∧
 (!i. i < LENGTH lhs ==> cell_inp_run fext s (EL i lhs) = INR (CBool (EL i lhs'))) ∧
 LENGTH rhs' = LENGTH rhs ∧
 (!i. i < LENGTH rhs ==> cell_inp_run fext s (EL i rhs) = INR (CBool (EL i rhs'))) ∧
 cell_input_lt c tmpnum ∧
 EVERY (\inp. cell_input_lt inp tmpnum) lhs ∧
 EVERY (\inp. cell_input_lt inp tmpnum) rhs ⇒
 ∃s'. sum_foldM (cell_run fext) s (MAP2i (λi inp2 inp3. CellMux (i + tmpnum) c inp2 inp3) lhs rhs) = INR s' /\
      s'.fbits = s.fbits /\ (* <-- follows from general determinism thm... *)
      (!inp. cell_input_lt inp tmpnum ==> cell_inp_run fext s' inp = cell_inp_run fext s inp) /\
      (!i. i < LENGTH lhs ==> cell_inp_run fext s' (VarInp (NetVar (i + tmpnum)) NONE) =
                              INR (CBool (EL i (if c' then lhs' else rhs'))))
Proof
 Induct >- rw [sum_foldM_def] \\ Cases_on ‘lhs'’ >- rw [] \\ Cases_on ‘rhs’ >- rw [] \\ Cases_on ‘rhs'’ >- rw [] \\
 fs [sum_foldM_def, sum_bind_INR, cell_run_def] \\ rpt strip_tac' \\

 first_assum (qspec_then `0` mp_tac) \\ impl_tac >- simp [] \\
 last_assum (qspec_then `0` mp_tac) \\ impl_tac >- simp [] \\ 
 PURE_REWRITE_TAC [EL, HD] \\ rpt strip_tac \\ simp [cellMux_run_def] \\

 qmatch_goalsub_abbrev_tac `sum_foldM _ s' _` \\
 first_x_assum (qspecl_then [‘t'’, ‘t’, ‘t''’, ‘c’, ‘c'’, ‘SUC tmpnum’, ‘s'’, ‘fext’] mp_tac) \\
 unabbrev_all_tac \\ impl_tac >- (rw [cell_input_lt_cell_inp_run_cset_var]
 >- (fs [EVERY_EL, cell_input_lt_cell_inp_run_cset_var] \\ last_x_assum (qspec_then ‘SUC i’ mp_tac) \\ simp [])
 >- (fs [EVERY_EL, cell_input_lt_cell_inp_run_cset_var] \\ last_x_assum (qspec_then ‘SUC i’ mp_tac) \\ simp [])
 >- (first_x_assum (qspec_then ‘SUC i’ mp_tac) \\ fs [EVERY_EL, cell_input_lt_cell_inp_run_cset_var] \\ simp [])
 >- (first_x_assum (qspec_then ‘SUC i’ mp_tac) \\ fs [EVERY_EL, cell_input_lt_cell_inp_run_cset_var] \\ simp [])
 >- (match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])
 \\ match_mp_tac EVERY_cell_input_lt_le \\ asm_exists_tac \\ simp []) \\ strip_tac \\

 ‘((λi inp2 inp3. CellMux (i + tmpnum) c inp2 inp3) ∘ SUC) = (λi inp2 inp3. CellMux (i + SUC tmpnum) c inp2 inp3)’
 by simp [FUN_EQ_THM] \\

 simp [cset_var_fbits] \\ rpt strip_tac
 >- (drule_strip cell_input_lt_SUC \\ drule_first \\ simp [cell_input_lt_cell_inp_run_cset_var])
 \\ Cases_on ‘i’ \\ fs []
 >- (first_x_assum (qspec_then ‘VarInp (NetVar tmpnum) NONE’ mp_tac) \\
     impl_tac >- simp [cell_input_lt_def, var_lt_def] \\ strip_tac \\ rw [cell_inp_run_cset_var])
 \\ drule_first \\ rw [] \\ fs [arithmeticTheory.ADD1]
QED

Theorem blast_cell_input_SOME_bool: (* todo: rename *)
 !inp blast_s inp' tmpnum.
 blast_cell_input blast_s inp = BoolInp inp' /\
 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum ∧
 cell_input_lt inp blast_s.tmpnum ==>
 cell_input_lt inp' blast_s.tmpnum
Proof
 Cases
 >- (Cases_on `v` \\ rw [blast_cell_input_def] \\ rw [cell_input_lt_def])

 >- (rw [blast_cell_input_def] \\ every_case_tac \\ rw [cell_input_lt_def])

 >- (rw [blast_cell_input_def, blasterstate_ok_def] \\ every_case_tac \\ fs [] \\
     drule_first \\ rw [] \\ fs [EVERY_EL, revEL_def, cell_input_lt_def])
QED

Theorem blast_cell_input_SOME: (* todo: rename *)
 !inp blast_s inps tmpnum.
 blast_cell_input blast_s inp = ArrayInp inps /\
 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum ==>
 EVERY (\inp. cell_input_lt inp blast_s.tmpnum) inps
Proof
 Cases
 >- (Cases_on `v` \\ rw [blast_cell_input_def] \\
    rw [EVERY_MEM, MEM_MAP] \\ simp [cell_input_lt_def])

 >- (rpt gen_tac \\ simp [blast_cell_input_def] \\ every_case_tac \\ strip_tac \\ rveq \\
    rw [EVERY_MEM, MEM_GENLIST] \\ simp [cell_input_lt_def])

 >- (rw [blast_cell_input_def, blasterstate_ok_def] \\ every_case_tac \\ fs [] \\ drule_first \\ rw [])
QED

(* should be merged with above... blasterstate_ok unrolled... *)        
Theorem blast_cell_input_bool_cell_input_lt:
 !inp inp' blast_s out tmpnum.
 blast_cell_input blast_s inp = BoolInp inp' /\
 cell_input_lt inp out /\ out <= tmpnum /\
 (!var inps. lookup var_cmp var blast_s.si = SOME (ArrayInp inps) ==> EVERY (\inp. cell_input_lt inp tmpnum) inps) ∧
 (!var inp. lookup var_cmp var blast_s.si = SOME (BoolInp inp) ==> cell_input_lt inp tmpnum) ⇒
 cell_input_lt inp' tmpnum
Proof
 Cases \\ rw [blast_cell_input_def]
 >- (Cases_on ‘v’ \\ fs [blast_cell_input_def] \\ rw [cell_input_lt_def])
 >- (every_case_tac \\ fs [] \\ rw [cell_input_lt_def])
 \\ every_case_tac \\ fs [] \\ rveq
 >- drule_strip cell_input_lt_le
 >- drule_first
 >- drule_strip cell_input_lt_le
 >- drule_first
 >- (drule_first \\ fs [revEL_def, EVERY_EL])
 >- simp [cell_input_lt_def]
QED

Theorem blast_cell_input_bool_bsi_cell_input_ok:
 !inp inp' blast_s out tmpnum.
 blast_cell_input blast_s inp = BoolInp inp' /\
 cell_input_lt inp out /\
 (!var inps. lookup var_cmp var blast_s.si = SOME (ArrayInp inps) ==> EVERY (bsi_cell_input_ok out tmpnum) inps) ∧
 (!var inp. lookup var_cmp var blast_s.si = SOME (BoolInp inp) ==> bsi_cell_input_ok out tmpnum inp) ==>
 bsi_cell_input_ok out tmpnum inp'
Proof
 Cases \\ rpt gen_tac
 >- (Cases_on ‘v’ \\ rw [blast_cell_input_def] \\ simp [bsi_cell_input_ok_def, cell_input_lt_def, cell_input_ge_def])
 >- (simp [blast_cell_input_def] \\ every_case_tac \\ rw [] \\ simp [bsi_cell_input_ok_def, cell_input_lt_def, cell_input_ge_def])
 \\ simp [blast_cell_input_def] \\ every_case_tac \\ rw [] \\ TRY drule_first \\ 
    fs [revEL_def, EVERY_EL, bsi_cell_input_ok_def, cell_input_lt_def]
QED

(* should be merged with above... blasterstate_ok unrolled... *)
Theorem blast_cell_input_array_cell_input_lt:
 !inp inps blast_s out tmpnum.
 blast_cell_input blast_s inp = ArrayInp inps /\
 cell_input_lt inp out /\ out <= tmpnum /\
 (!var inps. lookup var_cmp var blast_s.si = SOME (ArrayInp inps) ==> EVERY (\inp. cell_input_lt inp tmpnum) inps) ⇒
 EVERY (\inp. cell_input_lt inp tmpnum) inps
Proof
 Cases \\ rw [blast_cell_input_def]
 >- (Cases_on ‘v’ \\ fs [blast_cell_input_def] \\ rw [cell_input_lt_def, EVERY_MAP])
 >- (every_case_tac \\ fs [] \\ rw [cell_input_lt_def, EVERY_GENLIST])
 \\ every_case_tac \\ fs [] \\ Cases_on ‘v’ \\ rveq \\
    fs [cell_input_lt_def, var_lt_def] \\ drule_first \\ fs [revEL_def, EVERY_EL]
QED

Theorem blast_cell_input_array_bsi_cell_input_ok:
 !inp inps blast_s out tmpnum.
 blast_cell_input blast_s inp = ArrayInp inps /\
 (!var inps. lookup var_cmp var blast_s.si = SOME (ArrayInp inps) ==> EVERY (bsi_cell_input_ok out tmpnum) inps) ==>
 EVERY (bsi_cell_input_ok out tmpnum) inps
Proof
 Cases \\ rpt gen_tac
 >- (Cases_on ‘v’ \\ rw [blast_cell_input_def] \\ simp [EVERY_MAP, bsi_cell_input_ok_def, cell_input_lt_def, cell_input_ge_def])
 >- (simp [blast_cell_input_def] \\ every_case_tac \\ rw [] \\ simp [EVERY_GENLIST, bsi_cell_input_ok_def, cell_input_lt_def, cell_input_ge_def])
 \\ simp [blast_cell_input_def] \\ every_case_tac \\ rw [] \\ drule_first
QED

Theorem cell_inp_run_lt_cget_var_cong:
 ∀inp fext s s' n m.
 (∀var. var_lt var n ⇒ cget_var s' var = cget_var s var) ∧ cell_input_lt inp m ∧ m ≤ n ⇒
 cell_inp_run fext s' inp = cell_inp_run fext s inp
Proof
 Cases \\ rw [cell_inp_run_def, cell_input_lt_def] \\ drule_strip var_lt_le \\ simp []
QED
                                                                                               
Definition inps2n_def:
 inps2n fext s inps = sum_map v2n $ sum_mapM (λinp. sum_bind (cell_inp_run fext s inp) get_bool) inps
End

Theorem inps2n_lt:
 ∀inps fext s n. inps2n fext s inps = INR n ⇒ n < 2 ** LENGTH inps
Proof
 rw [inps2n_def, sum_map_INR, sum_mapM_EL] \\ metis_tac [v2n_lt]
QED

Theorem inps2n_nil:
 ∀fext s. inps2n fext s [] = INR 0
Proof
 rpt gen_tac \\ EVAL_TAC
QED

Theorem v2n_sing:
 ∀b. v2n [b] = if b then 1 else 0
Proof
 rw [v2n_def, bitify_reverse_map]
QED

Theorem inps2n_sing:
 ∀fext s inp b.
 cell_inp_run fext s inp = INR (CBool b) ⇒ inps2n fext s [inp] = INR (if b then 1 else 0)
Proof
 simp [inps2n_def, sum_mapM_def, sum_bind_def, get_bool_def, sum_map_INR, v2n_sing]
QED

Theorem inps2n_F:
 ∀fext s. inps2n fext s [ConstInp (CBool F)] = INR 0
Proof
 rpt gen_tac \\ EVAL_TAC
QED

Triviality zero_extend_suc:
 ∀l n. LENGTH l ≤ n ⇒ zero_extend (SUC n) l = F :: zero_extend n l
Proof
 rw [zero_extend_def, PAD_LEFT] \\ ‘SUC n − LENGTH l = SUC (n - LENGTH l)’ by decide_tac \\
 pop_assum (rewrite_tac o sing) \\ simp [GENLIST_CONS]
QED

Triviality length_dropwhile_sub_length:
 ∀l P. LENGTH (dropWhile P l) − LENGTH l = 0
Proof
 simp [LENGTH_dropWhile_LESS_EQ]
QED

Triviality fixwidth_dropWhile_F:
 ∀l. fixwidth (LENGTH l) (dropWhile ($<=> F) l) = l
Proof
 Induct \\ rw [fixwidth_def] \\ fs [] \\ qspecl_then [‘$<=> F’, ‘l’] assume_tac LENGTH_dropWhile_LESS_EQ
 >- (fs [zero_extend_suc, fixwidth_def] \\ every_case_tac \\ fs [length_dropwhile_sub_length, zero_extend_id])
 \\ fs [arithmeticTheory.ADD1]
QED

Triviality el_inps2n_lem:
 ∀inps fext s n i.
 inps2n fext s inps = INR n ∧ i < LENGTH inps ⇒
 cell_inp_run fext s (EL i inps) = INR $ CBool $ EL i (fixwidth (LENGTH inps) (n2v n))
Proof
 simp [inps2n_def, sum_map_INR] \\ rpt strip_tac \\ rveq \\ simp [n2v_v2n] \\ 
 fs [sum_mapM_EL] \\ drule_first \\ fs [sum_bind_INR, get_bool_INR] \\ rveq \\
 IF_CASES_TAC >- fs [EVERY_EL, fixwidth_F] \\ 
 qpat_x_assum ‘LENGTH _ = LENGTH _’ (assume_tac o GSYM) \\ simp [fixwidth_dropWhile_F]
QED

Theorem inps2n_append:
 ∀l1 l2 n fext s.
 inps2n fext s (l1 ++ l2) = INR n ⇔
 ∃n1 n2. inps2n fext s l1 = INR n1 ∧ inps2n fext s l2 = INR n2 ∧ n = n1*2**(LENGTH l2) + n2
Proof
 rw [inps2n_def] \\ fs [sum_map_INR, sum_mapM_append] \\ eq_tac \\ rw [v2n_append, PULL_EXISTS] \\
 imp_res_tac length_sum_mapM \\ simp []
QED

(* Too weak to be an eq currently *)
Theorem inps2n_INR:
 ∀inps s fext n.
 inps2n fext s inps = INR n ⇒
 EVERY (λinp. ∃b. cell_inp_run fext s inp = INR $ CBool b) inps
Proof
 rw [EVERY_EL] \\ drule_strip el_inps2n_lem \\ simp []
QED

Triviality inps2n_v2n_lem:
 ∀l s fext bs.
 (∀i. i < LENGTH l ⇒ cell_inp_run fext s (EL i l) = INR (CBool (EL i bs))) ∧ LENGTH bs = LENGTH l ⇒
 inps2n fext s l = INR (v2n bs)
Proof
 rw [inps2n_def, sum_map_INR, sum_mapM_EL] \\ qexists_tac ‘bs’ \\ rw [] \\ drule_first \\
 simp [sum_bind_def, get_bool_def]
QED

Triviality n2l_2_2pow_lem:
 ∀n a. a < 2**n ⇒ n2l 2 (a + 2 ** n) = if a = 0 then PAD_LEFT 0 (n + 1) [1] else PAD_RIGHT 0 n (n2l 2 a) ++ [1]
Proof
 (* Can be cleaned up probably, but I don't want to touch this proof right now... *)
 Induct >- simp [lt1, PAD_LEFT] \\ rpt strip_tac \\ simp [Once n2l_def] \\
 IF_CASES_TAC >- (fs [arithmeticTheory.EXP] \\ Cases_on ‘a’ \\ fs [] \\ Cases_on ‘n'’ \\ fs []) \\
 simp [arithmeticTheory.ZERO_EXP] \\ ‘(a + 2 ** SUC n) = (2 ** n * 2 + a)’ by fs [arithmeticTheory.EXP] \\
 pop_assum (rewrite_tac o sing) \\ DEP_REWRITE_TAC [arithmeticTheory.ADD_DIV_ADD_DIV] \\ simp [] \\
 first_x_assum (qspec_then ‘a DIV 2’ mp_tac) \\ impl_tac >- simp [arithmeticTheory.EXP2_LT] \\ strip_tac \\
 simp [] \\ CONV_TAC (RHS_CONV (REWRITE_CONV [Once n2l_def])) \\ simp [] \\
 Cases_on ‘a’ >- (simp [PAD_LEFT, GENLIST_CONS]) \\ simp [] \\ Cases_on ‘n'’ >- (simp [PAD_LEFT, PAD_RIGHT]) \\ simp [] \\
 simp [PAD_LEFT, PAD_RIGHT] \\ rw [] \\ Cases_on ‘n’ \\ fs [GENLIST_CONS]
QED

Triviality length_n2l_bound_lem:
 ∀a n. a ≠ 0 ∧ a < 2 ** n ⇒ LENGTH (n2l 2 a) ≤ n
Proof
 rpt gen_tac \\ Cases_on ‘n = 0’ >- simp [] \\
 simp [LENGTH_n2l] \\ rpt strip_tac \\ ‘a <= 2 ** n - 1’ by decide_tac \\ ‘0 < a’ by decide_tac \\
 drule_strip bitTheory.LOG2_LE_MONO \\ rfs [log2_twoexp_sub1, bitTheory.LOG2_def]
QED

Triviality fixwidth_sum_2pow_lem:
 ∀n a. a < 2**n ⇒ n2v (a + 2 ** n) = T :: fixwidth n (n2v a)
Proof
 rw [n2v_def, boolify_reverse_map, num_to_bin_list_def] \\
 drule_strip n2l_2_2pow_lem \\ rw []
 >- simp [PAD_LEFT, fixwidth_F, MAP_GENLIST, REVERSE_GENLIST, GENLIST_FUN_EQ]
 \\ simp [PAD_RIGHT, MAP_GENLIST, REVERSE_GENLIST] \\ rw [fixwidth_def, zero_extend_def, PAD_LEFT, GENLIST_FUN_EQ] \\
    drule_strip length_n2l_bound_lem \\ ‘LENGTH (n2l 2 a) = n’ by decide_tac \\ simp []
QED

Triviality fixwidth_sum_2pow: (* todo: rename to carry something *)
 ∀b a n. a < 2**n ∧ b < 2 ⇒ fixwidth n (n2v $ a + b * 2 ** n) = fixwidth n (n2v a)
Proof
 simp [lt2] \\ rpt strip_tac \\ simp [] \\ drule_strip fixwidth_sum_2pow_lem \\ simp [] \\ simp [fixwidth_def]
QED
                                                                                     
Triviality length_le4_lem:
 (∀l. LENGTH l = 1 ⇔ ∃e0. l = [e0]) ∧
 (∀l. LENGTH l = 2 ⇔ ∃e1 e0. l = [e1; e0]) ∧
 (∀l. LENGTH l = 3 ⇔ ∃e2 e1 e0. l = [e2; e1; e0]) ∧
 (∀l. LENGTH l = 4 ⇔ ∃e3 e2 e1 e0. l = [e3; e2; e1; e0])
Proof
 simp [LENGTH_EQ_NUM_compute, PULL_EXISTS]
QED

Theorem cellLUT_run_xor_lut_table:
 ∀in1 in2 in1' in2' fext s v.
 cell_inp_run fext s in1 = INR (CBool in1') ∧
 cell_inp_run fext s in2 = INR (CBool in2') ⇒
 cellLUT_run fext s [in1; in2] xor_lut_table = INR (CBool (in1' ≠ in2'))
Proof
 rw [cellLUT_run_def, sum_mapM_def, sum_map_def, sum_bind_def, get_bool_def, xor_lut_table_def] \\ metis_tac []
QED

Triviality EVERY_cell_inp_run_bool_lt_cset_var:
 ∀inps v fext s tmpnum.
 EVERY (λinp. ∃b. cell_inp_run fext s inp = INR (CBool b)) inps ∧
 EVERY (λinp. cell_input_lt inp tmpnum) inps ⇒
 EVERY (λinp. ∃b. cell_inp_run fext (cset_var s (NetVar tmpnum) v) inp = INR (CBool b)) inps
Proof
 rw [EVERY_MEM] \\ rpt drule_first \\
 Cases_on ‘inp’ \\ fs [cell_inp_run_def, cell_input_lt_def, cget_var_cset_var] \\
 Cases_on ‘v'’ \\ fs [var_lt_def]
QED

Theorem run_cells_xor:
 ∀inps1 inps2 fext bs tmpnum.
 LENGTH inps2 = LENGTH inps1 ∧
 EVERY (λinp. ∃b. cell_inp_run fext bs inp = INR (CBool b)) inps1 ∧
 EVERY (λinp. ∃b. cell_inp_run fext bs inp = INR (CBool b)) inps2 ∧
 EVERY (λinp. cell_input_lt inp tmpnum) inps1 ∧
 EVERY (λinp. cell_input_lt inp tmpnum) inps2 ⇒
 ∃bs'. sum_foldM (cell_run fext) bs (MAP2i (λi inp1 inp2. CellLUT (i + tmpnum) [inp1; inp2] xor_lut_table) inps1 inps2) = INR bs' ∧
       bs'.fbits = bs.fbits ∧
       (∀n. cget_var bs' (NetVar n) = if tmpnum ≤ n ∧ n < tmpnum + LENGTH inps1 then
                                       INR (CBool ((OUTR (get_bool (OUTR (cell_inp_run fext bs (EL (n - tmpnum) inps1)))))
                                            ≠
                                            (OUTR (get_bool (OUTR (cell_inp_run fext bs (EL (n - tmpnum) inps2)))))))

                                      else
                                       cget_var bs (NetVar n))
Proof
 Induct >- (Cases \\ simp [sum_foldM_def]) \\ gen_tac \\ Cases \\ simp [] \\ rpt strip_tac' \\
 qspecl_then [‘h’, ‘h'’] assume_tac cellLUT_run_xor_lut_table \\ drule_first \\
 simp [sum_foldM_def, sum_bind_def, cell_run_def] \\
 qmatch_goalsub_abbrev_tac ‘cset_var _ _ res’ \\
 qspecl_then [‘inps1’, ‘res’] assume_tac EVERY_cell_inp_run_bool_lt_cset_var \\ drule_first \\
 qspecl_then [‘t’, ‘res’] assume_tac EVERY_cell_inp_run_bool_lt_cset_var \\ drule_first \\
 unabbrev_all_tac \\
 qspecl_then [‘inps1’] assume_tac EVERY_cell_input_lt_le \\ drule_first \\
 disch_then (qspec_then ‘tmpnum + 1’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
 qspecl_then [‘t’] assume_tac EVERY_cell_input_lt_le \\ drule_first \\
 disch_then (qspec_then ‘tmpnum + 1’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
 drule_first \\ simp [combinTheory.o_DEF] \\
 ‘∀n. tmpnum + SUC n = n + (tmpnum + 1)’ by decide_tac \\ pop_assum (rewrite_tac o sing) \\
 simp [cset_var_fbits] \\ gen_tac \\
 ‘n < tmpnum ∨ n = tmpnum ∨ (tmpnum < n ∧ n < tmpnum + LENGTH inps1 + 1) ∨ tmpnum + LENGTH inps1 + 1 ≤ n’ by decide_tac
 >- simp [cget_var_cset_var]
 >- simp [cget_var_cset_var, get_bool_def]
 >- (simp [EL_CONS] \\ ‘PRE (n - tmpnum) = n - (tmpnum + 1)’ by decide_tac \\ simp [] \\
     fs [EVERY_EL] \\ ‘n − (tmpnum + 1) < LENGTH inps1 ∧ n - (tmpnum + 1) < LENGTH t’ by fs [] \\
     rpt drule_first \\ fs [cell_input_lt_cell_inp_run_cset_var])
 >- simp [cget_var_cset_var]
QED

Triviality EVERY_cell_input_lt_unchanged:
 ∀inps n fext s s'.
 EVERY (λinp. cell_input_lt inp n) inps ∧
 (∀inp. cell_input_lt inp n ⇒ cell_inp_run fext s' inp = cell_inp_run fext s inp) ⇒
 EVERY (λinp. cell_inp_run fext s' inp = cell_inp_run fext s inp) inps
Proof
 simp [EVERY_MEM]
QED

Triviality cell_inp_run_ConstInp:
 ∀fext s b. cell_inp_run fext s (ConstInp (CBool b)) = INR (CBool b)
Proof
 simp [cell_inp_run_def]
QED

(* Separate out proof of "static properties" in adder case, "dynamic properties" depends on the input lists being
   of equal length... *)
Theorem blast_cell_add4_correct_static_part:
 ∀n r tmpnum tmpnum' cin inps1 inps2 outs cout cells.
 blast_cell_add4 tmpnum cin inps1 inps2 = (tmpnum', outs, cout, cells) ∧
 LENGTH inps1 ≤ 4 ∧
 cell_input_lt cin tmpnum ∧ EVERY (\inp. cell_input_lt inp tmpnum) inps1 ∧ EVERY (\inp. cell_input_lt inp tmpnum) inps2 ⇒
 tmpnum ≤ tmpnum' ∧
 EVERY (λinp. cell_input_ge inp tmpnum) outs ∧
 EVERY (λinp. cell_input_lt inp tmpnum') outs ∧
 cell_input_lt cout tmpnum' ∧
 deterministic_netlist cells
Proof
 simp [Once blast_cell_add4_def, le4] \\ rpt strip_tac' \\ fs [length_le4_lem] \\ rveq \\ fs [] \\
 simp [EVERY_DEF, cell_input_ge_def, var_ge_def, cell_input_lt_def, var_lt_def] \\
 simp [EVERY_EL, deterministic_netlist_def, deterministic_cell_def, indexedListsTheory.EL_MAP2i]
QED

Theorem blast_cell_add_correct_static_part:
 ∀n r tmpnum tmpnum' cin inps1 inps2 outs cout cells.
 blast_cell_add tmpnum cin inps1 inps2 = (tmpnum', outs, cout, cells) ∧
 LENGTH inps1 = n*4 + r ∧ r < 4 ∧
 cell_input_lt cin tmpnum ∧ EVERY (\inp. cell_input_lt inp tmpnum) inps1 ∧ EVERY (\inp. cell_input_lt inp tmpnum) inps2 ⇒
 tmpnum ≤ tmpnum' ∧
 EVERY (λinp. cell_input_ge inp tmpnum) outs ∧
 EVERY (λinp. cell_input_lt inp tmpnum') outs ∧
 deterministic_netlist cells
Proof
 Induct
 >- (* base *)
 (simp [Once blast_cell_add_def, DROP_EQ_NIL] \\ rpt gen_tac \\
  IF_CASES_TAC >- simp [deterministic_netlist_def] \\
  rpt strip_tac' \\ fs [DROP_LENGTH_TOO_LONG, TAKE_LENGTH_TOO_LONG] \\
  pairarg_tac \\ fs [] \\ rveq \\
  drule_strip blast_cell_add4_correct_static_part \\ simp [EVERY_REVERSE, EVERY_TAKE])
 \\ (* step *)
 simp [Once blast_cell_add_def, DROP_EQ_NIL] \\ rpt strip_tac' \\
 qpat_x_assum ‘LENGTH _ = _’ mp_tac \\ ‘r + 4 * SUC n = 4 + (4 * n + r)’ by decide_tac \\
 pop_assum (rewrite_tac o sing) \\ once_rewrite_tac [LENGTH_EQ_SUM] \\ strip_tac \\ rveq \\

 Cases_on ‘l1 = []’ \\ fs [] \\ Cases_on ‘l2 = []’ \\ fs []
 >- (* length 4... *)
 (fs [length_le4_lem, blast_cell_add4_def] \\ rveq \\ fs [] \\
  simp [cell_input_ge_def, var_ge_def, cell_input_lt_def, var_lt_def] \\
  simp [EVERY_EL, deterministic_netlist_def, deterministic_cell_def, indexedListsTheory.EL_MAP2i])
 \\ (* all other lengths *)
 fs [DROP_APPEND, DROP_LENGTH_TOO_LONG, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] \\
 pairarg_tac \\ drule_strip blast_cell_add4_correct_static_part \\ simp [EVERY_REVERSE, EVERY_TAKE] \\
 strip_tac \\ every_case_tac >- (‘n = 0 ∧ r = 0’ by decide_tac \\ fs []) \\ fs [] \\
 pairarg_tac \\ drule_first \\ impl_tac >- (rpt conj_tac
 >- (match_mp_tac EVERY_cell_input_lt_le \\ asm_exists_tac \\ simp [])
 >- (qspec_then ‘inps2’ assume_tac EVERY_cell_input_lt_le \\ drule_first \\ simp [EVERY_DROP])) \\ strip_tac \\
 fs [] \\ rveq \\ simp [EVERY_APPEND, deterministic_netlist_append] \\ conj_tac
 >- (match_mp_tac EVERY_cell_input_ge_le \\ asm_exists_tac \\ simp [])
 \\ match_mp_tac EVERY_cell_input_lt_le \\ asm_exists_tac \\ simp []
QED

(* Works if only bool vars are present in goal *)        
fun Cases_on_all (asm, g) =
 (MAP_EVERY (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC o flip SPEC BOOL_CASES_AX) (free_vars g)) (asm, g);

Theorem blast_cell_add4_correct:
 ∀inps1 inps2 inps1' inps2' tmpnum tmpnum' cin cin' cout outs cells fext bs.
 blast_cell_add4 tmpnum cin inps1 inps2 = (tmpnum', outs, cout, cells) ∧
 inps2n fext bs inps1 = INR inps1' ∧ inps2n fext bs inps2 = INR inps2' ∧ inps2n fext bs [cin] = INR cin' ∧
 EVERY (\inp. cell_input_lt inp tmpnum) inps1 ∧ EVERY (\inp. cell_input_lt inp tmpnum) inps2 ∧ cell_input_lt cin tmpnum ∧
 inps1 ≠ [] ∧ LENGTH inps1 <= 4 ∧ LENGTH inps2 = LENGTH inps1 ⇒
 tmpnum' = tmpnum + LENGTH inps1 + 2 ∧
 LENGTH outs = LENGTH inps1 ∧
 EVERY (\inp. cell_input_lt inp tmpnum') outs ∧ cell_input_lt cout tmpnum' ∧
 ∃bs' outs' cout'. sum_foldM (cell_run fext) bs cells = INR bs' ∧
                   bs'.fbits = bs.fbits ∧
                   (∀var. var_lt var tmpnum ⇒ cget_var bs' var = cget_var bs var) ∧
                   inps2n fext bs' outs = INR outs' ∧
                   inps2n fext bs' [cout] = INR cout' ∧
                   outs' + 2**(LENGTH inps1)*cout' = inps1' + inps2' + cin'
Proof
 simp [Once blast_cell_add4_def, sum_foldM_append] \\ rpt strip_tac' \\

 imp_res_tac inps2n_INR \\
 drule_strip run_cells_xor \\ simp [sum_bind_def] \\

 ‘∀inp. cell_input_lt inp tmpnum ⇒ cell_inp_run fext bs' inp = cell_inp_run fext bs inp’ by
  (Cases \\ simp [cell_inp_run_def] \\ Cases_on ‘v’ >- (drule_strip cells_run_cget_var_RegVar \\ simp []) \\
   simp [cell_input_lt_def, var_lt_def]) \\

 qspec_then ‘inps1’ assume_tac EVERY_cell_input_lt_unchanged \\ drule_first \\
 qspec_then ‘inps2’ drule_strip EVERY_cell_input_lt_unchanged \\ drule_first \\

 rpt conj_tac
 >- simp [EVERY_REVERSE, EVERY_GENLIST, cell_input_lt_def, var_lt_def]
 >- simp [cell_input_lt_def, var_lt_def] \\

 fs [le4, length_le4_lem] \\ rfs [length_le4_lem] \\ rveq \\ fs [EVERY_DEF] \\

 simp [sum_foldM_def, cell_run_def, PAD_LEFT, sum_bind_def, sum_map_def, sum_mapM_def, cell_inp_run_ConstInp] \\
 simp [cell_inp_run_def, cget_fext_var_def, sum_bind_def, sum_map_def] \\
 simp [cellCarry4_run_def, get_bool_def, sum_bind_def, sum_map_def, sum_mapM_def, cset_var_fbits] \\
 simp [GSYM PULL_EXISTS] \\
 (conj_tac >- (rw [var_lt_def, cget_var_cset_var] \\
               Cases_on ‘var’ >- (drule_strip cells_run_cget_var_RegVar \\ simp []) \\ fs [var_lt_def])) \\
 simp [carry4_xor_def, carry4_muxcy_def, inps2n_def, sum_mapM_def, sum_map_def, sum_bind_def] \\
 simp [cell_inp_run_cset_var', cget_fext_var_def, sum_revEL_def, sum_EL_EL, get_bool_def, sum_map_def, sum_bind_def] \\

 fs [inps2n_def, sum_map_INR, sum_mapM_INR] \\ fs [sum_mapM_def] \\ fs [sum_bind_def, get_bool_def] \\ rveq \\
    
 EVAL_TAC \\ once_rewrite_tac [bitify_reverse_map] \\ EVAL_TAC \\
 Cases_on_all \\ EVAL_TAC
 (* CONV_TAC (LHS_CONV EVAL) \\ CONV_TAC (RHS_CONV EVAL) *)
QED

Triviality inps2n_cong:
 ∀inps fext s s' n.
 EVERY (λinp. cell_inp_run fext s' inp = cell_inp_run fext s inp) inps ∧
 inps2n fext s inps = INR n ⇒
 inps2n fext s' inps = INR n
Proof
 rw [EVERY_EL, inps2n_def, sum_map_INR, sum_mapM_EL]
QED
                  
Triviality inps2n_cong_REVERSE:
 ∀inps fext s s' n.
 EVERY (λinp. cell_inp_run fext s' inp = cell_inp_run fext s inp) inps ∧
 inps2n fext s (REVERSE inps) = INR n ⇒
 inps2n fext s' (REVERSE inps) = INR n
Proof
 metis_tac [EVERY_REVERSE, inps2n_cong]
QED

(* Well... cute induction by simply complete induction would have probably worked here... *)
Theorem blast_cell_add_correct:
 ∀n tmpnum tmpnum' cin cin' inps1 inps1' inps2 inps2' outs cout cells fext bs r.
 blast_cell_add tmpnum cin inps1 inps2 = (tmpnum', outs, cout, cells) ∧
 inps2n fext bs (REVERSE inps1) = INR inps1' ∧
 inps2n fext bs (REVERSE inps2) = INR inps2' ∧
 inps2n fext bs [cin] = INR cin' ∧
 cell_input_lt cin tmpnum ∧ EVERY (\inp. cell_input_lt inp tmpnum) inps1 ∧ EVERY (\inp. cell_input_lt inp tmpnum) inps2 ∧
 LENGTH inps1 = 4*n + r ∧ LENGTH inps2 = 4*n + r ∧ r < 4 ⇒
 tmpnum ≤ tmpnum' ∧
 LENGTH outs = LENGTH inps1 ∧
 ∃bs' outs' cout'. sum_foldM (cell_run fext) bs cells = INR bs' ∧
                   bs'.fbits = bs.fbits ∧
                   (∀var. var_lt var tmpnum ⇒ cget_var bs' var = cget_var bs var) ∧
                   inps2n fext bs' outs = INR outs' ∧
                   inps2n fext bs' [cout] = INR cout' ∧
                   outs' + 2**(LENGTH inps1)*cout' = inps1' + inps2' + cin'
Proof
 Induct
 >- (* Base *)
 (simp [Once blast_cell_add_def, DROP_EQ_NIL] \\ rpt gen_tac \\ IF_CASES_TAC
 >- (* len = 0 *)
 (rw [] \\ fs [inps2n_nil, REVERSE_DEF] \\ rw [sum_foldM_def])
 \\ (* len = 1, 2, 3 *)
 pairarg_tac \\ simp [] \\ reverse IF_CASES_TAC >- simp [] \\ rpt strip_tac' \\ fs [] \\ rveq \\
 fs [TAKE_LENGTH_TOO_LONG] \\ drule_strip blast_cell_add4_correct \\ simp [EVERY_REVERSE])

 \\ (* Step *)  
 simp [Once blast_cell_add_def, DROP_EQ_NIL] \\ rpt gen_tac \\ IF_CASES_TAC >- simp [] \\
 pairarg_tac \\ simp [] \\ IF_CASES_TAC
 >- (* len = 4 *)
 (last_x_assum kall_tac \\ rpt strip_tac' \\ fs [] \\ rveq \\
 ‘n = 0 ∧ r = 0’ by decide_tac \\ rveq \\ fs [TAKE_LENGTH_TOO_LONG] \\
 drule_strip blast_cell_add4_correct \\ simp [EVERY_REVERSE])

 \\ (* len > 4 *)
 rpt strip_tac' \\ qpat_x_assum ‘LENGTH inps1 = _’ mp_tac \\ qpat_x_assum ‘LENGTH inps2 = _’ mp_tac \\
 ‘r + 4 * SUC n = 4 + (4 * n + r)’ by decide_tac \\ pop_assum (rewrite_tac o sing) \\
 ntac 2 (disch_then (strip_assume_tac o ONCE_REWRITE_RULE [LENGTH_EQ_SUM])) \\
 rveq \\ qpat_x_assum ‘_ ≠ []’ kall_tac \\

 fs [REVERSE_APPEND, inps2n_append] \\
 fs [DROP_APPEND, DROP_LENGTH_NIL_rwt, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] \\
 
 drule_strip blast_cell_add4_correct \\ simp [EVERY_REVERSE, NOT_NIL_EQ_LENGTH_NOT_0] \\ strip_tac \\
 pairarg_tac \\ fs [] \\ rveq \\

 (* copied... *)
 ‘∀inp. cell_input_lt inp tmpnum ⇒ cell_inp_run fext bs' inp = cell_inp_run fext bs inp’ by
  (Cases \\ simp [cell_inp_run_def] \\ Cases_on ‘v’ >- (drule_strip cells_run_cget_var_RegVar \\ simp []) \\
   simp [cell_input_lt_def, var_lt_def]) \\
 (* end copy... *)

 qspec_then ‘l2’ assume_tac EVERY_cell_input_lt_unchanged \\ drule_first \\
 qspec_then ‘l2'’ assume_tac EVERY_cell_input_lt_unchanged \\ drule_first \\
 drule_first \\
 qspec_then ‘l2’ assume_tac inps2n_cong_REVERSE \\ drule_first \\
 qspec_then ‘l2'’ assume_tac inps2n_cong_REVERSE \\ drule_first \\
 drule_first \\ disch_then (qspec_then ‘r’ mp_tac) \\
 impl_tac >- (simp [] \\ rpt conj_tac \\ match_mp_tac EVERY_cell_input_lt_le \\ asm_exists_tac \\ simp []) \\ strip_tac \\

 simp [sum_foldM_append, sum_bind_def, inps2n_append] \\
 (* copied again... *)
 ‘∀inp. cell_input_lt inp (tmpnum + 6) ⇒ cell_inp_run fext bs'' inp = cell_inp_run fext bs' inp’ by
  (Cases \\ simp [cell_inp_run_def] \\ Cases_on ‘v’ >- (drule_strip cells_run_cget_var_RegVar \\ simp []) \\
   simp [cell_input_lt_def, var_lt_def]) \\
 (* end copy... *)
 qspec_then ‘outs4’ assume_tac EVERY_cell_input_lt_unchanged \\ drule_first \\
 drule_strip inps2n_cong \\ simp [] \\ conj_tac
 >- (rpt strip_tac \\ drule var_lt_le \\ disch_then (qspec_then ‘tmpnum + 6’ mp_tac) \\ simp [])
 >- (‘4 * n + (r + 4) = 4 + (4 * n + r)’ by decide_tac \\ pop_assum (rewrite_tac o sing) \\
    once_rewrite_tac [arithmeticTheory.EXP_ADD] \\ simp [])
QED

Theorem blast_cell_equal12_correct_static:
 blast_cell_equal12 tmpnum preveq lhs rhs = (tmpnum',cells,out) ∧
 LENGTH lhs ≤ 12 ∧ lhs ≠ [] ⇒
 tmpnum ≤ tmpnum' ∧
 cell_input_lt out tmpnum' ∧
 cell_input_ge out tmpnum ∧
 deterministic_netlist cells
Proof
 rewrite_tac [le12] \\ rpt strip_tac' \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\
 fs [blast_cell_equal12_def] \\
 fs [Ntimes blast_cell_equal_luts_def 4, blast_cell_equal_lut_def, take_drop_TAKE_DROP] \\ rveq \\
 every_case_tac \\ fs [] \\ rveq \\
 simp [deterministic_netlist_def, deterministic_cell_def, cell_input_lt_def, var_lt_def, cell_input_ge_def, var_ge_def]
QED

Theorem blast_cell_equalarray_correct_static:
 ∀lhs rhs tmpnum tmpnum' tmpnumbase cells out preveq.
 blast_cell_equalarray tmpnum preveq lhs rhs = (tmpnum', cells, out) ∧
 cell_input_lt preveq tmpnum ∧
 cell_input_ge preveq tmpnumbase ∧
 tmpnumbase ≤ tmpnum ⇒
 tmpnum ≤ tmpnum' ∧
 cell_input_lt out tmpnum' ∧
 cell_input_ge out tmpnumbase ∧
 deterministic_netlist cells
Proof
 gen_tac \\ completeInduct_on ‘LENGTH lhs’ \\ gen_tac \\ strip_tac \\ rpt gen_tac \\
 once_rewrite_tac [blast_cell_equalarray_def] \\
 IF_CASES_TAC >- (rw [deterministic_netlist_def, cell_input_lt_def, cell_input_ge_def] \\ simp []) \\
 simp [take_drop_TAKE_DROP] \\ rpt strip_tac' \\
 pairarg_tac \\ drule_strip blast_cell_equal12_correct_static \\
 impl_tac >- simp [LENGTH_TAKE_EQ] \\ strip_tac \\ fs [] \\
 every_case_tac >- (fs [] \\ rw [] \\ match_mp_tac cell_input_ge_le \\ asm_exists_tac \\ simp []) \\

 pairarg_tac \\
 first_x_assum (qspec_then ‘LENGTH (DROP 12 lhs)’ mp_tac) \\
 impl_tac >- (Cases_on ‘lhs’ \\ fs [LENGTH_DROP]) \\
 disch_then (qspec_then ‘DROP 12 lhs’ mp_tac) \\ impl_tac >- simp [] \\ disch_then drule_strip \\
 fs [] \\ rw [deterministic_netlist_append] \\
 match_mp_tac cell_input_ge_le \\ asm_exists_tac \\ simp []
QED

Triviality cell_inp_run_cleanup_lem:
 ∀inp n v0 v1 v2 v3 s fext.
 cell_input_lt inp n ⇒
 (cell_inp_run fext (cset_var s (NetVar n) v0) inp =
  cell_inp_run fext s inp) ∧
 (cell_inp_run fext (cset_var (cset_var s (NetVar n) v0) (NetVar (SUC n)) v1) inp =
  cell_inp_run fext s inp) ∧
 (cell_inp_run fext (cset_var (cset_var (cset_var s (NetVar n) v0) (NetVar (SUC n)) v1) (NetVar (SUC (SUC n))) v2) inp =
  cell_inp_run fext s inp) ∧
 (cell_inp_run fext (cset_var (cset_var (cset_var (cset_var s (NetVar n) v0) (NetVar (SUC n)) v1) (NetVar (SUC (SUC n))) v2) (NetVar (SUC (SUC (SUC n)))) v3) inp =
  cell_inp_run fext s inp)
Proof
 rpt strip_tac' \\
 DEP_REWRITE_TAC [cell_input_lt_cell_inp_run_cset_var] \\ rw [cell_input_lt_def] \\
 match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp []
QED

Theorem cell_run_CellLut_eq2:
 ∀in1 in2 s in1' in2' fext out.
 cell_inp_run fext s in1 = INR (CBool in1') ∧
 cell_inp_run fext s in2 = INR (CBool in2') ⇒
 cell_run fext s (CellLUT out [in1; in2] [[F; F]; [T; T]]) = INR (cset_var s (NetVar out) (CBool (in1' = in2')))
Proof
 EVAL_TAC \\ simp [] \\ EVAL_TAC \\ simp [rtlstate_component_equality] \\ metis_tac []
QED

Theorem cell_run_CellLut_eq4:
 ∀in1 in2 in3 in4 s in1' in2' in3' in4' fext out.
 cell_inp_run fext s in1 = INR (CBool in1') ∧
 cell_inp_run fext s in2 = INR (CBool in2') ∧
 cell_inp_run fext s in3 = INR (CBool in3') ∧
 cell_inp_run fext s in4 = INR (CBool in4') ⇒
 cell_run fext s (CellLUT out [in1; in2; in3; in4] [[F; F; F; F]; [F; F; T; T]; [T; T; F; F]; [T; T; T; T]]) = INR (cset_var s (NetVar out) (CBool (in1' = in2' ∧ in3' = in4')))
Proof
 EVAL_TAC \\ simp [] \\ EVAL_TAC \\ simp [rtlstate_component_equality] \\ metis_tac []
QED

Theorem cell_run_CellLut_eq6:
 ∀in1 in2 in3 in4 in5 in6 s in1' in2' in3' in4' in5' in6' fext out.
 cell_inp_run fext s in1 = INR (CBool in1') ∧
 cell_inp_run fext s in2 = INR (CBool in2') ∧
 cell_inp_run fext s in3 = INR (CBool in3') ∧
 cell_inp_run fext s in4 = INR (CBool in4') ∧
 cell_inp_run fext s in5 = INR (CBool in5') ∧
 cell_inp_run fext s in6 = INR (CBool in6') ⇒
 cell_run fext s (CellLUT out [in1; in2; in3; in4; in5; in6] [[F;F;F;F;F;F]; [F;F;F;F;T;T]; [F;F;T;T;F;F]; [F;F;T;T;T;T]; [T;T;F;F;F;F]; [T;T;F;F;T;T]; [T;T;T;T;F;F]; [T;T;T;T;T;T]]) = INR (cset_var s (NetVar out) (CBool (in1' = in2' ∧ in3' = in4' ∧ in5' = in6')))
Proof
 EVAL_TAC \\ simp [] \\ EVAL_TAC \\ simp [rtlstate_component_equality] \\ metis_tac []
QED

Theorem cell_run_Carry4_eq:
 ∀cin in0 in1 in2 in3 cin' in0' in1' in2' in3' fext s out cout.
 cell_inp_run fext s cin = INR (CBool cin') ∧
 cell_inp_run fext s in0 = INR (CBool in0') ∧
 cell_inp_run fext s in1 = INR (CBool in1') ∧
 cell_inp_run fext s in2 = INR (CBool in2') ∧
 cell_inp_run fext s in3 = INR (CBool in3') ⇒
 ∃out'. cell_run fext s (Carry4 out cout cin (REPLICATE 4 (ConstInp (CBool F))) [in3; in2; in1; in0]) =
        INR (cset_var (cset_var s (NetVar cout) (CArray [in3' ∧ in2' ∧ in1' ∧ in0' ∧ cin';
                                                         in2' ∧ in1' ∧ in0' ∧ cin';
                                                         in1' ∧ in0' ∧ cin';
                                                         in0' ∧ cin'])) (NetVar out) out')
Proof
 rpt strip_tac \\ EVAL_TAC \\ simp [] \\ EVAL_TAC \\ simp [rtlstate_component_equality]
QED

fun cell_run_Carry4_tac (g as (asl,w)) = let
 val cell_run_tm = find_term is_cell_run w
in
 mp_tac (PART_MATCH' (lhs o snd o strip_exists o rand) cell_run_Carry4_eq cell_run_tm) g
end

fun cell_run_CellLut_tac (g as (asl,w)) = let
 val cell_run_tm = find_term is_cell_run w
 val vars = cell_run_tm |> rand |> rator |> rand |> listSyntax.dest_list |> fst
 val th = case (length vars) of 2 => cell_run_CellLut_eq2 | 4 => cell_run_CellLut_eq4 | _ => cell_run_CellLut_eq6
 val s = cell_run_tm |> rator |> rand
in
 assume_tac (SPECL (vars @ [s]) th) g
end

val blast_luts_tac = (cell_run_CellLut_tac \\ rfs [cell_inp_run_cleanup_lem] \\
                      drule_first \\ simp [sum_bind_def] \\ pop_assum kall_tac);

val blast_carry_tac = (simp [PAD_LEFT] \\ cell_run_Carry4_tac \\
                       simp [cell_inp_run_cset_var, cell_inp_run_ConstInp, cell_inp_run_cleanup_lem] \\
                       strip_tac \\ simp [] \\ pop_assum kall_tac);

Theorem blast_cell_equal12_correct:
 blast_cell_equal12 tmpnum preveq lhs rhs = (tmpnum', cells, out) ∧
 cell_input_lt preveq tmpnum ∧
 cell_inp_run fext bs preveq = INR (CBool preveq') ∧
 LENGTH lhs ≤ 12 ∧ lhs ≠ [] ∧
 LENGTH rhs = LENGTH lhs ∧
 LENGTH b = LENGTH lhs ∧
 LIST_REL (λinp1 inp2. cell_inp_run fext bs inp1 = INR (CBool inp2)) lhs b ∧
 EVERY (λinp. cell_input_lt inp tmpnum) lhs ∧
 LENGTH b' = LENGTH rhs ∧
 LIST_REL (λinp1 inp2. cell_inp_run fext bs inp1 = INR (CBool inp2)) rhs b' ∧
 EVERY (λinp. cell_input_lt inp tmpnum) rhs ⇒
 tmpnum ≤ tmpnum' ∧
 ∃bs'. sum_foldM (cell_run fext) bs cells = INR bs' ∧
       cell_inp_run fext bs' out =
       INR (CBool ((LIST_REL (λinp1 inp2. cell_inp_run fext bs inp1 = cell_inp_run fext bs inp2) lhs rhs) ∧ preveq')) ∧
       (∀inp. cell_input_lt inp tmpnum ⇒ cell_inp_run fext bs' inp = cell_inp_run fext bs inp)
Proof
 rewrite_tac [le12] \\ rpt strip_tac' \\ rfs [] \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\
 fs [blast_cell_equal12_def] \\
 fs [Ntimes blast_cell_equal_luts_def 4, blast_cell_equal_lut_def, take_drop_TAKE_DROP] \\ rveq \\

 TRY (CHANGED_TAC every_case_tac \\ fs [cell_inp_run_ConstInp] \\ rveq) \\
 simp [sum_foldM_def, flat_zip_def, sum_bind_INR] \\
 rpt blast_luts_tac \\
 TRY blast_carry_tac \\
 
 TRY (conj_tac >- (simp [cell_inp_run_cset_var'] \\ EVAL_TAC \\ rewrite_tac [CONJ_ASSOC]) \\
      Cases \\ rw [cell_inp_run_def, cget_var_cset_var, cell_input_lt_def, var_lt_def])
QED

Triviality LENGTH_TAKE_less:
 ∀l n. LENGTH l ≤ n ⇒ LENGTH (TAKE n l) = LENGTH l
Proof
 simp [LENGTH_TAKE_EQ]
QED

Theorem blast_cell_equalarray_correct:
 ∀lhs rhs b b' tmpnum tmpnum' cells out preveq preveq' fext bs.
 blast_cell_equalarray tmpnum preveq lhs rhs = (tmpnum', cells, out) ∧
 cell_input_lt preveq tmpnum ∧
 cell_inp_run fext bs preveq = INR (CBool preveq') ∧
 LENGTH rhs = LENGTH lhs ∧
 LENGTH b = LENGTH lhs ∧
 LIST_REL (λinp1 inp2. cell_inp_run fext bs inp1 = INR (CBool inp2)) lhs b ∧
 EVERY (λinp. cell_input_lt inp tmpnum) lhs ∧
 LENGTH b' = LENGTH rhs ∧
 LIST_REL (λinp1 inp2. cell_inp_run fext bs inp1 = INR (CBool inp2)) rhs b' ∧
 EVERY (λinp. cell_input_lt inp tmpnum) rhs  ⇒
 tmpnum ≤ tmpnum' ∧
 ∃bs'. sum_foldM (cell_run fext) bs cells = INR bs' ∧
       cell_inp_run fext bs' out =
       INR (CBool ((∀i. i < LENGTH lhs ⇒ cell_inp_run fext bs (EL i lhs) = cell_inp_run fext bs (EL i rhs)) ∧ preveq')) ∧
       (∀inp. cell_input_lt inp tmpnum ⇒ cell_inp_run fext bs' inp = cell_inp_run fext bs inp)
Proof
 gen_tac \\ completeInduct_on ‘LENGTH lhs’ \\ simp [Once blast_cell_equalarray_def] \\
 rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ IF_CASES_TAC >- (rw [sum_foldM_def, cell_inp_run_def] \\ simp []) \\
 simp [take_drop_TAKE_DROP] \\ rpt strip_tac' \\ pairarg_tac \\ drule_strip blast_cell_equal12_correct \\
 disch_then (qspecl_then [‘TAKE 12 b'’, ‘TAKE 12 b’] mp_tac) \\
 impl_tac >- simp [LENGTH_TAKE_EQ, rich_listTheory.EVERY2_TAKE, EVERY_TAKE] \\ strip_tac \\
 every_case_tac \\ fs [] >- (rveq \\ fs [DROP_EQ_NIL] \\ simp [LIST_REL_EL_EQN, LENGTH_TAKE_less, EL_TAKE]) \\
 pairarg_tac \\ first_x_assum (qspec_then ‘LENGTH (DROP 12 lhs)’ mp_tac) \\
 impl_tac >- (Cases_on ‘lhs’ \\ fs [LENGTH_DROP]) \\ disch_then (qspec_then ‘DROP 12 lhs’ mp_tac) \\
 impl_tac >- simp [] \\
 drule_strip blast_cell_equal12_correct_static \\ impl_tac >- simp [LENGTH_TAKE_EQ] \\ strip_tac \\
 drule_strip blast_cell_equalarray_correct_static \\
 disch_then drule_strip \\ disch_then (qspecl_then [‘DROP 12 b’, ‘DROP 12 b'’] mp_tac) \\
 impl_tac >- (rw [] \\
              TRY (match_mp_tac rich_listTheory.EVERY2_DROP \\ irule EVERY2_MEM_MONO \\ asm_exists_any_tac \\
                   Cases \\ rw [MEM_ZIP] \\ fs [EVERY_EL]) \\
              TRY (match_mp_tac EVERY_DROP \\ match_mp_tac EVERY_cell_input_lt_le \\ asm_exists_tac \\ simp [])) \\
 strip_tac \\ fs [] \\ rveq \\ simp [sum_foldM_append, sum_bind_def] \\
 reverse conj_tac >- metis_tac [cell_input_lt_le] \\
 fs [DROP_EQ_NIL] \\ simp [LIST_REL_EL_EQN, LENGTH_TAKE_EQ, EL_DROP, EL_TAKE] \\ eq_tac
 >- (strip_tac \\ simp [] \\ rpt strip_tac \\ Cases_on ‘i < 12’ >- simp [] \\
     rpt (first_x_assum (qspec_then ‘i - 12’ mp_tac)) \\ simp [] \\ rpt strip_tac \\
     fs [EVERY_EL] \\ metis_tac [cell_input_lt_le])
 >- (strip_tac \\ simp [] \\ rpt strip_tac \\ first_x_assum (qspec_then ‘i + 12’ mp_tac) \\ simp [] \\
     fs [EVERY_EL] \\ metis_tac [cell_input_lt_le])
QED

Theorem cell2_run_bad_types:
 (∀v bs. cell2_run CAnd (CArray bs) v = INL TypeError) ∧
 (∀v bs. cell2_run CAnd v (CArray bs) = INL TypeError) ∧
 (∀v bs. cell2_run COr (CArray bs) v = INL TypeError) ∧
 (∀v bs. cell2_run COr v (CArray bs) = INL TypeError) ∧
 (∀v b. cell2_run CAdd (CBool b) v = INL TypeError) ∧
 (∀v b. cell2_run CAdd v (CBool b) = INL TypeError)
Proof
 rpt conj_tac \\ Cases \\ simp [cell2_run_def]
QED

Theorem bsi_cell_input_ok_cell_inp_run_cset_var_bool:
 ∀fext s inp v v' out tmpnum.
 cell_inp_run fext s inp = INR v ∧
 bsi_cell_input_ok out tmpnum inp ∧
 out < tmpnum ⇒
 cell_inp_run fext (cset_var s (NetVar out) v') inp = INR v
Proof
 rw [bsi_cell_input_ok_def] \\
 Cases_on ‘inp’ \\ fs [cell_inp_run_def, sum_bind_INR] \\ rw [cget_var_cset_var] \\ fs [cell_input_lt_def, cell_input_ge_def, var_lt_def, var_ge_def]
QED

Theorem bsi_cell_input_ok_cell_inp_run_cset_var_array:
 ∀fext s inps i v out tmpnum.
 EVERY (bsi_cell_input_ok out tmpnum) inps ∧
 i < LENGTH inps ∧
 out < tmpnum ⇒
 cell_inp_run fext (cset_var s (NetVar out) v) (EL i inps) = cell_inp_run fext s (EL i inps)
Proof
 rpt strip_tac \\ Cases_on ‘EL i inps’ \\
 simp [cell_inp_run_def, cget_var_cset_var] \\ rw [] \\ metis_tac [EVERY_output_not_in_si_not_NetVar]
QED

Theorem bsi_cell_input_ok_cell_inp_run_cset_var:
 ∀inp fext s out tmpnum v.
 bsi_cell_input_ok out tmpnum inp ∧ out < tmpnum ⇒
 cell_inp_run fext (cset_var s (NetVar out) v) inp = cell_inp_run fext s inp
Proof
 rw [bsi_cell_input_ok_def]
 >- simp [cell_input_lt_cell_inp_run_cset_var]
 \\ Cases_on ‘inp’ \\ rw [cell_inp_run_def, cget_var_cset_var] \\ fs [cell_input_ge_def, var_ge_def]
QED

Theorem blast_rel_cset_var_NetVar_bool:
 !fext si tmpnum s bs b out.
 blast_rel fext si tmpnum s bs ∧
 out < tmpnum ∧
 (∀var inps. lookup var_cmp var si = SOME (ArrayInp inps) ⇒
             EVERY (bsi_cell_input_ok out tmpnum) inps) ∧
 (∀var inp. lookup var_cmp var si = SOME (BoolInp inp) ⇒
            bsi_cell_input_ok out tmpnum inp) ⇒
 lookup var_cmp (NetVar out) si = NONE ==>
 blast_rel fext si tmpnum (cset_var s (NetVar out) (CBool b))
                          (cset_var bs (NetVar out) (CBool b))
Proof
 rw [blast_rel_def, cset_var_fbits, cget_var_cset_var] \\ 
 IF_CASES_TAC >- simp [] \\ drule_first \\ rpt TOP_CASE_TAC \\ fs [] \\ rpt strip_tac \\ drule_first
 >- (drule_strip bsi_cell_input_ok_cell_inp_run_cset_var \\ simp [])
 \\ fs [EVERY_EL] \\ first_x_assum (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
 drule_strip bsi_cell_input_ok_cell_inp_run_cset_var \\ simp []
QED

(*Theorem blast_rel_cset_var_NetVar_array:
 !fext si tmpnum s bs b out.
 blast_rel fext si tmpnum s bs ∧
 out < tmpnum ∧
 (∀var inps. lookup var_cmp var si = SOME (ArrayInp inps) ⇒
             EVERY (bsi_cell_input_ok out tmpnum) inps) ∧
 (∀var inp. lookup var_cmp var si = SOME (BoolInp inp) ⇒
            bsi_cell_input_ok out tmpnum inp) ⇒
 lookup var_cmp (NetVar out) si = NONE ==>
 blast_rel fext si tmpnum (cset_var s (NetVar out) (CBool b))
                          (cset_var bs (NetVar out) (CBool b))
Proof
 rw [blast_rel_def, cset_var_fbits, cget_var_cset_var] \\ 
 IF_CASES_TAC >- simp [] \\ drule_first \\ rpt TOP_CASE_TAC \\ fs [] \\ rpt strip_tac \\ drule_first
 >- (drule_strip bsi_cell_input_ok_cell_inp_run_cset_var \\ simp [])
 \\ fs [EVERY_EL] \\ first_x_assum (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
 drule_strip bsi_cell_input_ok_cell_inp_run_cset_var \\ simp []
QED*)

Theorem blast_rel_cset_var_cset_var_bool:
 ∀fext si tmpnum tmpnum' s bs out b.
 blast_rel fext si tmpnum s bs ∧
 blasterstate_ok si tmpnum tmpnum' ∧
 lookup var_cmp (NetVar out) si = NONE ∧
 out < tmpnum ∧
 (∀var inps. lookup var_cmp var si = SOME (ArrayInp inps) ⇒ EVERY (bsi_cell_input_ok out tmpnum) inps) ∧
 (∀var inp. lookup var_cmp var si = SOME (BoolInp inp) ⇒ bsi_cell_input_ok out tmpnum inp) ⇒
 blast_rel fext si tmpnum (cset_var s (NetVar out) (CBool b)) (cset_var bs (NetVar out) (CBool b))
Proof
 fs [blast_rel_def, blasterstate_ok_def, cset_var_fbits, cget_var_cset_var] \\ rpt strip_tac \\ rw [] \\
 drule_first \\ rpt TOP_CASE_TAC \\ fs []
 >- (drule_first \\ drule_strip bsi_cell_input_ok_cell_inp_run_cset_var \\ simp [])
 \\ drule_first \\ fs [EVERY_EL] \\ rpt strip_tac \\ rpt (first_x_assum (qspec_then ‘i’ mp_tac)) \\ simp [] \\
    rpt strip_tac \\ drule_strip bsi_cell_input_ok_cell_inp_run_cset_var \\ simp []
QED

Definition bsi_inp_trans_ok_def:
 (bsi_inp_trans_ok out tmpnum (ArrayInp inps) ⇔ EVERY (bsi_cell_input_ok out tmpnum) inps) ∧
 (bsi_inp_trans_ok out tmpnum (BoolInp inp) ⇔ bsi_cell_input_ok out tmpnum inp)
End

Theorem blast_cell_correct:
 !cell blast_s blast_s' nl tmpnum.
 blast_cell blast_s cell = (blast_s', nl) /\

 deterministic_cell cell /\
 cell_ok 0 tmpnum cell /\
 cell_covered_by_extenv blast_s.extenv cell /\

 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum ==>
 blast_s'.extenv = blast_s.extenv /\
 blasterstate_ok blast_s'.si tmpnum blast_s'.tmpnum /\
 deterministic_netlist nl ∧

 ((!var inp out. lookup var_cmp var blast_s.si = SOME inp ∧ MEM out (cell_output cell) ==>
                 bsi_inp_trans_ok out tmpnum inp) ==>
  (!var inp out. lookup var_cmp var blast_s'.si = SOME inp ∧ MEM out (cell_output cell) ==>
                 bsi_inp_trans_ok out tmpnum inp)) ∧
 (!reg i. lookup var_cmp (RegVar reg i) blast_s'.si = lookup var_cmp (RegVar reg i) blast_s.si) /\
 (!n. ~MEM n (cell_output cell) ==> lookup var_cmp (NetVar n) blast_s'.si = lookup var_cmp (NetVar n) blast_s.si) /\

 (!fext s s' bs.
  cell_run fext s cell = INR s' /\ rtltype_extenv_n blast_s.extenv fext /\ 
  blast_rel fext blast_s.si tmpnum s bs /\
  (∀out. MEM out (cell_output cell) ⇒ lookup var_cmp (NetVar out) blast_s.si = NONE) /\
  (!var inps out. lookup var_cmp var blast_s.si = SOME (ArrayInp inps) ∧ MEM out (cell_output cell) ==>
                  EVERY (bsi_cell_input_ok out tmpnum) inps) ∧
  (!var inp out. lookup var_cmp var blast_s.si = SOME (BoolInp inp) ∧ MEM out (cell_output cell) ==>
                 bsi_cell_input_ok out tmpnum inp) ==>
  ?bs'. sum_foldM (cell_run fext) bs nl = INR bs' /\ blast_rel fext blast_s'.si tmpnum s' bs')
Proof
 Cases \\ rewrite_tac [deterministic_cell_def, cell_ok_def, cell_covered_by_extenv_def]

 >- (* Cell1 *)
 (rename1 `Cell1 t out in1` \\ Cases_on `t` \\
 simp [blast_cell_def, blast_cell_bitwise_def] \\ rpt gen_tac \\ TOP_CASE_TAC \\ rpt strip_tac' \\ rveq

 >- (simp [deterministic_netlist_def, deterministic_cell_def] \\ rpt strip_tac' \\
    fs [sum_foldM_def, cell_run_def, sum_bind_INR, cell_output_ok_def, cell_output_def] \\
    drule_strip blast_cell_inp_run_correct_bool \\ simp [] \\
    strip_tac \\ fs [cell1_run_def] \\ rveq \\
    drule_strip blast_rel_cset_var_cset_var_bool \\ simp []) \\

 fs [blaster_new_names_def] \\ rveq \\ simp [] \\
 rpt conj_tac \\ rpt strip_tac
 >- simp [blasterstate_ok_insert]
 >- simp [deterministic_netlist_def, EVERY_EL, deterministic_cell_def]
 >- (rfs [blasterstate_ok_def, lookup_insert_var_cmp, cell_output_ok_def, cell_output_def] \\ every_case_tac
     >- rw [EVERY_GENLIST, bsi_inp_trans_ok_def, bsi_cell_input_ok_def, cell_input_lt_def, cell_input_ge_def, var_lt_def, var_ge_def]
     >- metis_tac [])
 >- (fs [blasterstate_ok_def, lookup_insert_var_cmp, cell_output_def])
 >- (fs [blasterstate_ok_def, lookup_insert_var_cmp, cell_output_def]) \\

 fs [cell_run_def, sum_bind_INR, cell_output_ok_def, cell_output_def] \\

 drule_strip blast_cell_inp_run_correct_array \\ simp [] \\ strip_tac \\
 fs [cell1_run_def] \\ rveq \\
 drule_strip blast_cell_input_SOME \\
 drule_strip cell1_bitwise_correct \\
 fs [blast_rel_def, cset_var_fbits, cget_var_cset_var] \\ rpt strip_tac \\
 IF_CASES_TAC >- fs [blasterstate_ok_def, lookup_insert_var_cmp, cell_inp_run_def, EL_MAP] \\

 fs [blasterstate_ok_def, lookup_insert_var_cmp] \\
 drule_first \\ pop_assum mp_tac \\ rpt TOP_CASE_TAC
 >- (first_assum (qspec_then `VarInp var NONE` mp_tac) \\
    impl_tac >- (simp [cell_input_lt_def] \\ match_mp_tac var_lt_le \\
                asm_exists_tac \\ simp []) \\
    rpt strip_tac \\ fs [cell_inp_run_def, sum_bind_def, sum_bind_INR, cget_fext_var_def] \\
    rpt drule_first \\ simp []) \\

 strip_tac \\ rw [] \\
 first_x_assum (qspec_then `i` mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
 first_x_assum (qspec_then `EL i inps` mp_tac) \\
 impl_tac >- (drule_first \\ fs [EVERY_EL] \\
              first_x_assum (qspec_then `i` mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
              first_x_assum irule \\ simp [] \\ asm_exists_tac) \\
 simp [cell_inp_run_def])

 >- (* Cell2 *)
 (rename1 `Cell2 t out in1 in2` \\ Cases_on `t`

 \\ (* CAnd and COr *)
 TRY (simp [blast_cell_def, blast_cell_bitwise_def] \\ rpt gen_tac \\ rpt TOP_CASE_TAC \\ rpt strip_tac' \\ rveq
 >- (* bool, bool *)
 (simp [deterministic_netlist_def, deterministic_cell_def] \\
  simp [sum_foldM_def, cell_run_def, sum_bind_INR, cell_output_ok_def, cell_output_def] \\ rpt strip_tac' \\
  qspec_then ‘in1’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
  qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
  fs [cell_output_ok_def] \\ rpt strip_tac' \\ fs [cell2_run_def] \\ rveq \\
  drule_strip blast_rel_cset_var_cset_var_bool \\ simp [])

 \\ (* non bool *)
 simp [deterministic_netlist_def, deterministic_cell_def] \\
 simp [sum_foldM_def, cell_run_def, sum_bind_INR, cell_output_def] \\ rpt strip_tac' \\
 drule_strip blast_cell_inp_run_correct_array \\ fs [cell_output_ok_def] \\ strip_tac \\
 fs [cell2_run_bad_types])

 >- (* Equal *)
 (simp [blast_cell_def, blast_cell_equal_def] \\ rpt gen_tac \\ every_case_tac \\ rpt strip_tac' \\ rveq
 >- (* bool, bool *)
 (simp [deterministic_netlist_def, deterministic_cell_def, sum_foldM_def, cell_run_def, sum_bind_INR] \\
  rpt strip_tac' \\
  qspec_then ‘in1’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
  qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
  fs [cell_output_ok_def] \\ rpt strip_tac \\ rveq \\
  fs [cell_output_def, cell2_run_def] \\ rveq \\
  drule_strip blast_rel_cset_var_cset_var_bool \\ simp [])

 >- (* bool, array *)
 (rw [sum_foldM_def, cell_run_def, sum_bind_INR, deterministic_netlist_def] \\
 drule_strip blast_cell_inp_run_correct_bool \\ drule_strip blast_cell_inp_run_correct_array \\
 fs [cell_output_ok_def] \\ rpt strip_tac \\ rveq \\ fs [cell2_run_def])

 >- (* array, bool (same as bool, array case) *)
 (rw [sum_foldM_def, cell_run_def, sum_bind_INR, deterministic_netlist_def] \\
 drule_strip blast_cell_inp_run_correct_bool \\ drule_strip blast_cell_inp_run_correct_array \\
 fs [cell_output_ok_def] \\ rpt strip_tac \\ rveq \\ fs [cell2_run_def])

 >- (* array, array *)
 (pairarg_tac \\ drule_strip blast_cell_equalarray_correct_static \\
  disch_then (qspec_then ‘blast_s.tmpnum’ mp_tac) \\ impl_tac >- simp [cell_input_lt_def, cell_input_ge_def] \\
  strip_tac \\ fs [] \\ rveq \\ simp [] \\ rpt conj_tac
 >- (fs [blasterstate_ok_def, insert_thm_var_cmp, lookup_insert_var_cmp] \\ rw [] \\ simp []
     >- (drule_first \\ match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])
     \\ drule_first \\ match_mp_tac EVERY_cell_input_lt_le \\ asm_exists_tac \\ simp [])
 >- (fs [cell_output_def, blasterstate_ok_def, lookup_insert_var_cmp] \\ strip_tac \\ rw []
     >- (simp [bsi_inp_trans_ok_def, bsi_cell_input_ok_def] \\ disj2_tac \\
         match_mp_tac cell_input_ge_le \\ asm_exists_tac \\ simp [])
     >- drule_first)
 >- fs [blasterstate_ok_def, lookup_insert_var_cmp]
 >- fs [cell_output_def, blasterstate_ok_def, lookup_insert_var_cmp] \\

 simp [cell_run_def, sum_bind_INR] \\ rpt strip_tac \\
 qspec_then ‘in1’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
 qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
 fs [cell_output_ok_def] \\ rpt strip_tac \\ rveq \\
 qspec_then ‘in1’ assume_tac blast_cell_input_SOME \\ drule_first \\
 qspec_then ‘in2’ assume_tac blast_cell_input_SOME \\ drule_first \\
 fs [cell2_run_def, sum_bind_INR, sum_check_INR] \\ rveq \\
 drule_strip blast_cell_equalarray_correct \\ simp [cell_input_lt_def, cell_inp_run_def] \\
 disch_then (qspecl_then [‘b'’, ‘b’, ‘fext’, ‘bs’] mp_tac) \\ impl_tac >- simp [LIST_REL_EL_EQN] \\ strip_tac \\
 fs [blast_rel_def, cset_var_fbits, cget_var_cset_var] \\
 conj_tac >- (drule_strip run_cells_deterministic_netlist \\ simp []) \\
 rpt strip_tac \\ drule_first \\ rw []
 >- (fs [blasterstate_ok_def, lookup_insert_var_cmp] \\ reverse eq_tac >- metis_tac [] \\
     strip_tac \\ rewrite_tac [GSYM LIST_REL_eq, LIST_REL_EL_EQN] \\ rw [])
 \\ rpt TOP_CASE_TAC
 >- (fs [blasterstate_ok_def, lookup_insert_var_cmp]
     >- (first_x_assum (qspec_then ‘VarInp var NONE’ mp_tac) \\
         simp [cell_input_lt_def, cell_inp_run_def] \\
         impl_tac >- (match_mp_tac var_lt_le \\ asm_exists_tac \\ simp []) \\ simp [])
     >- (drule_last \\ first_x_assum (qspec_then ‘inp’ mp_tac) \\
         impl_tac >- (match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp []) \\ simp []))
 >- (fs [blasterstate_ok_def, lookup_insert_var_cmp] \\
     drule_last \\ fs [EVERY_EL])))

 >- (* CAdd case *)
 (simp [blast_cell_def] \\ rpt gen_tac \\ every_case_tac \\ rpt strip_tac' \\ rveq \\

 TRY (rw [sum_foldM_def, cell_run_def, sum_bind_INR, deterministic_netlist_def] \\
      drule_strip blast_cell_inp_run_correct_bool \\ fs [cell_output_ok_def] \\ strip_tac \\
      fs [cell2_run_bad_types] \\ NO_TAC) \\

 simp [cell_output_def] \\ pairarg_tac \\ fs [] \\ rveq \\ simp [] \\
 qspecl_then [‘LENGTH l'’, ‘4’] mp_tac arithmeticTheory.DA \\ impl_tac >- simp [] \\ strip_tac \\
 qspec_then ‘in1’ assume_tac blast_cell_input_SOME \\ drule_first \\
 qspec_then ‘in2’ assume_tac blast_cell_input_SOME \\ drule_first \\
 drule_strip blast_cell_add_correct_static_part \\
 rewrite_tac [LENGTH_REVERSE, cell_input_lt_def, EVERY_REVERSE] \\
 disch_then drule_strip \\

 rpt conj_tac
 >- (fs [blasterstate_ok_def, insert_thm_var_cmp, lookup_insert_var_cmp] \\ rw [] \\ simp [] \\ drule_first
     >- (match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])
     \\ irule EVERY_cell_input_lt_le \\ asm_exists_any_tac \\ simp [])
 >- simp []
 >- (fs [blasterstate_ok_def, lookup_insert_var_cmp] \\ strip_tac \\ rpt gen_tac \\ IF_CASES_TAC
     >- (rw [] \\ simp [bsi_inp_trans_ok_def] \\
         irule EVERY_MONOTONIC \\ qpat_x_assum ‘EVERY _ inps’ kall_tac \\ asm_exists_any_tac \\
         rw [bsi_cell_input_ok_def] \\ disj2_tac \\ match_mp_tac cell_input_ge_le \\ asm_exists_tac \\ simp [])
     >- (rw [] \\ drule_first))
 >- fs [blasterstate_ok_def, lookup_insert_var_cmp]
 >- fs [blasterstate_ok_def, lookup_insert_var_cmp] \\

 rpt strip_tac' \\ fs [cell_run_def, sum_bind_INR] \\
 drule_strip blast_cell_inp_run_correct_array \\
 qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
 rpt (impl_tac >- fs [cell_output_ok_def] \\ strip_tac) \\ rveq \\
 fs [cell2_run_def, sum_bind_INR, sum_check_INR] \\ rveq \\
 drule_strip inps2n_v2n_lem \\ qspec_then ‘l’ assume_tac inps2n_v2n_lem \\ drule_first \\
 qspecl_then [‘fext’, ‘bs’] assume_tac inps2n_F \\
 rfs [] \\ drule_strip blast_cell_add_correct \\
 rewrite_tac [REVERSE_REVERSE, EVERY_REVERSE, LENGTH_REVERSE, cell_input_lt_def] \\
 disch_then drule_strip \\ simp [] \\

 fs [blast_rel_def, blasterstate_ok_def, cset_var_fbits, cget_var_cset_var] \\ rpt strip_tac \\ IF_CASES_TAC

 >- (rw [lookup_insert_var_cmp] \\
    qspec_then ‘outs’ assume_tac el_inps2n_lem \\ drule_first \\ disch_then (qspec_then ‘i’ mp_tac) \\
    simp [] \\ strip_tac \\
    drule_strip inps2n_lt \\ qspec_then ‘outs’ assume_tac inps2n_lt \\ drule_first \\ fs [] \\
    drule_strip fixwidth_sum_2pow \\ rfs [])

 \\ fs [lookup_insert_var_cmp] \\ drule_first \\ rpt TOP_CASE_TAC
 >- (fs []
     >- (drule var_lt_le \\ disch_then (qspec_then ‘blast_s.tmpnum’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
         drule_first \\ fs [])
     \\ metis_tac [cell_inp_run_cong_lt])

 >- (fs [] \\ rpt strip_tac \\ first_x_assum (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
     rpt drule_first \\ fs [EVERY_EL] \\
     first_x_assum (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
     drule_strip cell_inp_run_lt_cget_var_cong \\ simp [])))

 >- (* CellMux *)
 (rename1 ‘CellMux out in1 in2 in3’ \\
  simp [blast_cell_def, cell_output_def] \\ rpt gen_tac \\ reverse TOP_CASE_TAC
  >- (rpt strip_tac' \\ rveq \\ simp [deterministic_netlist_def, cell_run_def, sum_bind_INR] \\ rpt strip_tac' \\
      drule_strip blast_cell_inp_run_correct_array \\ fs [cell_output_ok_def] \\ strip_tac \\ fs [cellMux_run_def]) \\
  rpt TOP_CASE_TAC \\ rpt strip_tac' \\ rveq \\
  simp [deterministic_netlist_def, deterministic_cell_def, sum_foldM_def, cell_run_def, sum_bind_INR] \\
  rpt strip_tac' \\ qspec_then ‘in1’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
  fs [cell_output_ok_def] \\ strip_tac

  >- (* bool, bool *)
  (qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
   qspec_then ‘in3’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
   simp [] \\ rpt strip_tac \\ fs [cellMux_run_def] \\
   drule_strip blast_rel_cset_var_cset_var_bool \\ simp [])

  >- (* bool, array *)
  (qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
   qspec_then ‘in3’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
   simp [] \\ rpt strip_tac \\ fs [cellMux_run_def])

  >- (* array, bool *)
  (qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
   qspec_then ‘in3’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
   simp [] \\ rpt strip_tac \\ fs [cellMux_run_def])

  \\ (* array, array *)
  fs [blaster_new_names_def] \\ rveq \\ simp [] \\ rpt strip_tac
  >- (match_mp_tac blasterstate_ok_insert \\ simp [])
  >- simp [EVERY_EL, indexedListsTheory.EL_MAP2i, deterministic_cell_def]
  >- (rfs [blasterstate_ok_def, lookup_insert_var_cmp, cell_output_ok_def, cell_output_def] \\ every_case_tac
     >- rw [EVERY_GENLIST, bsi_inp_trans_ok_def, bsi_cell_input_ok_def, cell_input_lt_def, cell_input_ge_def, var_lt_def, var_ge_def]
     >- metis_tac [])
  >- (fs [blasterstate_ok_def, lookup_insert_var_cmp, cell_output_def])
  >- (fs [blasterstate_ok_def, lookup_insert_var_cmp, cell_output_def]) \\

  drule_first \\
  qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
  qspec_then ‘in3’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
  simp [] \\ rpt strip_tac \\ fs [cellMux_run_def, sum_bind_INR, sum_check_INR] \\ rveq \\

  drule_strip blast_cell_input_SOME_bool \\
  impl_tac >- (match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ fs [blasterstate_ok_def]) \\ strip_tac \\
  qspec_then ‘in2’ assume_tac blast_cell_input_SOME \\ drule_first \\
  qspec_then ‘in3’ assume_tac blast_cell_input_SOME \\ drule_first \\
  qspecl_then [‘l’, ‘l'’] assume_tac blast_cellMux_correct \\ drule_first \\ simp [] \\

  fs [blast_rel_def, blasterstate_ok_def, cset_var_fbits, cget_var_cset_var, lookup_insert_var_cmp] \\ rpt strip_tac \\
  IF_CASES_TAC >- rw [] \\

  drule_last \\ rpt TOP_CASE_TAC \\ fs []
  >- (first_assum (qspec_then `VarInp var NONE` mp_tac) \\ 
      impl_tac >- (simp [cell_input_lt_def] \\ match_mp_tac var_lt_le \\ asm_exists_tac \\ simp []) \\
      simp [cell_inp_run_def])

  \\ fs [EVERY_EL] \\ metis_tac [])

 \\ (* CellArrayWrite *)
 rename1 ‘CellArrayWrite out arr idx e’ \\
 simp [blast_cell_def, cell_output_ok_def, cell_output_def] \\
 rpt gen_tac \\ TOP_CASE_TAC
 >- (* bool as array *)
 (rw [cell_run_def, sum_bind_INR, deterministic_netlist_def] \\ simp [] \\
 Cases_on ‘in1’ \\ Cases_on ‘in2’ \\ fs [cellArrayWrite_run_def] \\ rveq \\
 drule_strip blast_cell_inp_run_correct_bool \\ simp [])

 \\ TOP_CASE_TAC \\ rpt strip_tac' \\ rveq
 >- (* array *)
 (simp [] \\ rpt strip_tac
 >- (fs [blasterstate_ok_def, insert_thm_var_cmp, lookup_insert_var_cmp] \\ conj_tac \\ rpt gen_tac \\
     (reverse IF_CASES_TAC >- (rw [] \\ drule_first)) \\ rw []
     >- (match_mp_tac IMP_EVERY_revLUPDATE \\ simp [] \\ conj_tac
         >- (match_mp_tac blast_cell_input_bool_cell_input_lt \\ rpt asm_exists_tac \\ simp [] \\ conj_tac \\
             first_x_assum MATCH_ACCEPT_TAC)
         \\ (match_mp_tac blast_cell_input_array_cell_input_lt \\ rpt asm_exists_tac \\ simp [] \\
             first_x_assum MATCH_ACCEPT_TAC))
     \\ (match_mp_tac blast_cell_input_array_cell_input_lt \\ rpt asm_exists_tac \\ simp [] \\
         first_x_assum MATCH_ACCEPT_TAC))
 >- simp [deterministic_netlist_def]
 >- (rfs [blasterstate_ok_def, lookup_insert_var_cmp] \\ 
     pop_assum mp_tac \\ reverse IF_CASES_TAC >- metis_tac [] \\ rw [] \\ simp [bsi_inp_trans_ok_def]
     >- (match_mp_tac IMP_EVERY_revLUPDATE \\
         drule_strip blast_cell_input_bool_bsi_cell_input_ok \\
         drule_strip blast_cell_input_array_bsi_cell_input_ok \\ metis_tac [bsi_inp_trans_ok_def])
     \\ drule_strip blast_cell_input_array_bsi_cell_input_ok \\ metis_tac [bsi_inp_trans_ok_def])
 >- fs [blasterstate_ok_def, lookup_insert_var_cmp]
 >- fs [blasterstate_ok_def, lookup_insert_var_cmp]

 \\ fs [sum_foldM_def, cell_run_def, sum_bind_INR] \\ 
    drule_strip blast_cell_inp_run_correct_array \\ drule_strip blast_cell_inp_run_correct_bool \\
    simp [] \\ rpt strip_tac \\ rveq \\ fs [cellArrayWrite_run_def] \\ rveq \\

    fs [blast_rel_def, blasterstate_ok_def, lookup_insert_var_cmp, cset_var_fbits, cget_var_cset_var] \\
    rpt strip_tac \\ reverse IF_CASES_TAC >- fs [] \\
    rw [revLUPDATE_def, EL_LUPDATE] \\ rw [])
 
 >- (* array as input *)
 (simp [cell_run_def, sum_bind_INR, deterministic_netlist_def] \\ rpt strip_tac \\
 Cases_on ‘in1’ \\ Cases_on ‘in2’ \\ fs [cellArrayWrite_run_def] \\ rveq \\
 drule_strip blast_cell_inp_run_correct_array \\ simp [])
QED

(* If we maintain this invariant we do not need to remove entries when "blasting" bools (i.e. doing nothing);
   now also used for more purposes. *)
val netlist_overlap_si_def = Define ‘
 netlist_overlap_si si tmpnum nl =
  !n. MEM n (FLAT (MAP cell_output nl)) ==>
      lookup var_cmp (NetVar n) si = NONE /\
      (!var inps. lookup var_cmp var si = SOME (ArrayInp inps) ==> EVERY (bsi_cell_input_ok n tmpnum) inps) ∧
      (!var inp. lookup var_cmp var si = SOME (BoolInp inp) ==> bsi_cell_input_ok n tmpnum inp)’;

Triviality EVERY_bsi_cell_input_ok_out_le:
 !n m tmpnum inps. EVERY (bsi_cell_input_ok n tmpnum) inps /\ n <= m ==> EVERY (bsi_cell_input_ok m tmpnum) inps
Proof
 rw [EVERY_MEM] \\ drule_first \\ fs [bsi_cell_input_ok_def] \\ metis_tac [cell_input_lt_le]
QED

Triviality sorted_append_snd_imp:
 ∀l1 l2 R. SORTED R (l1 ⧺ l2) ⇒ SORTED R l2
Proof
 simp [sortingTheory.SORTED_APPEND_GEN]
QED

Triviality sorted_append_lt:
 ∀(xs : num list) ys.
 SORTED $< (xs ++ ys) ==> ∀x y. MEM x xs ∧ MEM y ys ⇒ x < y
Proof
 Induct \\ fs [sortingTheory.SORTED_EQ] \\ metis_tac []
QED

Theorem blast_netlist_correct:
 !nl nl' blast_s blast_s' tmpnum.
 blast_netlist blast_s nl = (blast_s', nl') /\

 deterministic_netlist nl /\ netlist_ok blast_s.extenv 0 tmpnum nl /\ netlist_sorted nl /\

 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum ==>
 blast_s'.extenv = blast_s.extenv /\
 blasterstate_ok blast_s'.si tmpnum blast_s'.tmpnum /\

 (!reg i. lookup var_cmp (RegVar reg i) blast_s'.si = lookup var_cmp (RegVar reg i) blast_s.si) /\
 (!n. ~MEM n (FLAT (MAP cell_output nl)) ==>
      lookup var_cmp (NetVar n) blast_s'.si = lookup var_cmp (NetVar n) blast_s.si) /\

 deterministic_netlist nl' /\
 (!s s' bs fext.
   sum_foldM (cell_run fext) s nl = INR s' /\ rtltype_extenv_n blast_s.extenv fext /\
   blast_rel fext blast_s.si tmpnum s bs /\
   netlist_overlap_si blast_s.si tmpnum nl ==>
   ?bs'. sum_foldM (cell_run fext) bs nl' = INR bs' /\ blast_rel fext blast_s'.si tmpnum s' bs')
Proof
 Induct >- (rw [blast_netlist_def] \\ fs [sum_foldM_def] \\ rw []) \\
 simp [blast_netlist_def] \\ rpt strip_tac' \\ rpt (pairarg_tac \\ fs []) \\ rveq \\
 fs [deterministic_netlist_def, netlist_ok_def, netlist_sorted_def] \\
 drule_strip blast_cell_correct \\
 drule_first \\ drule_strip sorted_append_snd_imp \\ simp [] \\ pop_assum kall_tac \\ disch_then drule_strip \\
 fs [sum_foldM_def, sum_bind_INR, deterministic_netlist_def] \\ rpt strip_tac \\

 drule_last \\ impl_tac >- (fs [netlist_overlap_si_def, blasterstate_ok_def] \\
                            metis_tac [arithmeticTheory.LESS_LESS_EQ_TRANS]) \\ strip_tac \\
 simp [sum_foldM_append, sum_bind_def] \\
 drule_first \\ disch_then match_mp_tac \\

 full_simp_tac (srw_ss()++boolSimps.DNF_ss) [netlist_overlap_si_def] \\
 drule_strip sorted_all_distinct_lt \\ fs [ALL_DISTINCT_APPEND] \\ conj_tac >- metis_tac [] \\
 rpt strip_tac \\ (Cases_on ‘var’ >- metis_tac []) \\ Cases_on ‘MEM n' (cell_output h)’
 >- (first_x_assum (qspecl_then [‘NetVar n'’, ‘ArrayInp inps’, ‘n'’] mp_tac) \\
     impl_tac >- (Cases_on ‘inp’ \\ metis_tac [bsi_inp_trans_ok_def]) \\ simp [bsi_inp_trans_ok_def] \\ strip_tac \\
     irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [bsi_cell_input_ok_def] \\ simp [] \\
     disj1_tac \\ match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ drule_strip sorted_append_lt \\ simp [])
 >- metis_tac []
 >- (first_x_assum (qspecl_then [‘NetVar n'’, ‘BoolInp inp’, ‘n'’] mp_tac) \\
     impl_tac >- (rpt gen_tac \\ Cases_on ‘inp'’ \\ metis_tac [bsi_inp_trans_ok_def]) \\
     simp [bsi_inp_trans_ok_def, bsi_cell_input_ok_def] \\ reverse strip_tac >- simp [] \\
     disj1_tac \\ match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ drule_strip sorted_append_lt \\ simp [])
 >- metis_tac []
QED

Theorem blast_regs_correct_bool:
 !fext snet sbase bsnet bsbase s blast_s h1 h2 h3 inp inp' tmpnum.
 blast_cell_input blast_s inp = BoolInp inp' /\
 reg_run fext snet sbase (CBool_t,h1,h2,h3,SOME inp) = INR s /\
 blast_rel fext blast_s.si tmpnum sbase bsbase /\
 blast_rel fext blast_s.si tmpnum snet bsnet /\
 rtltype_extenv_n blast_s.extenv fext /\
 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum /\
 reg_ok blast_s.extenv tmpnum (CBool_t,h1,h2,h3,SOME inp) /\
 si_wf blast_s.si /\
 si_prefilled blast_s.si (CBool_t,h1,h2,h3,SOME inp) /\
 only_regs sbase ==>
 ?bs. reg_run fext bsnet bsbase (CBool_t,h1,h2,h3,SOME inp') = INR bs /\ (* <-- h4 must be output from blasting... *)
      only_regs s /\
      blast_rel fext blast_s.si tmpnum s bs
Proof
 rw [reg_run_def, sum_bind_INR, si_prefilled_def, reg_ok_def] \\
 drule_strip blast_cell_inp_run_correct_bool \\ simp [] \\ strip_tac \\
 simp [only_regs_cset_var_RegVar] \\ 
 match_mp_tac blast_rel_cset_var_reg_bool \\ simp []
QED

Theorem blast_regs_correct_array_help:
 !reg fext init inps vs shift bsnet bsbase.
 LENGTH vs = LENGTH inps /\
 (!i. i < LENGTH inps ==> cell_inp_run fext bsnet (EL i inps) = INR (CBool (EL i vs))) ==>
 (* init does not matter here, but have it to match later: *)
 ?bs. sum_foldM (reg_run fext bsnet) bsbase (MAPi (λi inp. (CBool_t,reg,i+shift,SOME (CBool (EL (i+shift) init)),SOME inp)) inps) = INR bs /\
      (!var. cget_var bs var = case var of
               RegVar reg' i' => if reg' = reg /\ shift <= i' /\ i' < LENGTH inps + shift then
                                  INR (CBool (EL (i'-shift) vs))
                                 else
                                  cget_var bsbase var
             | _ => cget_var bsbase var) /\
      bs.fbits = bsbase.fbits
Proof
 (* Much of proof similar to init_run_blasted_array_help proof ... *)
 ntac 3 gen_tac \\ Induct >- (rw [sum_foldM_def] \\ TOP_CASE_TAC) \\ rpt strip_tac \\ Cases_on ‘vs’ \\ fs [] \\
 simp [sum_foldM_def, reg_run_def] \\
 first_assum (qspec_then ‘0’ (rewrite_tac o sing o SIMP_RULE (srw_ss()) [])) \\ simp [sum_bind_def, has_rtltype_v_def] \\
 qmatch_goalsub_abbrev_tac ‘sum_foldM _ bsbase' _’ \\
 drule_first \\ disch_then (qspecl_then [‘shift + 1’, ‘bsnet’, ‘bsbase'’] mp_tac) \\
 impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then ‘SUC i’ mp_tac) \\ simp []) \\ strip_tac \\
 unabbrev_all_tac \\ qexists_tac ‘bs’ \\ rpt conj_tac
 >- (qpat_x_assum ‘sum_foldM _ _ _ = _’ (assume_tac o GSYM) \\
     simp [combinTheory.o_DEF, arithmeticTheory.ADD1] \\ f_equals_tac \\ simp [FUN_EQ_THM])
 >- (rpt strip_tac \\ simp [] \\ TOP_CASE_TAC
  >- (simp [arithmeticTheory.ADD1] \\ Cases_on ‘n = shift’
   >- (rveq \\ simp [cget_var_cset_var])
   >- (simp [cget_var_cset_var] \\ IF_CASES_TAC \\ fs [] \\
      Cases_on ‘n - shift’ \\ fs [] \\ f_equals_tac \\ decide_tac))
  >- simp [cget_var_cset_var])
 \\ fs [cset_var_fbits]
QED

Theorem blast_regs_correct_array:
 !l x fext snet sbase bsnet bsbase s blast_s n reg i inp tmpnum.
 blast_cell_input blast_s inp = ArrayInp x /\
 reg_run fext snet sbase (CArray_t n,reg,i,SOME (CArray l),SOME inp) = INR s /\
 blast_rel fext blast_s.si tmpnum sbase bsbase /\
 blast_rel fext blast_s.si tmpnum snet bsnet /\
 LENGTH l = LENGTH x /\
 rtltype_extenv_n blast_s.extenv fext /\
 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum /\
 reg_ok blast_s.extenv tmpnum (CArray_t n,reg,i,SOME (CArray l),SOME inp) /\
 si_wf blast_s.si /\
 si_prefilled blast_s.si (CArray_t n,reg,i,SOME (CArray l),SOME inp) /\
 only_regs sbase ==>
 ?bs. sum_foldM (reg_run fext bsnet) bsbase (MAPi (λi inp. (CBool_t,reg,i,SOME (CBool (EL i l)),SOME inp)) x) = INR bs /\
      only_regs s /\
      blast_rel fext blast_s.si tmpnum s bs
Proof
 rw [reg_ok_def, has_rtltype_v_def, reg_run_def, sum_bind_INR] \\
 drule_strip blast_cell_inp_run_correct_array \\ simp [] \\ strip_tac \\
 drule_strip blast_regs_correct_array_help \\ pop_assum (qspecl_then [‘reg’, ‘l’, ‘0’, ‘bsbase’] strip_assume_tac) \\
 fs [only_regs_cset_var_RegVar, blast_rel_def, cset_var_fbits, cget_var_cset_var] \\
 rpt strip_tac \\ IF_CASES_TAC
 >- (rveq \\ fs [si_prefilled_def, si_wf_def] \\ rpt strip_tac \\ rpt drule_first \\
     rfs [cell_inp_run_def, sum_bind_def, cget_fext_var_def]) \\
 drule_last \\ TOP_CASE_TAC \\ TOP_CASE_TAC \\ fs []

 >- (rpt TOP_CASE_TAC \\ qpat_x_assum ‘only_regs _’ mp_tac \\ simp [only_regs_def] \\
     disch_then (qspec_then ‘RegVar reg n’ assume_tac) \\ fs [] \\ rfs [])

 >- (qpat_x_assum ‘only_regs _’ mp_tac \\ simp [only_regs_def] \\
     disch_then (qspec_then ‘var’ mp_tac) \\ Cases_on ‘var’ \\ simp [] \\
     rfs [si_wf_def]) \\

 rpt strip_tac \\ first_x_assum (qspec_then ‘i’ mp_tac) \\
 impl_tac >- simp [] \\

 qpat_x_assum ‘only_regs _’ assume_tac \\ fs [only_regs_def] \\ first_x_assum (qspec_then ‘var’ mp_tac) \\
 TOP_CASE_TAC \\ fs [] \\ strip_tac \\ rveq \\ drule_strip si_wf_shape \\ fs [] \\ rveq \\
 first_assum (once_rewrite_tac o sing) \\ rw [EL_GENLIST, cell_inp_run_def, sum_bind_INR, cget_fext_var_def]
QED

Theorem blast_regs_correct_array_no_inp:
 !i fi fv fext bsnet bsbase t dest.
 sum_foldM (reg_run fext bsnet) bsbase (GENLIST (λi. (t,dest,fi i,fv i,NONE)) i) = INR bsbase
Proof
 Induct >- simp [sum_foldM_def] \\ simp [GENLIST, SNOC_APPEND, sum_foldM_append, sum_bind_def] \\
 simp [sum_foldM_def, reg_run_def, sum_bind_def]
QED

Theorem blast_regs_correct:
 !regs regs' blast_s fext snet sbase bsnet bsbase s tmpnum.
 blast_regs blast_s regs = INR regs' /\
 sum_foldM (reg_run fext snet) sbase regs = INR s /\
 blast_rel fext blast_s.si tmpnum sbase bsbase /\
 blast_rel fext blast_s.si tmpnum snet bsnet /\
 regs_ok blast_s.extenv tmpnum regs /\
 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum /\
 si_wf blast_s.si /\
 si_prefilleds blast_s.si regs /\
 only_regs sbase /\
 rtltype_extenv_n blast_s.extenv fext  ==>
 ?bs. sum_foldM (reg_run fext bsnet) bsbase regs' = INR bs /\
      only_regs s /\
      blast_rel fext blast_s.si tmpnum s bs
Proof
 Induct >- (rw [blast_regs_def] \\ fs [sum_foldM_def] \\ rw []) \\
 PairCases \\ fs [blast_regs_def, sum_foldM_def, sum_bind_INR, regs_ok_def, si_prefilleds_def] \\ rpt gen_tac \\
 TOP_CASE_TAC \\ every_case_tac \\ simp [sum_bind_INR] \\ strip_tac \\ rveq
 >- (* bool without inp *)
    (fs [optionTheory.OPTION_MAP_EQ_NONE] \\ rveq \\
    fs [sum_foldM_def, reg_run_def, sum_bind_INR] \\ rveq \\ drule_first \\ simp [])
 >- (* bool *)
    (fs [optionTheory.OPTION_MAP_EQ_SOME] \\ qpat_x_assum ‘BoolInp _ = _’ (assume_tac o GSYM) \\ rveq \\
     simp [sum_foldM_def] \\ drule_strip blast_regs_correct_bool \\ simp [sum_bind_INR] \\ drule_first \\ simp [])
 >- (* array without inp *)
    (fs [sum_foldM_append, reg_run_def] \\ rveq \\
    DEP_REWRITE_TAC [blast_regs_correct_array_no_inp] \\ simp [sum_bind_def] \\
    drule_first \\ simp [])
 \\ (* array *)
    fs [sum_foldM_append, sum_check_INR] \\ drule_strip blast_regs_correct_array \\ simp [sum_bind_INR] \\
    drule_first \\ simp []
QED

Theorem blast_netlist_correct_step:
 !tmpnum fext nl nl' s s' bs blast_s blast_s' regs regs'.
 blast_netlist blast_s nl = (blast_s', nl') /\
 blast_regs blast_s' regs = INR regs' /\
 netlist_step fext s nl regs = INR s' /\
 blast_rel fext blast_s.si tmpnum s bs /\

 deterministic_netlist nl /\ netlist_ok blast_s.extenv 0 tmpnum nl /\ netlist_sorted nl /\
 regs_ok blast_s.extenv tmpnum regs /\

 si_wf blast_s.si /\
 si_prefilleds blast_s.si regs /\

 netlist_overlap_si blast_s.si tmpnum nl /\

 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum /\
 rtltype_extenv_n blast_s.extenv fext /\

 only_regs s ==>
 blast_s'.extenv = blast_s.extenv /\
 ?bs'. netlist_step fext bs nl' regs' = INR bs' /\
       only_regs s' /\
       blast_rel fext blast_s'.si tmpnum s' bs'
Proof
 simp [netlist_step_def, sum_bind_INR] \\ rpt strip_tac' \\

 drule_strip blast_netlist_correct \\ drule_first \\ simp [] \\

 ‘si_wf blast_s'.si’ by metis_tac [si_wf_def] \\
 ‘blast_rel fext blast_s'.si tmpnum s bs’ by metis_tac [blast_rel_only_regs] \\

 drule_strip blast_regs_correct \\
 impl_tac >- (simp [] \\ drule_strip si_prefilleds_cong \\ simp []) \\ strip_tac \\
 simp [only_regs_fbits] \\ fs [blast_rel_def, cget_var_fbits, cell_inp_run_fbits]
QED

Theorem blast_netlist_correct_run:
 !n nl nl' fext s s' bs blast_s blast_s' tmpnum regs regs'.
 blast_netlist blast_s nl = (blast_s', nl') /\
 blast_regs blast_s' regs = INR regs' /\
 netlist_run fext s nl regs n = INR s' /\
 blast_reg_rel blast_s.si s bs /\

 si_wf blast_s.si /\
 si_prefilleds blast_s.si regs /\

 deterministic_netlist nl /\ netlist_ok blast_s.extenv 0 tmpnum nl /\ netlist_sorted nl /\ netlist_overlap_si blast_s.si tmpnum nl /\
 regs_ok blast_s.extenv tmpnum regs /\

 rtltype_extenv blast_s.extenv fext /\
 blasterstate_ok blast_s.si tmpnum blast_s.tmpnum /\
 
 only_regs s ==>
 ?bs'. netlist_run fext bs nl' regs' n = INR bs' /\
       blasterstate_ok blast_s'.si tmpnum blast_s'.tmpnum /\
       only_regs s' /\
       blast_reg_rel blast_s.si s' bs'
Proof
 Induct >- (simp [netlist_run_def] \\ rpt strip_tac' \\ drule_strip blast_netlist_correct) \\

 rw [netlist_run_def, sum_bind_INR] \\ drule_first \\
 drule_strip blast_netlist_correct_step \\
 disch_then (qspecl_then [‘tmpnum’, ‘bs'’] mp_tac) \\ fs [rtltype_extenv_rtltype_extenv_n] \\ 
 impl_tac >- (drule_strip blast_reg_rel_blast_rel \\ simp []) \\ strip_tac \\

 drule_strip blast_netlist_correct \\ simp [] \\
 ‘si_wf blast_s'.si’ by metis_tac [si_wf_def] \\
 metis_tac [blast_rel_only_regs, blast_rel_blast_reg_rel]
QED

Theorem init_run_blasted_array_help:
 !finp reg vs l bs shift.
 LENGTH l = LENGTH vs ==>
 ?bs'. init_run bs (MAPi (λi inp. (CBool_t,reg,i+shift,SOME (CBool (EL i l)),finp inp)) vs) = INR bs' /\
       (!var. cget_var bs' var = case var of
                RegVar reg' i' => if reg' = reg /\ shift <= i' /\ i' < LENGTH l + shift then
                                   INR (CBool (EL (i'-shift) l))
                                  else
                                   cget_var bs var
              | _ => cget_var bs var) /\
       bs'.fbits = bs.fbits
Proof
 ntac 2 gen_tac \\ Induct >- (rw [init_run_def] \\ TOP_CASE_TAC) \\ rpt strip_tac \\ Cases_on ‘l’ \\ fs [] \\
 simp [init_run_def, has_rtltype_v_def] \\ qmatch_goalsub_abbrev_tac ‘init_run bs' _’ \\
 drule_first \\ pop_assum (qspecl_then [‘bs'’, ‘shift + 1’] strip_assume_tac) \\
 unabbrev_all_tac \\ qexists_tac ‘bs''’ \\ rpt conj_tac
 >- (qpat_x_assum ‘init_run _ _ = _’ (assume_tac o GSYM) \\ fs [combinTheory.o_DEF, arithmeticTheory.ADD1] \\ f_equals_tac \\ simp [FUN_EQ_THM])
 >- (rpt strip_tac \\ simp [] \\ TOP_CASE_TAC
  >- (simp [arithmeticTheory.ADD1] \\ Cases_on ‘n = shift’
   >- (rveq \\ simp [cget_var_cset_var])
   >- (simp [cget_var_cset_var] \\ IF_CASES_TAC \\ fs [] \\
      Cases_on ‘n - shift’ \\ fs [] \\ f_equals_tac \\ decide_tac))
  >- simp [cget_var_cset_var])
 \\ fs [cset_var_fbits]
QED

Theorem init_run_blasted_array:
 !finp inps inp n l s s' bs si reg.
 init_run s [(CArray_t n,reg,0,SOME (CArray l),inp)] = INR s' /\
 si_prefilled si (CArray_t n,reg,0,SOME (CArray l),inp) /\
 si_wf si /\
 only_regs s /\
 blast_reg_rel si s bs /\
 LENGTH l = LENGTH inps ==>
 only_regs s' /\
 ?bs'. init_run bs (MAPi (λi inp. (CBool_t,reg,i,SOME (CBool (EL i l)),finp inp)) inps) = INR bs' /\
       blast_reg_rel si s' bs'
Proof
 rpt strip_tac' \\ drule_strip init_run_blasted_array_help \\ 
 pop_assum (qspecl_then [‘finp’, ‘reg’, ‘bs’, ‘0’] strip_assume_tac) \\
 fs [init_run_def, blast_reg_rel_def, cset_var_fbits, only_regs_cset_var_RegVar] \\ rpt strip_tac \\ simp [cget_var_cset_var] \\ IF_CASES_TAC
 >- (fs [has_rtltype_v_def, si_prefilled_def, si_wf_def] \\ rveq \\ drule_last \\ rpt strip_tac \\ rfs [cell_inp_run_def, sum_bind_def, cget_fext_var_def])
 \\ rpt TOP_CASE_TAC \\ fs [] \\
    rpt strip_tac \\ first_x_assum (qspec_then ‘reg'’ mp_tac) \\ simp []
QED

Triviality MAPi_ignore_second_arg_GENLIST':
 !l f j. MAPi (λi inp. f (i+j)) l = GENLIST (λi. f (i+j)) (LENGTH l)
Proof
 Induct \\ rw [GENLIST_CONS] \\ first_x_assum (qspecl_then [‘f’, ‘j + 1’] mp_tac) \\
 simp [combinTheory.o_DEF, arithmeticTheory.ADD1] \\
 ‘!(a:num) i. j + (i + 1) = i + (j + 1)’ by decide_tac \\ pop_assum (once_rewrite_tac o sing) \\ simp []
QED

Triviality MAPi_ignore_second_arg_GENLIST:
 !l f. MAPi (λi inp. f i) l = GENLIST (λi. f i) (LENGTH l)
Proof
 rpt gen_tac \\ qspecl_then [‘l’, ‘f’, ‘0’] mp_tac MAPi_ignore_second_arg_GENLIST' \\ simp []
QED

Theorem blast_regs_init_correct:
 !tmpnum regs regs' s s' bs blast_s.
 init_run s regs = INR s' /\
 blast_regs blast_s regs = INR regs' /\
 regs_ok blast_s.extenv tmpnum regs /\
 deterministic_regs regs /\
 only_regs s /\
 blast_reg_rel blast_s.si s bs /\
 si_wf blast_s.si /\
 si_prefilleds blast_s.si regs ==>
 ?bs'. init_run bs regs' = INR bs' /\
       blast_reg_rel blast_s.si s' bs'
Proof
 gen_tac \\ Induct >- simp [init_run_def, blast_regs_def] \\
 PairCases \\ rename1 `(t, reg, i, v, inp)` \\
 fs [regs_ok_def, reg_ok_def, deterministic_regs_def, blast_regs_def, si_prefilleds_def] \\
 rpt gen_tac \\ TOP_CASE_TAC

 >- (* bool *)
 (rpt TOP_CASE_TAC \\ (simp [sum_bind_INR] \\ rpt strip_tac' \\ rveq \\ fs [init_run_def] \\
                       TOP_CASE_TAC >- fs [deterministic_reg_def] \\ fs [] \\ FULL_CASE_TAC \\ fs [] \\
                       first_x_assum match_mp_tac \\ rpt asm_exists_tac \\
                       fs [only_regs_cset_var_RegVar, si_prefilled_def, has_rtltype_v_CBool_t] \\
                       metis_tac [blast_rel_cset_var_reg_bool, blast_reg_rel_blast_rel, blast_rel_blast_reg_rel]))

 \\ every_case_tac
 >- (* array -- genlist case (no inps) *)
 (rw [sum_check_INR, sum_bind_INR] \\ fs [init_run_append, Once init_run_cons] \\
 simp [GSYM MAPi_ignore_second_arg_GENLIST] \\
 qspecl_then [‘K NONE : 'a -> cell_input option’, ‘l’] mp_tac init_run_blasted_array \\ disch_then drule_strip \\
 simp [combinTheory.K_THM] \\ strip_tac \\ simp [] \\
 first_x_assum match_mp_tac \\ asm_exists_tac \\ simp [])

 \\ (* array -- mapi case (inps) *)
 rw [sum_check_INR, sum_bind_INR] \\ fs [init_run_append, Once init_run_cons] \\
 qspecl_then [‘SOME’, ‘l’] mp_tac init_run_blasted_array \\ disch_then drule_strip \\
 simp [] \\ first_x_assum match_mp_tac \\ asm_exists_tac \\ simp []
QED

Triviality mem_map_blast_reg_name_reg_name:
 ∀regs reg i. MEM (reg,i) (MAP blast_reg_name regs) ⇒ MEM reg (MAP reg_name regs)
Proof
 rw [MEM_MAP] \\ qexists_tac ‘y’ \\ PairCases_on ‘y’ \\ fs [blast_reg_name_def, reg_name_def]
QED

Theorem blast_regs_distinct:
 ∀regs regs' blast_s.
 blast_regs blast_s regs = INR regs' ∧ regs_distinct regs ⇒
 (∀reg. MEM reg (MAP reg_name regs') ⇒ MEM reg (MAP reg_name regs)) ∧ blast_regs_distinct regs'
Proof
 Induct >- rw [blast_regs_def, blast_regs_distinct_def] \\
 TRY PairCases \\ simp [blast_regs_def] \\ rpt gen_tac \\ TOP_CASE_TAC

 >- (rpt TOP_CASE_TAC \\ simp [sum_bind_INR] \\ rpt strip_tac' \\ rveq \\
    drule_strip regs_distinct_tl \\ drule_first \\ (rw [reg_name_def]
    >- (drule_first \\ simp [])
    >- (fs [blast_regs_distinct_def, regs_distinct_def, blast_reg_name_def, reg_name_def] \\
        metis_tac [mem_map_blast_reg_name_reg_name])))

 \\ every_case_tac \\ simp [sum_bind_INR] \\ rpt strip_tac' \\ rveq \\
    drule_strip regs_distinct_tl \\ drule_first \\ (rw [reg_name_def]
    >- fs [MAP_GENLIST, MEM_GENLIST, indexedListsTheory.MEM_MAPi, reg_name_def]
    >- (drule_first \\ simp [])
    >- (fs [blast_regs_distinct_def, regs_distinct_def, blast_reg_name_def, reg_name_def,
            MAP_GENLIST, ALL_DISTINCT_GENLIST, indexedListsTheory.MAPi_GENLIST, ALL_DISTINCT_APPEND] \\
        rw [MEM_GENLIST, indexedListsTheory.MEM_MAPi, blast_reg_name_def] \\
        metis_tac [mem_map_blast_reg_name_reg_name]))
QED

Theorem init_run_only_regs_ok:
 !regs (extenv : (string, rtltype) alist) s s' tmpnum.
 init_run s regs = INR s' /\ regs_ok extenv tmpnum regs /\ only_regs s ==> only_regs s'
Proof
 Induct >- (EVAL_TAC \\ simp []) \\ PairCases \\ fs [init_run_def, regs_ok_def, reg_ok_def] \\ rpt gen_tac \\ TOP_CASE_TAC
 >- (pairarg_tac \\ simp [] \\ strip_tac \\ drule_first \\ simp [only_regs_cset_var_RegVar, only_regs_fbits])
 \\ rw [] \\ drule_first \\ simp [only_regs_cset_var_RegVar]
QED

Theorem blast_rel_nil:
 !fext si tmpnum fbits. blast_rel fext si tmpnum <| env := []; fbits := fbits |> <| env := []; fbits := fbits |>
Proof
 rw [blast_rel_def, cget_var_def]
QED

Theorem blast_reg_rel_nil:
 !si fbits. blast_reg_rel si <| env := []; fbits := fbits |> <| env := []; fbits := fbits |>
Proof
 rw [blast_reg_rel_def, cget_var_def]
QED

Theorem only_regs_nil:
 !fbits. only_regs <|env := []; fbits := fbits|>
Proof
 rw [only_regs_def, cget_var_def] \\ TOP_CASE_TAC
QED

(** Initial si properties **)

Theorem MEM_reg_regs_shape:
 !reg regs. MEM reg (MAP reg_name regs) <=> ?t i v inp. MEM (t,reg,i,v,inp) regs
Proof
 rw [MEM_MAP] \\ eq_tac \\ strip_tac
 >- (rveq \\ PairCases_on ‘y’ \\ simp [reg_name_def] \\ asm_exists_tac)
 \\ asm_exists_any_tac \\ simp [reg_name_def]
QED

Theorem regs_ok_RegVar_idx_0:
 !regs extenv t reg i v inp tmpnum. regs_ok extenv tmpnum regs /\ MEM (t,reg,i,v,inp) regs ==> i = 0
Proof
 rw [regs_ok_def, EVERY_MEM] \\ drule_first \\ fs [reg_ok_def]
QED

(*Theorem regs_wf_RegVar_idx_not_0:
 !regs t reg i v inp. regs_wf regs /\ i <> 0 ==> ~MEM (t,reg,i,v,inp) regs
Proof
 metis_tac [regs_wf_RegVar_idx_0]
QED*)

Theorem fromList_cons:
 !cmp k v xs. fromList cmp ((k,v)::xs) = insert cmp k v (fromList cmp xs)
Proof
 simp [fromList_def]
QED

Theorem lookup_initial_si_NetVar:
 !regs n. lookup var_cmp (NetVar n) (fromList var_cmp (option_flatMap build_si_entry regs)) = NONE
Proof
 Induct >- (EVAL_TAC \\ simp []) \\ PairCases \\ rpt strip_tac \\ simp [option_flatMap_def, build_si_entry_def] \\
 every_case_tac \\ simp [fromList_cons] \\ DEP_REWRITE_TAC [lookup_insert_var_cmp] \\ simp [fromList_thm_var_cmp]
QED

Triviality lookup_initial_si_RegVar_bool:
 !regs reg i inp.
 lookup var_cmp (RegVar reg i) (fromList var_cmp (option_flatMap build_si_entry regs)) ≠ SOME (BoolInp inp)
Proof
 Induct >- (EVAL_TAC \\ simp []) \\ PairCases \\ rpt strip_tac' \\ simp [option_flatMap_def, build_si_entry_def] \\
 every_case_tac \\ simp [fromList_cons] \\ DEP_REWRITE_TAC [lookup_insert_var_cmp] \\ rw [fromList_thm_var_cmp]
QED

Theorem lookup_initial_si_bool:
 !regs var inp.
 lookup var_cmp var (fromList var_cmp (option_flatMap build_si_entry regs)) ≠ SOME (BoolInp inp)
Proof
 Cases_on ‘var’ \\ simp [lookup_initial_si_NetVar, lookup_initial_si_RegVar_bool]
QED

Theorem lookup_initial_si_RegVar_not_mem:
 !regs reg i.
 ~MEM reg (MAP reg_name regs) ==>
 lookup var_cmp (RegVar reg i) (fromList var_cmp (option_flatMap build_si_entry regs)) = NONE
Proof
 Induct >- (EVAL_TAC \\ simp []) \\ PairCases \\ rpt strip_tac \\ simp [option_flatMap_def, build_si_entry_def] \\
 every_case_tac \\ fs [fromList_cons, reg_name_def] \\
 DEP_REWRITE_TAC [lookup_insert_var_cmp] \\ simp [fromList_thm_var_cmp]
QED

Theorem lookup_initial_si_RegVar_idx_not_0:
 !i regs reg.
 i <> 0 ==> lookup var_cmp (RegVar reg i) (fromList var_cmp (option_flatMap build_si_entry regs)) = NONE
Proof
 Induct_on ‘regs’ >- (EVAL_TAC \\ simp []) \\ PairCases \\ rpt strip_tac \\ simp [option_flatMap_def, build_si_entry_def] \\
 every_case_tac \\ fs [fromList_cons, reg_name_def] \\
 DEP_REWRITE_TAC [lookup_insert_var_cmp] \\ simp [fromList_thm_var_cmp]
QED

Theorem lookup_initial_si_RegVar_idx_not_0':
 !reg regs i v. lookup var_cmp (RegVar reg i) (fromList var_cmp (option_flatMap build_si_entry regs)) = SOME v ==> i = 0
Proof
 (* Terrible but short: *)
 rpt strip_tac \\ qspec_then ‘i’ mp_tac lookup_initial_si_RegVar_idx_not_0 \\
 Cases_on ‘i’ \\ fs [] \\ metis_tac [optionTheory.NOT_NONE_SOME]
QED

Theorem lookup_initial_si_RegVar_mem:
 !regs extenv t reg i v inp tmpnum.
 MEM (t,reg,i,v,inp) regs /\ regs_ok extenv tmpnum regs /\ regs_distinct regs ==>
 lookup var_cmp (RegVar reg i) (fromList var_cmp (option_flatMap build_si_entry regs)) =
 OPTION_MAP SND (build_si_entry (t,reg,i,v,inp))
Proof
 Induct >- (EVAL_TAC \\ simp []) \\ rpt strip_tac \\
 fs [regs_ok_def, regs_distinct_def, option_flatMap_def, build_si_entry_def]
 >- (rveq \\ Cases_on ‘t’ \\ simp [build_si_entry_def]
  >- fs [reg_name_def, lookup_initial_si_RegVar_not_mem]
  \\ fs [fromList_cons, reg_ok_def] \\ DEP_REWRITE_TAC [lookup_insert_var_cmp] \\ simp [fromList_thm_var_cmp])
 \\ TOP_CASE_TAC
  >- drule_first
  \\ PairCases_on ‘h’ \\ Cases_on ‘h0’ \\ fs [reg_name_def, build_si_entry_def] \\ rveq \\ simp [fromList_cons] \\
     fs [MEM_MAP] \\ first_x_assum (qspec_then ‘(t,reg,i,v,inp)’ strip_assume_tac) \\ fs [reg_name_def] \\
     DEP_REWRITE_TAC [lookup_insert_var_cmp] \\ simp [fromList_thm_var_cmp] \\ drule_first
QED

Theorem si_prefilleds_initial_si:
 !regs extenv tmpnum.
 regs_ok extenv tmpnum regs /\ regs_distinct regs ==>
 si_prefilleds (fromList var_cmp (option_flatMap build_si_entry regs)) regs
Proof
 rw [si_prefilleds_def, EVERY_MEM] \\ PairCases_on ‘e’ \\ simp [si_prefilled_def] \\
 drule_strip lookup_initial_si_RegVar_mem \\ TOP_CASE_TAC \\ fs [build_si_entry_def]
QED

Theorem lookup_initial_si_RegVar_array:
 !reg i regs inps extenv tmpnum.
 regs_ok extenv tmpnum regs /\ regs_distinct regs /\
 lookup var_cmp (RegVar reg i) (fromList var_cmp (option_flatMap build_si_entry regs)) = SOME (ArrayInp inps) ==>
 i = 0 /\
 ∃v inp. MEM (CArray_t (LENGTH inps),reg,0,v,inp) regs /\
         ArrayInp inps = SND (THE (build_si_entry (CArray_t (LENGTH inps),reg,0,v,inp)))
Proof
 rpt strip_tac' \\ drule_strip lookup_initial_si_RegVar_idx_not_0' \\
 reverse (Cases_on ‘MEM reg (MAP reg_name regs)’) >- fs [lookup_initial_si_RegVar_not_mem] \\
 fs [MEM_reg_regs_shape] \\ drule_strip regs_ok_RegVar_idx_0 \\ drule_strip lookup_initial_si_RegVar_mem \\
 Cases_on ‘t’ \\ fs [build_si_entry_def] \\
 reverse (Cases_on ‘n = LENGTH inps’) >- metis_tac [LENGTH_GENLIST] \\ rveq \\
 asm_exists_tac \\ fs []
QED

Theorem build_si_entry_SOME:
 !t reg v inp inps.
 build_si_entry (t,reg,0,v,inp) = SOME inps <=>
 ?l. t = CArray_t l /\ inps = (RegVar reg 0,ArrayInp (GENLIST (\i. VarInp (RegVar reg i) NONE) l))
Proof
 rw [build_si_entry_def] \\ TOP_CASE_TAC \\ metis_tac []
QED

Theorem blasterstate_ok_initial_si:
 !regs extenv n tmpnum.
 regs_ok extenv tmpnum regs /\ regs_distinct regs ==>
 blasterstate_ok (fromList var_cmp (option_flatMap build_si_entry regs)) n n
Proof
 rw [blasterstate_ok_def, fromList_thm_var_cmp] \\ Cases_on ‘var’ \\
 fs [lookup_initial_si_NetVar, lookup_initial_si_RegVar_bool] \\
 drule_strip lookup_initial_si_RegVar_array \\ fs [build_si_entry_def] \\
 pop_assum (fn th => once_rewrite_tac [th]) \\ simp [EVERY_GENLIST, cell_input_lt_def, var_lt_def]
QED

Theorem si_wf_initial_si:
 !regs extenv tmpnum.
 regs_ok extenv tmpnum regs /\ regs_distinct regs ==>
 si_wf (fromList var_cmp (option_flatMap build_si_entry regs))
Proof
 rw [si_wf_def, lookup_initial_si_NetVar, lookup_initial_si_RegVar_idx_not_0, lookup_initial_si_RegVar_bool] \\
 drule_strip lookup_initial_si_RegVar_array \\ fs [build_si_entry_def]
QED

Theorem netlist_overlap_si_initial_si:
 !regs extenv tmpnum nl.
 regs_ok extenv tmpnum regs /\ regs_distinct regs ==>
 netlist_overlap_si (fromList var_cmp (option_flatMap build_si_entry regs)) tmpnum nl
Proof
 rw [netlist_overlap_si_def, lookup_initial_si_NetVar, lookup_initial_si_bool] \\ 
 Cases_on ‘var’ \\ fs [lookup_initial_si_NetVar] \\ drule_strip lookup_initial_si_RegVar_array \\
 fs [build_si_entry_def] \\ first_assum (once_rewrite_tac o sing) \\ simp [EVERY_GENLIST] \\
 simp [bsi_cell_input_ok_def, cell_input_lt_def, cell_input_ge_def, var_lt_def, var_ge_def]
QED

(** Top level thm **)

Theorem blast_circuit_correct:
 !circuit circuit' blast_s n fext fbits s tmpnum.
 blast_circuit circuit tmpnum = INR (circuit', blast_s) /\
 circuit_run fext fbits circuit n = INR s /\
 rtltype_extenv (circuit_extenv circuit) fext /\
 circuit_ok 0 tmpnum circuit /\ circuit_sorted circuit /\ deterministic_circuit circuit ==>
 blasted_circuit circuit' ∧
 ?s'. circuit_run fext fbits circuit' n = INR s' /\
      blast_reg_rel blast_s.si s s'
Proof
 Cases \\ rename1 `Circuit extenv regs nl` \\
 simp [blast_circuit_def, circuit_extenv_def, circuit_ok_def, circuit_sorted_def, deterministic_circuit_def] \\
 rpt strip_tac' \\
 pairarg_tac \\ fs [sum_bind_INR] \\ rveq \\
 fs [circuit_run_def, sum_bind_INR] \\

 drule_strip blast_netlist_correct \\ simp [] \\ disch_then drule_strip \\
 impl_tac >- (drule_strip blasterstate_ok_initial_si \\ simp []) \\ strip_tac \\ rveq \\

 conj_tac >- (drule_strip blast_regs_distinct \\ simp [blasted_circuit_def]) \\

 drule_strip blast_regs_init_correct \\ disch_then (qspec_then ‘<|env := []; fbits := fbits|>’ mp_tac) \\
 simp [blast_reg_rel_nil, only_regs_nil] \\ impl_tac >- (conj_tac
 >- (rw [si_wf_def, lookup_initial_si_RegVar_idx_not_0, lookup_initial_si_bool] \\
     drule_strip lookup_initial_si_RegVar_array \\ fs [build_si_entry_def])
 \\ drule_strip si_prefilleds_cong \\ metis_tac [si_prefilleds_initial_si]) \\ strip_tac \\

 qpat_x_assum ‘init_run _ regs = _’ assume_tac \\
 drule_strip init_run_only_regs_ok \\ impl_tac >- simp [only_regs_nil] \\ strip_tac \\

 drule_strip blast_netlist_correct_run \\ disch_then (qspecl_then [‘bs'’, ‘tmpnum’] mp_tac) \\ simp [] \\
 ‘si_wf blast_s.si’ by metis_tac [si_wf_def, lookup_initial_si_bool, si_wf_initial_si] \\
 impl_tac >- metis_tac [blast_rel_only_regs, blast_rel_blast_reg_rel, blast_reg_rel_blast_rel, si_wf_initial_si, si_prefilleds_initial_si, netlist_overlap_si_initial_si, blasterstate_ok_initial_si] \\
 strip_tac \\ simp [] \\
 metis_tac [blast_reg_rel_only_regs, si_wf_initial_si]
QED

val _ = export_theory ();
