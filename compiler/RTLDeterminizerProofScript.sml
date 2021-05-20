open hardwarePreamble;

open balanced_mapTheory;

open sumExtraTheory oracleTheory RTLTheory RTLTypeTheory RTLPropsTheory RTLDeterminizerTheory;

val _ = new_theory "RTLDeterminizerProof";

val lookup_insert_num_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) lookup_insert) comparisonTheory.num_cmp_good
 |> REWRITE_RULE [comparisonTheory.num_cmp_antisym];

val insert_thm_num_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) (SPEC_ALL insert_thm)) comparisonTheory.num_cmp_good;

(** Pass 1 proof **)

Definition covers_ndetcell_def:
 (covers_ndetcell preprocessing si (NDetCell out t) ⇔
  case lookup num_cmp out si of
    NONE => F
  | SOME (TBD t') => t' = t
  | SOME (HBD v) => rtltype_v v t) ∧
 (covers_ndetcell preprocessing si (CellMux out _ _ _) ⇔
  preprocessing ⇒ lookup num_cmp out si = NONE) ∧
 (covers_ndetcell preprocessing si cell ⇔ EVERY (λout. lookup num_cmp out si = NONE) (cell_output cell))
End

Theorem covers_ndetcell_preprocessing:
 ∀cell si. covers_ndetcell T si cell ⇒ covers_ndetcell F si cell
Proof
 Cases \\ rw [covers_ndetcell_def]
QED

Theorem cell_input_tbd_SOME:
 ∀inp si t n.
 cell_input_tbd si inp = SOME (t, n) ⇒
 ∃idx. inp = VarInp (NetVar n) idx ∧ lookup num_cmp n si = SOME (TBD t)
Proof
 Cases \\ simp [cell_input_tbd_def] \\
 rename1 ‘VarInp var idx’ \\ Cases_on ‘var’ \\ simp [cell_input_tbd_def] \\ rpt gen_tac \\
 every_case_tac \\ rw [] \\ rw []
QED

Theorem find_fills_step:
 ∀nl si si' n.
 find_fills si nl = INR si' ∧ ~MEM n (FLAT (MAP cell_output nl)) ∧
 invariant num_cmp si ⇒
 (lookup num_cmp n si = NONE ⇒ lookup num_cmp n si' = NONE) ∧
 (∀v. lookup num_cmp n si = SOME (HBD v) ⇒ lookup num_cmp n si' = SOME (HBD v)) ∧
 (∀t. lookup num_cmp n si = SOME (TBD t) ⇒
      lookup num_cmp n si' = SOME (TBD t) ∨ ∃v. lookup num_cmp n si' = SOME (HBD v) ∧ rtltype_v v t)
Proof
 Induct \\ simp [find_fills_def] \\ rpt gen_tac \\ every_case_tac \\ simp [sum_bind_INR, cell_output_def] \\
 rpt strip_tac' \\
 drule_first \\ simp [insert_thm_num_cmp, lookup_insert_num_cmp] \\
 fs [has_rtltype_v_correct, cell_input_tbd_def] \\
 drule_strip cell_input_tbd_SOME \\ fs [] \\ rw []
QED

Definition netlist_unprocessed_def:
 netlist_unprocessed si nl ⇔ EVERY (λcell. EVERY (λout. lookup num_cmp out si = NONE) (cell_output cell)) nl
End

Theorem netlist_unprocessed_empty:
 ∀nl. netlist_unprocessed empty nl
Proof
 rw [netlist_unprocessed_def, empty_def, lookup_def]
QED

Theorem netlist_unprocessed_cons:
 ∀si c cs.
 netlist_unprocessed si (c::cs) ⇔ EVERY (λout. lookup num_cmp out si = NONE) (cell_output c) ∧
                                  netlist_unprocessed si cs
Proof
 rw [netlist_unprocessed_def]
QED

Theorem netlist_unprocessed_insert:
 ∀nl si n entry.
 netlist_unprocessed si nl ∧ ~MEM n (FLAT (MAP cell_output nl)) ∧ invariant num_cmp si ⇒
 netlist_unprocessed (insert num_cmp n entry si) nl
Proof
 rw [netlist_unprocessed_def, EVERY_MEM, MEM_FLAT, MEM_MAP, lookup_insert_num_cmp] \\ metis_tac []
QED

Theorem netlist_unprocessed_already_processed:
 ∀nl si n entry. netlist_unprocessed si nl ∧ lookup num_cmp n si = SOME entry ⇒ ¬MEM n (FLAT (MAP cell_output nl))
Proof
 rw [netlist_unprocessed_def, EVERY_MEM, MEM_FLAT, MEM_MAP] \\ metis_tac [optionTheory.NOT_NONE_SOME]
QED

Theorem find_fills_correct:
 ∀nl si si'.
 find_fills si nl = INR si' ∧ ALL_DISTINCT (FLAT (MAP cell_output nl)) ∧
 netlist_unprocessed si nl ∧
 invariant num_cmp si ⇒
 EVERY (covers_ndetcell T si') nl ∧
 invariant num_cmp si'
Proof
 Induct >- simp [find_fills_def] \\
 Cases \\ simp [find_fills_def, sum_bind_INR, cell_output_def, covers_ndetcell_def, netlist_unprocessed_cons] \\
 rpt strip_tac'

 >- (* NDetCell *)
 (drule_strip netlist_unprocessed_insert \\ drule_first \\ simp [insert_thm_num_cmp] \\ strip_tac \\
 drule_strip find_fills_step \\ simp [insert_thm_num_cmp, lookup_insert_num_cmp] \\ rw [] \\ rw [])

 \\ (* Cells with simple proofs *)
 TRY (drule_first \\ drule_strip find_fills_step \\ simp [] \\ NO_TAC)

 >- (* CellMux *)
 (every_case_tac \\ drule_first \\ rveq \\ simp [] \\ drule_strip find_fills_step \\
 fs [insert_thm_num_cmp, lookup_insert_num_cmp, cell_input_tbd_def] \\
 drule_strip cell_input_tbd_SOME \\ fs [] \\

 drule_strip netlist_unprocessed_already_processed \\
 drule_strip netlist_unprocessed_insert \\ simp [] \\
 Cases_on ‘n = r’ \\ rveq \\ fs [])

 \\ (* Carry4 *)
 metis_tac [find_fills_step]
QED

(** Pass 2 proof **)

Theorem build_zero_type_correct:
 !t. rtltype_v (build_zero t) t
Proof
 Cases \\ rw [build_zero_def, rtltype_v_cases]
QED

(*Theorem only_regs_cset_var_RegVar:
 ∀cenv reg i v. only_regs cenv ⇒ only_regs (cset_var cenv (RegVar reg i) v)
Proof
 rw [only_regs_def, cget_var_cset_var]
QED*)

Theorem rtl_nd_value_same_shape:
 ∀fbits1 fbits1' fbits2 fbits2' t v v'.
 rtl_nd_value fbits1 t = (v, fbits1') ∧ rtl_nd_value fbits2 t = (v', fbits2') ⇒ same_shape v v'
Proof
 metis_tac [rtl_nd_value_type_correct, rtltype_v_same_shape]
QED

Theorem cget_fext_var_same_shape:
 ∀v1 v1' v2 idx.
 cget_fext_var idx v1 = INR v1' ∧ same_shape v1 v2 ⇒ ∃v2'. cget_fext_var idx v2 = INR v2' ∧ same_shape v1' v2'
Proof
 rw [cget_fext_var_def] \\ every_case_tac \\ fs [same_shape_def, sum_map_INR, sum_revEL_INR] \\ rw [same_shape_def]
QED

Definition det_rel_def:
 det_rel si cenvold cenv_det cenv <=>
  (* cenv_det <-> cenvold *)
  (!n v.
   lookup num_cmp n si = NONE ∧ cget_var cenvold (NetVar n) = INR v ⇒
   ∃v'. cget_var cenv_det (NetVar n) = INR v' ∧ same_shape v v') ∧

  (!reg i v.
   cget_var cenvold (RegVar reg i) = INR v ⇒
   ∃v'. cget_var cenv_det (RegVar reg i) = INR v' ∧ same_shape v v') ∧

  (* cenv <-> cenvold *)
  (!n v.
   cget_var cenvold (NetVar n) = INR v ⇒
   ∃v'. cget_var cenv (NetVar n) = INR v' ∧ same_shape v v') ∧

  (!t n v.
   lookup num_cmp n si = SOME (TBD t) ∧ cget_var cenvold (NetVar n) = INR v ⇒
   cget_var cenv (NetVar n) = INR $ build_zero t) ∧

  (!newv n v.
   lookup num_cmp n si = SOME (HBD newv) ∧ cget_var cenvold (NetVar n) = INR v ⇒
   cget_var cenv (NetVar n) = INR newv) ∧

  (* cenv_det <-> cenv *)
  (!n v.
   lookup num_cmp n si = NONE ∧ cget_var cenv_det (NetVar n) = INR v ⇒
   cget_var cenv (NetVar n) = INR v) ∧

  (!reg i.
   cget_var cenv (RegVar reg i) = cget_var cenv_det (RegVar reg i))
End

Theorem det_rel_fbits:
 ∀si cenvold cenv_det cenv fbits.
 (det_rel si (cenvold with fbits := fbits) cenv_det cenv ⇔ det_rel si cenvold cenv_det cenv) ∧
 (det_rel si cenvold (cenv_det with fbits := fbits) cenv ⇔ det_rel si cenvold cenv_det cenv) ∧
 (det_rel si cenvold cenv_det (cenv with fbits := fbits) ⇔ det_rel si cenvold cenv_det cenv)
Proof
 rw [det_rel_def, cget_var_fbits, cell_inp_run_fbits]
QED

Theorem det_rel_cset_var:
 ∀si cenvold cenv_det cenv v v' out.
 det_rel si cenvold cenv_det cenv ∧ same_shape v' v ∧ lookup num_cmp out si = NONE ⇒
 det_rel si (cset_var cenvold (NetVar out) v) (cset_var cenv_det (NetVar out) v') (cset_var cenv (NetVar out) v')
Proof
 rw [det_rel_def, cget_var_cset_var] \\ rw [] \\ fs [same_shape_sym]
QED

Theorem det_rel_insert_cset_var:
 ∀si cenvold cenv_det cenv v1 v2 n.
 det_rel si cenvold cenv_det cenv ∧ same_shape v1 v2 ∧ invariant num_cmp si ⇒
 det_rel (insert num_cmp n (HBD v2) si) (cset_var cenvold (NetVar n) v1) cenv_det (cset_var cenv (NetVar n) v2)
Proof
 simp [det_rel_def, cget_var_cset_var, lookup_insert_num_cmp] \\ rpt strip_tac \\ every_case_tac \\ fs []
QED

Definition det_rel_reg_def:
 det_rel_reg cenvold cenv_det cenv <=>
 (∀reg i. cget_var cenv_det (RegVar reg i) = cget_var cenv (RegVar reg i)) ∧
 (∀reg i v. cget_var cenvold (RegVar reg i) = INR v ⇒
            ∃v'. cget_var cenv_det (RegVar reg i) = INR v' ∧ same_shape v v')
End

Theorem det_rel_reg_fbits:
 ∀cenvold cenv_det cenv fbits.
 (det_rel_reg (cenvold with fbits := fbits) cenv_det cenv ⇔ det_rel_reg cenvold cenv_det cenv) ∧
 (det_rel_reg cenvold (cenv_det with fbits := fbits) cenv ⇔ det_rel_reg cenvold cenv_det cenv) ∧
 (det_rel_reg cenvold cenv_det (cenv with fbits := fbits) ⇔ det_rel_reg cenvold cenv_det cenv)
Proof
 rw [det_rel_reg_def, cget_var_fbits]
QED

Triviality det_rel_reg_cong3:
 ∀cenv_old cenv_det cenv cenv'.
 det_rel_reg cenv_old cenv_det cenv ∧ cenv'.env = cenv.env ⇒ det_rel_reg cenv_old cenv_det cenv'
Proof
 rw [det_rel_reg_def] \\ rw [cget_var_def]
QED

Theorem det_rel_reg_cset_var:
 !cenvold cenv_det cenv var v v'.
 det_rel_reg cenvold cenv_det cenv ∧ same_shape v' v ⇒
 det_rel_reg (cset_var cenvold var v') (cset_var cenv_det var v) (cset_var cenv var v)
Proof
 rw [det_rel_reg_def, cget_var_cset_var] \\ rw [] \\ metis_tac []
QED

Theorem det_rel_det_rel_reg:
 ∀si cenvold cenv_det cenv. det_rel si cenvold cenv_det cenv ⇒ det_rel_reg cenvold cenv_det cenv
Proof
 rw [det_rel_reg_def, det_rel_def]
QED

Theorem det_rel_reg_det_rel:
 ∀si cenvold cenv_det cenv.
 det_rel_reg cenvold cenv_det cenv ∧ only_regs cenvold ∧ only_regs cenv_det ⇒ det_rel si cenvold cenv_det cenv
Proof
 rw [det_rel_reg_def, only_regs_def, det_rel_def]
QED

Theorem ndetcell_run_build_zero:
 ∀t fbits cenv.
 ndetcell_run (cenv with fbits := replace_prefix fbits (K F) (rtltype_v_size t)) t =
  (cenv with fbits := fbits, build_zero t)
Proof
 Cases \\ rw [ndetcell_run_def, rtltype_v_size_def, build_zero_def]
 >- (rw [oracle_bit_def, rtlstate_component_equality, shift_seq_replace_prefix] \\ EVAL_TAC)
 \\ rw [oracle_bits_genlist, rtlstate_component_equality, shift_seq_replace_prefix] \\
    match_mp_tac GENLIST_CONG \\ rw [replace_prefix_def]
QED

Definition value_to_fbits_def:
 (value_to_fbits (CBool b) t = b) ∧
 (value_to_fbits (CArray bs) t = EL t bs)
End

Triviality ndetcell_run_value_to_fbits_lem1:
 ∀f n fbits. GENLIST (replace_prefix fbits f n) n = GENLIST f n
Proof
 rw [GENLIST_FUN_EQ, replace_prefix_def]
QED

Triviality ndetcell_run_value_to_fbits_lem2:
 ∀vs. GENLIST (value_to_fbits (CArray vs)) (LENGTH vs) = vs
Proof
 gen_tac \\ match_mp_tac GENLIST_EL \\ simp [value_to_fbits_def]
QED

Theorem ndetcell_run_value_to_fbits:
 ∀t v fbits cenv.
 rtltype_v v t ⇒
 ndetcell_run (cenv with fbits := replace_prefix fbits (value_to_fbits v) (value_bits v)) t =
  (cenv with fbits := fbits, v)
Proof
 Cases \\ rw [rtltype_v_cases] \\ simp [ndetcell_run_def, value_bits_def]
 >- (simp [oracle_bit_def, shift_seq_replace_prefix] \\ EVAL_TAC)
 \\ rw [oracle_bits_genlist, rtlstate_component_equality, shift_seq_replace_prefix] \\
    simp [ndetcell_run_value_to_fbits_lem1, ndetcell_run_value_to_fbits_lem2]
QED

Theorem cell_input_lt_build_const:
 ∀v idx max. cell_input_lt (build_const v idx) max
Proof
 Cases \\ Cases \\ simp [cell_input_lt_def, build_const_def]
QED

Theorem cell_input_lt_build_zero_with_idx:
 ∀t idx max. cell_input_lt (build_zero_with_idx t idx) max
Proof
 Cases \\ Cases \\ simp [cell_input_lt_def, build_zero_with_idx_def]
QED

Theorem cell_input_lt_rtl_determinizer_inp:
 ∀inp si max. cell_input_lt inp max ⇒ cell_input_lt (rtl_determinizer_inp si inp) max
Proof
 Cases \\ rw [rtl_determinizer_inp_def] \\ Cases_on ‘v’ \\ simp [rtl_determinizer_inp_def] \\
 every_case_tac \\ simp [cell_input_lt_def, cell_input_lt_build_const, cell_input_lt_build_zero_with_idx]
QED

Theorem cell_input_covered_by_extenv_build_const:
 ∀v idx extenv. cell_input_covered_by_extenv extenv (build_const v idx)
Proof
 Cases \\ Cases \\ simp [cell_input_covered_by_extenv_def, build_const_def]
QED

Theorem cell_input_covered_by_extenv_build_zero_with_idx:
 ∀t idx extenv. cell_input_covered_by_extenv extenv (build_zero_with_idx t idx)
Proof
 Cases \\ Cases \\ simp [cell_input_covered_by_extenv_def, build_zero_with_idx_def]
QED

Theorem cell_input_covered_by_extenv_rtl_determinizer_inp:
 ∀inp extenv si.
 cell_input_covered_by_extenv extenv inp ⇒ cell_input_covered_by_extenv extenv (rtl_determinizer_inp si inp)
Proof
 Cases \\ rw [rtl_determinizer_inp_def] \\ Cases_on ‘v’ \\ simp [rtl_determinizer_inp_def] \\
 every_case_tac \\ simp [cell_input_covered_by_extenv_def, cell_input_covered_by_extenv_build_const, cell_input_covered_by_extenv_build_zero_with_idx]
QED

Triviality MIN_a_min_b:
 ∀a b. MIN (a - b) a = a - b
Proof
 simp [arithmeticTheory.MIN_DEF]
QED

Theorem cell_inp_run_rtl_determinizer_inp:
 ∀inp fext cenvold cenv_det cenv si v.
 cell_inp_run fext cenvold inp = INR v ∧
 det_rel si cenvold cenv_det cenv ⇒
 ∃v'. cell_inp_run fext cenv_det (rtl_determinizer_inp si inp) = INR v' ∧
      cell_inp_run fext cenv inp = INR v' ∧
      same_shape v' v
Proof
 Cases \\ rw [cell_inp_run_def, rtl_determinizer_inp_def, same_shape_refl] \\
 rename1 ‘VarInp var idx’ \\ Cases_on ‘var’ \\
 fs [det_rel_def, cell_inp_run_def, rtl_determinizer_inp_def, sum_bind_INR]
 >- (drule_first \\ rfs [] \\ drule_strip cget_fext_var_same_shape \\ simp [same_shape_sym])
 \\ TOP_CASE_TAC
 >- (rpt drule_first \\ disch_then drule_strip \\ fs [cell_inp_run_def, sum_bind_def] \\ rveq \\
    imp_res_tac cget_fext_var_same_shape \\ simp [same_shape_sym])
 \\ TOP_CASE_TAC \\ rpt drule_last \\ rveq
 >- (Cases_on ‘r’ \\ fs [build_zero_def] \\ rveq \\ fs [same_shape_inv] \\ rveq \\
     fs [cget_fext_var_def, CaseEq "cell_input_idx", build_zero_with_idx_def, cell_inp_run_def] \\
     fs [sum_map_INR, sum_revEL_INR, revEL_GENLIST] \\
     rw [same_shape_def, DROP_GENLIST, TAKE_GENLIST, MIN_a_min_b])
 \\ Cases_on ‘v''’ \\ Cases_on ‘idx’ \\ fs [same_shape_inv] \\ rveq \\ fs [cget_fext_var_def] \\
    fs [sum_map_INR, sum_revEL_INR] \\
    rw [build_const_def, cell_inp_run_def, same_shape_def, rev_slice_def]
QED

Theorem cell1_run_same_shape:
 ∀v v' f. cell1_run f v = INR v' ⇒ same_shape v' v
Proof
 Cases \\ simp [cell1_run_def, same_shape_def]
QED

Theorem cell1_run_always_INR:
 ∀v f. ∃v'. cell1_run f v = (INR v' : error + value) ∧ same_shape v' v
Proof
 Cases \\ simp [cell1_run_def, same_shape_def]
QED

Theorem cell2_run_same_shape:
 ∀v1 v2 v3 cell2 v1' v2'.
 cell2_run cell2 v1 v2 = INR v3 ∧
 same_shape v1' v1 ∧ same_shape v2' v2 ⇒
 ∃v3'. cell2_run cell2 v1' v2' = INR v3' ∧ same_shape v3' v3
Proof
 rpt Cases \\ simp [same_shape_def, cell2_run_def, sum_bind_INR, sum_check_INR] \\
 rw [] \\ simp [bitstringTheory.length_fixwidth]
QED

Theorem cellMux_run_same_shape_same_input:
 ∀v1 v1' v2 v2' v3 v4.
 cellMux_run v1 v2 v3 = INR v4 ∧ same_shape v1' v1 ∧ same_shape v2' v2 ⇒
 same_shape v4 v2 ∧ ∃b. v1 = CBool b ∧ cellMux_run v1' v2' v2' = INR v2'
Proof
 rpt Cases \\ simp [cellMux_run_def, sum_bind_INR, sum_check_INR, same_shape_inv] \\
 rw [] \\ simp [sum_check_def, sum_bind_def, cellMux_run_def]
QED

Theorem cellMux_run_same_shape:
 ∀v1 v1' v2 v2' v3 v3' v4.
 cellMux_run v1 v2 v3 = INR v4 ∧ same_shape v1' v1 ∧ same_shape v2' v2 ∧ same_shape v3' v3 ⇒
 same_shape v4 v2 ∧ ∃v4'. cellMux_run v1' v2' v3' = INR v4' ∧ same_shape v4' v4
Proof
 rpt Cases \\ simp [cellMux_run_def, sum_bind_INR, sum_check_INR, same_shape_inv] \\ metis_tac []
QED

Theorem covers_ndetcell_insert_not_member:
 ∀nl n entry si b.
 EVERY (covers_ndetcell b si) nl ∧ ¬MEM n (FLAT (MAP cell_output nl)) ∧ invariant num_cmp si ⇒
 EVERY (covers_ndetcell b (insert num_cmp n entry si)) nl
Proof
 rw [EVERY_MEM] \\ drule_first \\ ‘~MEM n (cell_output e)’ by metis_tac [MEM_FLAT, MEM_MAP] \\
 Cases_on ‘e’ \\ fs [covers_ndetcell_def, lookup_insert_num_cmp, cell_output_def]
QED

Triviality cell_run_CellMux_rtl_determinizer_inp:
 cell_run fext cenvold (CellMux out cin tin fin) = INR cenvold' ∧
 det_rel si cenvold cenv_det cenv ⇒
 ∃v. cenvold' = cset_var cenvold (NetVar out) v ∧
 ∃v'. cell_run fext cenv_det (CellMux out (rtl_determinizer_inp si cin)
                                          (rtl_determinizer_inp si tin)
                                          (rtl_determinizer_inp si fin)) = INR (cset_var cenv_det (NetVar out) v') ∧
      ∀fbits. cell_run fext (cenv with fbits := fbits) (CellMux out cin tin fin) =
              INR (cset_var cenv (NetVar out) v' with fbits := fbits) ∧
              same_shape v' v
Proof
 rw [cell_run_def, sum_bind_INR] \\
 qspec_then ‘cin’ assume_tac cell_inp_run_rtl_determinizer_inp \\ pop_assum drule_strip \\
 qspec_then ‘tin’ assume_tac cell_inp_run_rtl_determinizer_inp \\ pop_assum drule_strip \\
 qspec_then ‘fin’ assume_tac cell_inp_run_rtl_determinizer_inp \\ pop_assum drule_strip \\
 simp [cell_inp_run_fbits, cset_var_fbits] \\ drule_strip cellMux_run_same_shape \\ metis_tac []
QED

Theorem cellArrayWrite_run_same_shape:
 ∀v1 v1' v2 v2' v3 idx.
 cellArrayWrite_run v1 idx v2 = INR v3 ∧
 same_shape v1' v1 ∧ same_shape v2' v2 ⇒
 ∃v3'. cellArrayWrite_run v1' idx v2' = INR v3' ∧ same_shape v3' v3
Proof
 ntac 5 Cases \\ simp [cellArrayWrite_run_def, same_shape_def] \\ rw [] \\ simp [length_revLUPDATE]
QED

Theorem rtl_determinizer_netlist_correct_cells_run:
 ∀(extenv : (string # rtltype) list) min max nl nl_det si si'.
 rtl_determinizer_netlist si nl = (si', nl_det) ∧
 netlist_ok extenv min max nl ∧
 netlist_sorted nl ∧
 invariant num_cmp si ∧
 EVERY (covers_ndetcell T si) nl ⇒
 netlist_ok extenv min max nl_det ∧
 netlist_sorted nl_det ∧
 invariant num_cmp si' ∧
 (∀n. ~MEM n (FLAT (MAP cell_output nl)) ⇒ lookup num_cmp n si' = lookup num_cmp n si ∧
                                           ~MEM n (FLAT (MAP cell_output nl_det))) ∧
 EVERY (covers_ndetcell F si') nl ∧
 (∀fext cenv_det cenvold cenvold' cenv.
 sum_foldM (cell_run fext) cenvold nl = INR cenvold' ∧ det_rel si cenvold cenv_det cenv ⇒
 ∃cenv_det'. sum_foldM (cell_run fext) cenv_det nl_det = INR cenv_det' ∧
             ∃fbits cenv'. sum_foldM (cell_run fext) (cenv with fbits := fbits) nl = INR cenv' ∧
                           det_rel si' cenvold' cenv_det' cenv')
Proof
 ntac 3 gen_tac \\ Induct \\ simp [rtl_determinizer_netlist_def, sum_foldM_def, sum_bind_INR, det_rel_fbits] \\
 rpt strip_tac' \\ drule_strip netlist_sorted_all_distinct \\
 Cases_on ‘h’ \\ fs [rtl_determinizer_cell_def, ALL_DISTINCT, cell_output_def, netlist_ok_cons, netlist_sorted_cons]

 >- (* NDetCell *)
 (rename1 ‘NDetCell out t’ \\
 qpat_x_assum ‘covers_ndetcell _ _ _’ mp_tac \\ simp [covers_ndetcell_def] \\ ntac 2 TOP_CASE_TAC \\ strip_tac

 >- (* TBD *)
 (rveq \\

 pairarg_tac \\ fs [] \\ rveq \\

 drule_first \\ rw [] \\
 drule_first \\ disch_then (qspecl_then [‘cenv_det’, ‘cset_var cenv (NetVar out) (build_zero r)’] mp_tac) \\
 impl_tac >- (fs [cell_run_def] \\ pairarg_tac \\ fs [] \\ rveq \\ drule_strip ndetcell_run_type_drule \\
              fs [det_rel_def] \\ rw [cget_var_cset_var, cget_var_fbits] \\
              metis_tac [build_zero_type_correct, rtltype_v_same_shape]) \\
 strip_tac \\ simp [] \\

 qexists_tac ‘replace_prefix fbits (K F) (rtltype_v_size r)’ \\
 simp [cell_run_def, ndetcell_run_build_zero, cset_var_fbits])

 >- (* HBD, proof duplicated here that can probably be fixed at least a little *)
 (pairarg_tac \\ fs [] \\ rveq \\

 drule_first \\ rw [] \\
 drule_first \\ disch_then (qspecl_then [‘cenv_det’, ‘cset_var cenv (NetVar out) v’] mp_tac) \\
 impl_tac >- (fs [cell_run_def] \\ pairarg_tac \\ fs [] \\ rveq \\ drule_strip ndetcell_run_type_drule \\
              fs [det_rel_def] \\ rw [cget_var_cset_var, cget_var_fbits] \\
              metis_tac [build_zero_type_correct, rtltype_v_same_shape]) \\
 strip_tac \\ simp [] \\

 qexists_tac ‘replace_prefix fbits (value_to_fbits v) (value_bits v)’ \\
 simp [cell_run_def, ndetcell_run_value_to_fbits, cset_var_fbits]))

 >- (* Cell1 *)
 (rename1 ‘Cell1 cell1 out in1’ \\ Cases_on ‘cell1’ \\
 pairarg_tac \\ fs [] \\ rveq \\

 drule_first \\ fs [covers_ndetcell_def, cell_output_def] \\ rpt conj_tac
 >- fs [netlist_ok_cons, cell_covered_by_extenv_def, cell_ok_def,
        cell_input_covered_by_extenv_rtl_determinizer_inp, cell_input_lt_rtl_determinizer_inp]
 >- (fs [netlist_sorted_cons, cell_output_def] \\ metis_tac []) \\

 rw [sum_foldM_INR, cell_run_def, sum_bind_INR, cell_inp_run_fbits] \\
 drule_strip cell_inp_run_rtl_determinizer_inp \\ simp [] \\
 qspecl_then [‘v'’, ‘$~’] strip_assume_tac cell1_run_always_INR \\ simp [cset_var_fbits] \\

 drule_first \\
 disch_then (qspecl_then [‘cset_var cenv_det (NetVar out) v''’, ‘cset_var cenv (NetVar out) v''’] mp_tac) \\
 impl_tac >- metis_tac [det_rel_cset_var, same_shape_trans, same_shape_sym, cell1_run_same_shape] \\
 strip_tac \\ rpt asm_exists_tac)

 >- (* Cell2 *)
 (rename1 ‘Cell2 cell2 out in1 in2’ \\
  pairarg_tac \\ fs [] \\ rveq \\

  drule_first \\ fs [covers_ndetcell_def, cell_output_def] \\ rpt conj_tac
  >- fs [netlist_ok_cons, cell_covered_by_extenv_def, cell_ok_def,
         cell_input_covered_by_extenv_rtl_determinizer_inp, cell_input_lt_rtl_determinizer_inp]
  >- (fs [netlist_sorted_cons, cell_output_def] \\ metis_tac []) \\

  rw [sum_foldM_INR, cell_run_def, sum_bind_INR, cell_inp_run_fbits] \\
  qspec_then ‘in1’ assume_tac cell_inp_run_rtl_determinizer_inp \\ drule_first \\
  qspec_then ‘in2’ assume_tac cell_inp_run_rtl_determinizer_inp \\ drule_first \\
  drule_strip cell2_run_same_shape \\
  simp [cset_var_fbits] \\
  drule_first \\
  rename1 ‘cset_var cenv_det (NetVar out) v_new’ \\
  disch_then (qspecl_then [‘cset_var cenv_det (NetVar out) v_new’, ‘cset_var cenv (NetVar out) v_new’] mp_tac) \\
  impl_tac >- (match_mp_tac det_rel_cset_var \\ simp []) \\ strip_tac \\
  rfs [] \\ rpt asm_exists_tac)

 >- (* CellMux *)
 (rename1 ‘CellMux out cin tin fin’ \\
 pairarg_tac \\ pop_assum mp_tac \\ rpt TOP_CASE_TAC \\ rpt strip_tac' \\ rveq \\ fs [] \\
 pairarg_tac \\ fs [] \\ rveq

 >- (drule_first \\ simp [insert_thm_num_cmp, covers_ndetcell_insert_not_member] \\ strip_tac \\
     rw [covers_ndetcell_def, lookup_insert_num_cmp] \\     

     fs [cell_run_def, sum_bind_INR] \\
     qspec_then ‘cin’ assume_tac cell_inp_run_rtl_determinizer_inp \\ pop_assum drule_strip \\
     qspec_then ‘tin’ assume_tac cell_inp_run_rtl_determinizer_inp \\ pop_assum drule_strip \\
     qspec_then ‘fin’ assume_tac cell_inp_run_rtl_determinizer_inp \\ pop_assum drule_strip \\
     rfs [cell_inp_run_fbits, cell_inp_run_def] \\ rveq \\

     drule_strip cellMux_run_same_shape_same_input \\ simp [] \\

     drule_first \\ disch_then (qspecl_then [‘cenv_det’, ‘cset_var cenv (NetVar out) v’] mp_tac) \\
     impl_tac >- metis_tac [det_rel_insert_cset_var, same_shape_trans, same_shape_sym] \\ strip_tac \\

     simp [cset_var_fbits] \\ rpt asm_exists_tac)

 \\ (fs [sum_foldM_INR, covers_ndetcell_def] \\ drule_first \\ rw []
     >- (fs [netlist_ok_cons, cell_covered_by_extenv_def, cell_ok_def,
             cell_input_covered_by_extenv_rtl_determinizer_inp, cell_input_lt_rtl_determinizer_inp] \\
         metis_tac [cell_input_covered_by_extenv_rtl_determinizer_inp, cell_input_lt_rtl_determinizer_inp])
     >- (fs [netlist_sorted_cons, cell_output_def] \\ metis_tac [])
     >- simp [cell_output_def] \\

    drule_strip cell_run_CellMux_rtl_determinizer_inp \\
    drule_first \\ rename1 ‘cset_var cenv_det (NetVar out) v_new’ \\
    disch_then (qspecl_then [‘cset_var cenv_det (NetVar out) v_new’, ‘cset_var cenv (NetVar out) v_new’] mp_tac) \\
    impl_tac >- (match_mp_tac det_rel_cset_var \\ simp []) \\ strip_tac \\
    
    rfs [] \\ rpt asm_exists_tac))

 >- (* CellArrayWrite *)
 (rename1 ‘CellArrayWrite out in1 idx in2’ \\
  pairarg_tac \\ fs [] \\ rveq \\

  drule_first \\ fs [covers_ndetcell_def, cell_output_def] \\ rpt conj_tac
  >- fs [netlist_ok_cons, cell_covered_by_extenv_def, cell_ok_def,
         cell_input_covered_by_extenv_rtl_determinizer_inp, cell_input_lt_rtl_determinizer_inp]
  >- (fs [netlist_sorted_cons, cell_output_def] \\ metis_tac []) \\

  rw [sum_foldM_INR, cell_run_def, sum_bind_INR, cell_inp_run_fbits] \\
  qspec_then ‘in1’ assume_tac cell_inp_run_rtl_determinizer_inp \\ drule_first \\
  qspec_then ‘in2’ assume_tac cell_inp_run_rtl_determinizer_inp \\ drule_first \\
  drule_strip cellArrayWrite_run_same_shape \\
  simp [cset_var_fbits] \\
  drule_first \\
  rename1 ‘cset_var cenv_det (NetVar out) v_new’ \\
  disch_then (qspecl_then [‘cset_var cenv_det (NetVar out) v_new’, ‘cset_var cenv (NetVar out) v_new’] mp_tac) \\
  impl_tac >- (match_mp_tac det_rel_cset_var \\ simp []) \\ strip_tac \\
  rfs [] \\ rpt asm_exists_tac)

 \\ (* None-relevant cells *)
 fs [cell_ok_def]
QED

Theorem rtl_determinizer_reg_correct:
 ∀regs fext cenv_reg_old cenv_reg_det cenv_reg cenv_net_old cenv_net_det cenv_net cenv_old si.
 sum_foldM (reg_run fext cenv_net_old) cenv_reg_old regs = INR cenv_old ∧
 det_rel si cenv_net_old cenv_net_det cenv_net ∧
 det_rel_reg cenv_reg_old cenv_reg_det cenv_reg ⇒
 ∃cenv_det. sum_foldM (reg_run fext cenv_net_det) cenv_reg_det (MAP (rtl_determinizer_reg si) regs) = INR cenv_det ∧
            ∃cenv. sum_foldM (reg_run fext cenv_net) cenv_reg regs = INR cenv ∧
                   det_rel_reg cenv_old cenv_det cenv
Proof
 Induct \\ TRY PairCases \\ simp [sum_foldM_def, sum_bind_INR, rtl_determinizer_reg_def, reg_run_def] \\
 rpt strip_tac \\ TOP_CASE_TAC
 >- (fs [] \\ rveq \\ drule_first \\ simp [])
 \\ fs [] \\ fs [sum_bind_INR] \\ rveq \\ drule_strip cell_inp_run_rtl_determinizer_inp \\
    fs [has_rtltype_v_correct] \\ drule_strip rtltype_v_same_shape_rtltype_v \\ simp [] \\
    first_x_assum match_mp_tac \\ rpt asm_exists_tac \\ match_mp_tac det_rel_reg_cset_var \\
    metis_tac [same_shape_sym]
QED

Triviality FILTER_reg_MAP_rtl_determinizer_reg_COMM:
 ∀regs si reg.
 FILTER (λ(var,data). data.reg_type = reg) (MAP (rtl_determinizer_reg si) regs) =
 MAP (rtl_determinizer_reg si) (FILTER (λ(var,data). data.reg_type = reg) regs)
Proof
 simp [rich_listTheory.FILTER_MAP, combinTheory.o_DEF, pairTheory.LAMBDA_PROD, rtl_determinizer_reg_def]
QED

Triviality netlist_ok_netlist_ok_unchanged_lem:
 ∀combs_nl ffs_nl si si' extenv min combs_max ffs_max.
 netlist_ok extenv min combs_max combs_nl ∧
 netlist_ok extenv combs_max ffs_max ffs_nl ∧
 (∀n. ¬MEM n (FLAT (MAP cell_output ffs_nl)) ⇒ lookup num_cmp n si' = lookup num_cmp n si) ⇒
 ∀n. n < combs_max ⇒ lookup num_cmp n si' = lookup num_cmp n si
Proof
 rw [netlist_ok_def, EVERY_MEM] \\ first_x_assum match_mp_tac \\
 strip_tac \\ fs [MEM_FLAT, MEM_MAP] \\ rveq \\
 rpt drule_first \\ fs [cell_ok_alt] \\ drule_first \\ fs [cell_output_ok_def]
QED

Triviality rtl_determinizer_reg_si_cong:
 regs_ok extenv combs_max ffs_max regs ∧
 (∀n. n < combs_max ⇒ lookup num_cmp n si' = lookup num_cmp n si) ⇒
 MAP (rtl_determinizer_reg si') (FILTER (λ(var,data). data.reg_type = PseudoReg) regs) =
 MAP (rtl_determinizer_reg si) (FILTER (λ(var,data). data.reg_type = PseudoReg) regs)
Proof
 rw [regs_ok_def, EVERY_MEM] \\ match_mp_tac MAP_CONG \\ simp [] \\
 PairCases \\ rw [MEM_FILTER, rtl_determinizer_reg_def, reg_metadata_component_equality] \\
 drule_first \\ fs [reg_ok_def] \\
 Cases_on ‘x2.inp’ \\ simp [] \\ Cases_on ‘x’ \\ simp [rtl_determinizer_inp_def] \\
 rename1 ‘VarInp var _’ \\ Cases_on ‘var’ \\ gs [rtl_determinizer_inp_def, cell_input_lt_def, var_lt_def]
QED

Triviality det_rel_reg_det_rel_Psuedo:
 det_rel_reg cenvold' cenv_det' cenv' ∧
 det_rel si cenvold cenv_det cenv ∧
 (∀n. cget_var cenvold' (NetVar n) = cget_var cenvold (NetVar n)) ∧
 (∀n. cget_var cenv_det' (NetVar n) = cget_var cenv_det (NetVar n)) ∧
 (∀n. cget_var cenv' (NetVar n) = cget_var cenv (NetVar n)) ⇒
 det_rel si cenvold' cenv_det' cenv'
Proof
 rw [det_rel_reg_def, det_rel_def]
QED

Theorem rtl_determinizer_netlist_correct_step:
 ∀combs_nl ffs_nl (extenv : (string # rtltype) list) min combs_max ffs_max si si' si'' combs_nl_det ffs_nl_det regs fext cenvold cenvold' cenv_det cenv.
 rtl_determinizer_netlist si combs_nl = (si', combs_nl_det) ∧
 rtl_determinizer_netlist si' ffs_nl = (si'', ffs_nl_det) ∧

 regs_ok extenv combs_max ffs_max regs ∧
 netlist_ok extenv min combs_max combs_nl ∧
 netlist_ok extenv combs_max ffs_max ffs_nl ∧

 netlist_sorted (combs_nl ⧺ ffs_nl) ∧

 invariant num_cmp si ∧

 EVERY (covers_ndetcell T si) combs_nl ∧
 EVERY (covers_ndetcell T si') ffs_nl ∧

 netlist_step fext cenvold combs_nl ffs_nl regs = INR cenvold' ∧
 det_rel_reg cenvold cenv_det cenv ∧ only_regs cenvold ∧ only_regs cenv_det ==>

 netlist_ok extenv min combs_max combs_nl_det ∧
 netlist_ok extenv combs_max ffs_max ffs_nl_det ∧

 netlist_sorted (combs_nl_det ++ ffs_nl_det) ∧

 ∃cenv_det'. netlist_step fext cenv_det combs_nl_det ffs_nl_det (MAP (rtl_determinizer_reg si'') regs) =
             INR cenv_det' ∧
             ∃fbits cenv'. netlist_step fext (cenv with fbits := fbits) combs_nl ffs_nl regs = INR cenv' ∧
                           det_rel si'' cenvold' cenv_det' cenv' (*∧ only_regs cenvold' ∧ only_regs cenv_det'*)
Proof
 simp [netlist_step_def, sum_bind_INR] \\ rpt strip_tac' \\
 rev_drule_strip rtl_determinizer_netlist_correct_cells_run \\
 impl_tac >- fs [netlist_sorted_def, sortingTheory.SORTED_APPEND] \\ strip_tac \\
 drule_strip rtl_determinizer_netlist_correct_cells_run \\
 impl_tac >- fs [netlist_sorted_def, sortingTheory.SORTED_APPEND] \\ strip_tac \\

 simp [] \\ conj_tac >- metis_tac [netlist_sorted_append] \\

 drule_strip det_rel_reg_det_rel \\ first_x_assum (qspec_then ‘si’ assume_tac) \\
 drule_last \\ simp [] \\
 
 drule_strip rtl_determinizer_reg_correct \\
 disch_then (qspecl_then [‘cenv_det'’, ‘cenv'’] mp_tac) \\
 impl_tac >- fs [det_rel_def, det_rel_reg_def] \\ strip_tac \\
 simp [FILTER_reg_MAP_rtl_determinizer_reg_COMM] \\

 qspecl_then [‘combs_nl’, ‘ffs_nl’, ‘si'’, ‘si''’, ‘extenv’] assume_tac netlist_ok_netlist_ok_unchanged_lem \\
 drule_first \\ simp [] \\ strip_tac \\

 drule_strip rtl_determinizer_reg_si_cong \\ simp [] \\

 drule_first \\ disch_then (qspecl_then [‘cenv_det''’, ‘cenv''’] mp_tac) \\
 impl_tac >- (irule det_rel_reg_det_rel_Psuedo \\ metis_tac [regs_run_cget_var_NetVar]) \\ strip_tac \\ simp [] \\
 
 qpat_x_assum ‘sum_foldM (cell_run fext) _ combs_nl = _’ assume_tac \\
 drule_strip cells_run_fbits \\

 qpat_x_assum ‘sum_foldM (cell_run fext) _ ffs_nl = _’ assume_tac \\
 drule_strip cells_run_fbits \\ fs [] \\

 last_x_assum (qspec_then ‘replace_prefix fbits' fbits m’ mp_tac) \\
 impl_tac >- simp [init_seq_eq_replace_prefix, init_seq_eq_sym] \\ strip_tac \\
 simp [PULL_EXISTS] \\ asm_exists_tac \\

 simp [shift_seq_replace_prefix] \\
 drule_strip regs_run_fbits \\ first_x_assum (qspec_then ‘fbits'’ strip_assume_tac) \\ simp []
QED

Theorem rtl_determinizer_netlist_correct_run:
 ∀combs_nl ffs_nl (extenv : (string # rtltype) list) min combs_max ffs_max n si si' si'' combs_nl_det ffs_nl_det regs fext cenvold cenvold' cenv_det cenv.
 rtl_determinizer_netlist si combs_nl = (si', combs_nl_det) ∧
 rtl_determinizer_netlist si' ffs_nl = (si'', ffs_nl_det) ∧

 regs_ok extenv combs_max ffs_max regs ∧
 netlist_ok extenv min combs_max combs_nl ∧
 netlist_ok extenv combs_max ffs_max ffs_nl ∧

 netlist_sorted (combs_nl ⧺ ffs_nl) ∧

 invariant num_cmp si ∧

 EVERY (covers_ndetcell T si) combs_nl ∧
 EVERY (covers_ndetcell T si') ffs_nl ∧

 netlist_run fext cenvold combs_nl ffs_nl regs n = INR cenvold' ∧
 det_rel_reg cenvold cenv_det cenv ∧ only_regs cenvold ∧ only_regs cenv_det ==>

 netlist_ok extenv min combs_max combs_nl_det ∧
 netlist_ok extenv combs_max ffs_max ffs_nl_det ∧

 netlist_sorted (combs_nl_det ++ ffs_nl_det) ∧

 ∃cenv_det'. netlist_run fext cenv_det combs_nl_det ffs_nl_det (MAP (rtl_determinizer_reg si'') regs) n =
             INR cenv_det' ∧
             ∃fbits cenv'. netlist_run fext (cenv with fbits := fbits) combs_nl ffs_nl regs n = INR cenv' ∧
                           det_rel si'' cenvold' cenv_det' cenv' (*∧ only_regs cenvold' ∧ only_regs cenv_det'*)
Proof
 ntac 6 gen_tac \\ Induct \\ simp [netlist_run_def, sum_bind_INR, det_rel_reg_fbits] \\ rpt strip_tac'
 >- (qspecl_then [‘combs_nl’, ‘ffs_nl’] assume_tac rtl_determinizer_netlist_correct_step \\ drule_first \\
     simp [] \\ asm_exists_tac \\ simp []) \\
 drule_first \\ simp [] \\

 qmatch_goalsub_abbrev_tac ‘sum_foldM (reg_run _ cenv_det') cenv_reg_det _’ \\
 drule_strip rtl_determinizer_reg_correct \\ 
 disch_then (qspecl_then [‘cenv_reg_det’, ‘cenv' with env := FILTER (is_RegVar ∘ FST) cenv'.env’] mp_tac) \\
 unabbrev_all_tac \\
 impl_tac >- fs [det_rel_def, det_rel_reg_def, cget_var_def, ALOOKUP_FILTER_FST, is_RegVar_def] \\ strip_tac \\
 simp [FILTER_reg_MAP_rtl_determinizer_reg_COMM] \\

 qspecl_then [‘combs_nl’, ‘ffs_nl’] assume_tac rtl_determinizer_netlist_correct_step \\ drule_first \\
 impl_tac >- (conj_tac \\ match_mp_tac regs_run_only_regs \\
              asm_exists_tac \\ simp [only_regs_FILTER_is_RegVar]) \\ strip_tac \\

 simp [] \\

 drule_strip netlist_run_fbits \\
 first_x_assum (qspec_then ‘replace_prefix fbits' fbits m’ mp_tac) \\
 impl_tac >- simp [init_seq_eq_replace_prefix, init_seq_eq_sym] \\ strip_tac \\
 simp [PULL_EXISTS] \\ fs [] \\ asm_exists_tac \\

 simp [shift_seq_replace_prefix] \\
 drule_strip regs_run_fbits \\ first_x_assum (qspec_then ‘fbits'’ strip_assume_tac) \\
 fs [rtlstate_fbits_fbits, shift_seq_replace_prefix] \\ simp [det_rel_reg_fbits, only_regs_fbits] \\
 metis_tac [regs_run_only_regs, det_rel_reg_cong3]
QED

Theorem rtl_nd_value_K_F_fbits:
 !t fbits. rtl_nd_value (replace_prefix fbits (K F) (rtltype_v_size t)) t = (build_zero t, fbits)
Proof
 Cases \\ rw [rtl_nd_value_def, build_zero_def, rtltype_v_size_def]
 >- (rw [oracle_bit_def, shift_seq_replace_prefix] \\ EVAL_TAC)
 \\ simp [oracle_bits_genlist, shift_seq_replace_prefix] \\
    match_mp_tac GENLIST_CONG \\ rw [replace_prefix_def]
QED

Theorem rtl_determinizer_reg_correct_init:
 !si regs cenvold cenvold' cenv_det cenv.
 init_run cenvold regs = INR cenvold' ==>
 ?cenv_det'. init_run cenv_det (MAP (rtl_determinizer_reg si) regs) = INR cenv_det' /\
             ?fbits cenv'. init_run (cenv with fbits := fbits) regs = INR cenv' /\
                           (det_rel_reg cenvold cenv_det cenv ==> det_rel_reg cenvold' cenv_det' cenv')
Proof
 gen_tac \\ Induct >- (rw [init_run_def] \\ metis_tac [rtlstate_fbits_fbits]) \\
 PairCases \\ Cases_on ‘h2.init’ \\
 rw [init_run_def, rtl_determinizer_reg_def, has_rtltype_v_correct, build_zero_type_correct]
 >- (pairarg_tac \\ fs [cset_var_fbits] \\ drule_first \\
    qmatch_goalsub_abbrev_tac ‘init_run cenv_det' (MAP (rtl_determinizer_reg si) regs)’ \\
    first_x_assum (qspecl_then [‘cenv_det'’,
                                ‘cset_var cenv (RegVar h0 h1) (build_zero h2.type)’] strip_assume_tac) \\
    qunabbrev_tac ‘cenv_det'’ \\
    simp [] \\ qexists_tac ‘replace_prefix fbits (K F) (rtltype_v_size h2.type)’ \\
    rw [rtl_nd_value_K_F_fbits] \\ first_x_assum match_mp_tac \\ simp [det_rel_reg_fbits] \\
    metis_tac [det_rel_reg_cset_var, rtl_nd_value_type_correct, build_zero_type_correct, rtltype_v_same_shape])

 \\ simp [cset_var_fbits, det_rel_reg_fbits] \\ drule_first \\ metis_tac [det_rel_reg_cset_var, same_shape_refl]
QED

Definition det_rel_reg_out_def:
 det_rel_reg_out (*cenvold*) cenv_det cenv <=>
 (∀reg. sum_alookup cenv_det reg = sum_alookup cenv reg)
End

Theorem rtl_determinizer_out_correct:
 ∀outs fext si cenvold cenvold' cenv_det cenv.
 sum_mapM (out_run fext cenvold) outs = INR cenvold' ∧
 EVERY out_ok outs ∧
 det_rel si cenvold cenv_det cenv ⇒
 ∃cenv_det'. sum_mapM (out_run fext cenv_det) outs = INR cenv_det' ∧
             ?cenv'. sum_mapM (out_run fext cenv) outs = INR cenv' /\
                     det_rel_reg_out (*si cenvold'*) cenv_det' cenv'
Proof
 Induct \\ TRY PairCases \\ simp [sum_mapM_INR, out_ok_cases] >- simp [det_rel_reg_out_def] \\
 rpt strip_tac \\ rveq \\ fs [out_run_def, cell_inp_run_def, sum_bind_INR] \\
 drule_first \\ fs [det_rel_def] \\ drule_first \\ fs [det_rel_reg_out_def, sum_alookup_cons]
QED

Theorem MAP_reg_name_MAP_rtl_determinizer_reg:
 ∀regs si. MAP reg_name (MAP (rtl_determinizer_reg si) regs) = MAP reg_name regs
Proof
 Induct \\ TRY PairCases \\ simp [rtl_determinizer_reg_def, reg_name_def]
QED

Theorem rtl_determinizer_reg_correct_static:
 ∀regs extenv combs_max ffs_max si.
 regs_ok extenv combs_max ffs_max regs ∧
 regs_distinct regs ⇒
 regs_ok extenv combs_max ffs_max (MAP (rtl_determinizer_reg si) regs) ∧
 regs_distinct (MAP (rtl_determinizer_reg si) regs)
Proof
 rw [regs_ok_def, regs_distinct_def, EVERY_MAP, MAP_reg_name_MAP_rtl_determinizer_reg] \\
 irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ PairCases \\ rw [reg_ok_def, rtl_determinizer_reg_def]
 >- (every_case_tac \\ fs [has_rtltype_v_correct, build_zero_type_correct])
 \\ Cases_on ‘x2.inp’ \\ fs [cell_input_lt_rtl_determinizer_inp, cell_input_covered_by_extenv_rtl_determinizer_inp]
QED

(* Output is deterministic *)

Theorem deterministic_regs_map_rtl_determinizer_reg:
 !regs si. deterministic_regs (MAP (rtl_determinizer_reg si) regs)
Proof
 Induct \\ TRY PairCases \\ fs [deterministic_regs_def, rtl_determinizer_reg_def, deterministic_reg_def]
QED

Theorem deterministic_netlist_rtl_determinizer_netlist:
 !nl nl' si si'. rtl_determinizer_netlist si nl = (si', nl') ==> deterministic_netlist nl'
Proof
 Induct \\ fs [rtl_determinizer_netlist_def, deterministic_netlist_def] \\
 Cases \\ rpt strip_tac \\ rpt (pairarg_tac \\ fs []) \\ rveq \\
 drule_first \\
 fs [rtl_determinizer_cell_def] \\ rw [deterministic_cell_def] \\
 every_case_tac \\ rw [] \\ rw [deterministic_cell_def]
QED

(* Top-level thm *)

Theorem covers_ndetcell_si_cong:
 ∀cell si si'.
 (∀n. MEM n (cell_output cell) ⇒ lookup num_cmp n si' = lookup num_cmp n si) ⇒
 covers_ndetcell T si' cell = covers_ndetcell T si cell
Proof
 Cases \\ simp [cell_output_def, covers_ndetcell_def]
QED

Theorem netlist_sorted_mem_lem:
 netlist_sorted (combs_nl ⧺ ffs_nl) ∧
 MEM cell ffs_nl ∧
 MEM n (cell_output cell) ⇒
 ¬MEM n (FLAT (MAP cell_output combs_nl))
Proof
 rpt strip_tac \\ drule_strip netlist_sorted_all_distinct \\ fs [ALL_DISTINCT_APPEND] \\
 drule_first \\ fs [MEM_FLAT, MEM_MAP] \\ metis_tac []
QED

Triviality ALOOKUP_rtl_determinizer_reg_reg_type:
 ∀regs rdata regi si.
 ALOOKUP (MAP (rtl_determinizer_reg si) regs) regi = SOME rdata ⇒
 ∃rdata'. ALOOKUP regs regi = SOME rdata' ∧ rdata'.reg_type = rdata.reg_type
Proof
 Induct \\ TRY PairCases \\ simp [rtl_determinizer_reg_def] \\ rw [SF SFY_ss] \\ rw []
QED

Theorem rtl_determinizer_correct:
 !cir cir' fext fbits fbits' n cenvold min combs_max ffs_max.
 rtl_determinizer cir = INR cir' ∧
 circuit_ok min combs_max ffs_max cir ∧
 circuit_sorted cir ∧
 (* needed to ensure that the circuit makes sense w.r.t. types: *)
 circuit_run fext fbits cir n = INR (cenvold, fbits') ==>
 circuit_extenv cir' = circuit_extenv cir ∧
 (∀regi rdata. ALOOKUP (circuit_regs cir') regi = SOME rdata ⇒
               ∃rdata'. ALOOKUP (circuit_regs cir) regi = SOME rdata' ∧ rdata'.reg_type = rdata.reg_type) ∧
 deterministic_circuit cir' ∧
 circuit_ok min combs_max ffs_max cir' ∧
 circuit_sorted cir' ∧
 ?cenv_det fbits_det. circuit_run fext fbits cir' n = INR (cenv_det, fbits_det) /\ (* <-- could say fbits here instead of fbits_det, but this anyway follows from general determinism thm for circuit_run *)
                      ?fbits' fbits'' cenv. circuit_run fext fbits' cir n = INR (cenv, fbits'') /\
                                            det_rel_reg_out (*cenvold*) cenv_det cenv
Proof
 namedCases ["extenv outs regs combs_nl ffs_nl"] \\ simp [rtl_determinizer_def, sum_bind_INR] \\ rpt strip_tac' \\
 rpt (pairarg_tac \\ gvs [sum_bind_INR]) \\

 conj_tac >- simp [circuit_extenv_def] \\
 conj_tac >- simp [circuit_regs_def, ALOOKUP_rtl_determinizer_reg_reg_type, SF SFY_ss] \\
 conj_tac >- (fs [deterministic_circuit_def, deterministic_regs_map_rtl_determinizer_reg] \\ 
              conj_tac \\ irule deterministic_netlist_rtl_determinizer_netlist \\ asm_exists_tac) \\

 fs [circuit_run_def, sum_bind_INR, circuit_sorted_def, circuit_ok_def] \\
 drule_strip rtl_determinizer_reg_correct_static \\ simp [] \\ pop_assum kall_tac \\

 drule_strip rtl_determinizer_reg_correct_init \\
 first_x_assum (qspecl_then [‘si''’, ‘<|env := []; fbits := fbits|>’, ‘<|env := []|>’] strip_assume_tac) \\
 pop_assum mp_tac \\ impl_tac >- simp [det_rel_reg_def, cget_var_def] \\ strip_tac \\ simp [] \\

 drule_strip netlist_sorted_all_distinct \\
 drule_strip find_fills_correct \\ impl_tac >- fs [netlist_unprocessed_empty, empty_thm] \\ simp [] \\ strip_tac \\

 ‘EVERY (covers_ndetcell T si') ffs_nl’ by
 (rev_drule_strip rtl_determinizer_netlist_correct_cells_run \\
  impl_tac >- fs [netlist_sorted_def, sortingTheory.SORTED_APPEND] \\ strip_tac \\
  irule EVERY_MEM_MONO \\ metis_tac [covers_ndetcell_si_cong, netlist_sorted_mem_lem]) \\

 qspecl_then [‘combs_nl’, ‘ffs_nl’] assume_tac rtl_determinizer_netlist_correct_run \\

 drule_first \\
 impl_tac >- (imp_res_tac init_run_only_regs \\ fs [only_regs_nil]) \\ strip_tac \\
 simp [circuit_run_def, sum_bind_def] \\

 drule_strip rtl_determinizer_out_correct \\ simp [] \\

 drule_strip init_run_fbits \\
 qexists_tac ‘replace_prefix fbits'' fbits' n'’ \\
 first_x_assum (qspec_then ‘replace_prefix fbits'' fbits' n'’ mp_tac) \\
 impl_tac >- simp [init_seq_eq_replace_prefix, init_seq_eq_sym] \\ strip_tac \\ fs [shift_seq_replace_prefix]
QED

val _ = export_theory ();
