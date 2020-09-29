open hardwarePreamble;

open sumExtraTheory RTLTheory RTLPropsTheory;

open RTLLib;

val _ = new_theory "RTLUnusedRegs";

Definition cell_input_reg_used_def:
 (cell_input_reg_used reg (ConstInp _) <=> F) /\
 (cell_input_reg_used reg (ExtInp _ _) <=> F) /\
 (cell_input_reg_used reg (VarInp var _) <=> var = reg)
End
    
Definition cell_reg_used_def:
 (cell_reg_used reg (NDetCell _ _) <=> F) /\
 (cell_reg_used reg (Cell1 _ _ in1) <=> cell_input_reg_used reg in1) /\
 (cell_reg_used reg (Cell2 _ _ in1 in2) <=> cell_input_reg_used reg in1 ∨
                                            cell_input_reg_used reg in2) /\
 (cell_reg_used reg (CellMux _ in1 in2 in3) <=> cell_input_reg_used reg in1 ∨
                                                cell_input_reg_used reg in2 ∨
                                                cell_input_reg_used reg in3) /\
 (cell_reg_used reg (CellArrayWrite _ in1 _ in2) <=> cell_input_reg_used reg in1 ∨
                                                     cell_input_reg_used reg in2) /\
 (cell_reg_used reg (CellLUT _ ins _) <=> EXISTS (cell_input_reg_used reg) ins) /\
 (cell_reg_used reg (Carry4 _ _ cin lhs rhs) <=> cell_input_reg_used reg cin ∨
                                                 EXISTS (cell_input_reg_used reg) lhs ∨
                                                 EXISTS (cell_input_reg_used reg) rhs)
End

Definition reg_reg_used_def:
 reg_reg_used reg (ty,dest,i,v,inp) ⇔
 case inp of
   NONE => F
 | SOME inp => cell_input_reg_used reg inp
End

(* Limitation: To keeps too many regs, e.g. regs referenced by unused regs (also consider cycles) *)
Definition reg_used_def:
 reg_used keep regs nl (t, var, idx, v, inp) ⇔ MEM var keep ∨
                                               EXISTS (cell_reg_used (RegVar var idx)) nl ∨
                                               EXISTS (reg_reg_used (RegVar var idx)) regs
End

Definition rtl_rem_unused_regs_def:
 rtl_rem_unused_regs keep (Circuit extenv regs nl) = Circuit extenv (FILTER (reg_used keep regs nl) regs) nl
End

Definition rem_rel_def:
 rem_rel keep (regs : regty list) nl s s' ⇔
 s'.fbits = s.fbits ∧
 (∀var idx. MEM var keep ∨ EXISTS (cell_reg_used (RegVar var idx)) nl ∨ EXISTS (reg_reg_used (RegVar var idx)) regs ⇒
            cget_var s' (RegVar var idx) = cget_var s (RegVar var idx)) ∧
 (∀n. cget_var s' (NetVar n) = cget_var s (NetVar n))
End

Theorem rem_rel_nl_tl:
 ∀keep regs c cs s s'. rem_rel keep regs (c::cs) s s' ⇒ rem_rel keep regs cs s s'
Proof
 simp [rem_rel_def] \\ metis_tac []
QED

Theorem rem_rel_regs_tl:
 ∀keep r rs nl s s'. rem_rel keep (r::rs) nl s s' ⇒ rem_rel keep rs nl s s'
Proof
 simp [rem_rel_def] \\ metis_tac []
QED

Triviality cell_inp_run_cong:
 ∀inp s2 s1 fext v.
 cell_inp_run fext s1 inp = INR v ∧
 (∀var idx. cell_input_reg_used (RegVar var idx) inp ⇒ cget_var s2 (RegVar var idx) = cget_var s1 (RegVar var idx)) ∧
 (∀n. cget_var s2 (NetVar n) = cget_var s1 (NetVar n)) ⇒
 cell_inp_run fext s2 inp = INR v
Proof
 Cases \\ simp [cell_inp_run_def] \\ Cases_on ‘v’ \\ rw [cell_inp_run_def, sum_bind_INR, cell_input_reg_used_def]
QED

Triviality sum_mapM_cell_inp_run_cong:
 ∀ins s2 s1 fext vs.
 sum_mapM (cell_inp_run fext s1) ins = INR vs ∧
 (∀var idx. EXISTS (cell_input_reg_used (RegVar var idx)) ins ⇒
            cget_var s2 (RegVar var idx) = cget_var s1 (RegVar var idx)) ∧
 (∀n. cget_var s2 (NetVar n) = cget_var s1 (NetVar n)) ⇒
 sum_mapM (cell_inp_run fext s2) ins = INR vs
Proof
 Induct \\ rw [sum_mapM_INR, cell_input_reg_used_def] \\
 drule_strip cell_inp_run_cong \\ disch_then (qspec_then ‘s2’ mp_tac) \\ impl_tac >- metis_tac [] \\ strip_tac \\
 drule_first \\ disch_then (qspec_then ‘s2’ mp_tac) \\ impl_tac >- metis_tac [] \\ simp []
QED

fun cell_inp_run_cong_tac inp =
 qspecl_then [inp, ‘s2’] assume_tac cell_inp_run_cong \\ drule_first \\ impl_tac >- metis_tac [] \\ strip_tac;

fun sum_mapM_cell_inp_run_cong_tac inps =
 qspecl_then [inps, ‘s2’] assume_tac sum_mapM_cell_inp_run_cong \\ drule_first \\ impl_tac >- metis_tac [] \\ strip_tac;

Theorem cell_run_rem_rel:
 ∀cell s1 s1' s2 fext keep regs nl.
 cell_run fext s1 cell = INR s1' ∧ rem_rel keep regs (cell::nl) s1 s2 ⇒
 ∃s2'. cell_run fext s2 cell = INR s2' ∧ rem_rel keep regs (cell::nl) s1' s2'
Proof
 Cases \\ simp [cell_run_def, rem_rel_def] \\ rpt strip_tac'
 >- (rename1 ‘NDetCell _ t’ \\ Cases_on ‘t’ \\ fs [ndetcell_run_def] \\
     rpt (pairarg_tac \\ fs []) \\ rveq \\
     fs [cget_var_fbits, cset_var_fbits, cget_var_cset_var, cell_reg_used_def] \\ metis_tac [])

 >- (rename1 ‘Cell1 op _ in1’ \\ Cases_on ‘op’ \\ fs [cell_run_def, sum_bind_INR, cell_reg_used_def] \\
     cell_inp_run_cong_tac ‘in1’ \\
     rw [cset_var_fbits, cget_var_cset_var] \\ metis_tac [])

 >- (rename1 ‘Cell2 op _ in1 in2’ \\ fs [sum_bind_INR, cell_reg_used_def] \\
     cell_inp_run_cong_tac ‘in1’ \\ cell_inp_run_cong_tac ‘in2’ \\
     rw [cset_var_fbits, cget_var_cset_var] \\ metis_tac [])

 >- (rename1 ‘CellMux _ in1 in2 in3’ \\ fs [sum_bind_INR, cell_reg_used_def] \\
     cell_inp_run_cong_tac ‘in1’ \\ cell_inp_run_cong_tac ‘in2’ \\ cell_inp_run_cong_tac ‘in3’ \\
     rw [cset_var_fbits, cget_var_cset_var] \\ metis_tac [])

 >- (rename1 ‘CellArrayWrite _ in1 _ in2’ \\ fs [sum_bind_INR, cell_reg_used_def] \\
     cell_inp_run_cong_tac ‘in1’ \\ cell_inp_run_cong_tac ‘in2’ \\
     rw [cset_var_fbits, cget_var_cset_var] \\ metis_tac [])

 >- (rename1 ‘CellLUT _ ins _’ \\ fs [cellLUT_run_def, sum_bind_INR, cell_reg_used_def] \\
     sum_mapM_cell_inp_run_cong_tac ‘ins’ \\
     rw [cset_var_fbits, cget_var_cset_var] \\ metis_tac [])

 >- (rename1 ‘Carry4 _ _ cin lhs rhs’ \\ fs [sum_bind_INR, cell_reg_used_def] \\ pairarg_tac \\
     cell_inp_run_cong_tac ‘cin’ \\ sum_mapM_cell_inp_run_cong_tac ‘lhs’ \\ sum_mapM_cell_inp_run_cong_tac ‘rhs’ \\
     fs [] \\ rw [cset_var_fbits, cget_var_cset_var] \\ metis_tac [])
QED

Theorem cells_run_rem_rel:
 ∀nl regs fext s1 s1' s2 keep.
 sum_foldM (cell_run fext) s1 nl = INR s1' ∧ rem_rel keep regs nl s1 s2 ⇒
 ∃s2'. sum_foldM (cell_run fext) s2 nl = INR s2' ∧ rem_rel keep regs nl s1' s2'
Proof
 Induct \\ simp [sum_foldM_def, sum_bind_INR] \\ rpt strip_tac' \\
 drule_strip cell_run_rem_rel \\
 drule_strip rem_rel_nl_tl \\ drule_first \\ imp_res_tac cells_run_cget_var_RegVar \\
 fs [rem_rel_def] \\ metis_tac []
QED

Triviality reg_run_cong:
 ∀(P : regty -> bool).
 reg_run fext s1_net s1 (h0,h1,h2,h3,h4) = INR s1' ∧
 (∀h0 h1 h2 h3 var idx. h4 = SOME (VarInp var idx) ⇒ cget_var s2_net var = cget_var s1_net var) ∧
 (∀h0 h1 h2 h3 h4. P (h0,h1,h2,h3,h4) ⇒ cget_var s2 (RegVar h1 h2) = cget_var s1 (RegVar h1 h2)) ∧
 P (h0,h1,h2,h3,h4) ⇒
 ∃s2'. reg_run fext s2_net s2 (h0,h1,h2,h3,h4) = INR s2' ∧
       (∀h0 h1 h2 h3 h4. P (h0,h1,h2,h3,h4) ⇒ cget_var s2' (RegVar h1 h2) = cget_var s1' (RegVar h1 h2))
Proof
 gen_tac \\ simp [reg_run_def] \\ TOP_CASE_TAC \\ simp [sum_bind_INR] \\ strip_tac \\ rveq >- metis_tac [] \\
 ‘cell_inp_run fext s2_net x = INR v’ by
 (Cases_on ‘x’ \\ fs [cell_inp_run_def, sum_bind_INR] \\ rpt drule_first \\ simp []) \\
 simp [cget_var_cset_var] \\ metis_tac []
QED

Theorem rem_rel_reg_inp_MEM_lem:
 rem_rel keep regs nl s1_net s2_net ⇒
 (∀h0 h1 h2 h3 inp var idx.
  MEM (h0,h1,h2,h3,SOME (VarInp var idx)) regs ⇒
  cget_var s2_net var = cget_var s1_net var)
Proof
 rw [rem_rel_def] \\ Cases_on ‘var’ \\ full_simp_tac (srw_ss()++boolSimps.DNF_ss) [EXISTS_MEM] \\
 drule_first \\ simp [reg_reg_used_def, cell_input_reg_used_def]
QED

Theorem regs_run_rem_rel_lem:
 ∀regs fext s1 s1_net s1' s2 s2_net P.
 sum_foldM (reg_run fext s1_net) s1 regs = INR s1' ∧
 (∀h0 h1 h2 h3 inp var idx.
  MEM (h0,h1,h2,h3,SOME (VarInp var idx)) regs ⇒
  cget_var s2_net var = cget_var s1_net var) ∧
 (∀h0 h1 h2 h3 h4.
  P (h0,h1,h2,h3,h4) ⇒
  cget_var s2 (RegVar h1 h2) = cget_var s1 (RegVar h1 h2)) ∧
 (∀h0 h1 h2 h3 h4 h0' h3' h4'. P (h0,h1,h2,h3,h4) = P (h0',h1,h2,h3',h4')) ⇒
 ∃s2'. sum_foldM (reg_run fext s2_net) s2 (FILTER P regs) = INR s2' ∧
       (∀h0 h1 h2 h3 h4. P (h0,h1,h2,h3,h4) ⇒ cget_var s2' (RegVar h1 h2) = cget_var s1' (RegVar h1 h2))
Proof
 Induct \\ TRY PairCases \\ simp [sum_foldM_INR] \\ rpt strip_tac' \\ IF_CASES_TAC
 >- (simp [sum_foldM_INR] \\ drule_strip reg_run_cong \\
     disch_then (qspecl_then [‘s2_net’, ‘s2’, ‘P’] mp_tac) \\
     impl_tac >- (fs [] \\ metis_tac []) \\ strip_tac \\ simp [] \\ first_x_assum match_mp_tac \\
     asm_exists_tac \\ metis_tac [])
 \\ first_x_assum match_mp_tac \\ asm_exists_tac \\ rpt conj_tac \\ TRY (metis_tac []) \\
    drule_strip reg_run_cget_var \\ rw [] \\ fs [reg_name_def, reg_idx_def] \\ metis_tac []
QED

Theorem regs_run_rem_rel:
 ∀regs fext s1 s1_net s1' s2 s2_net keep nl.
 sum_foldM (reg_run fext s1_net) s1 regs = INR s1' ∧
 rem_rel keep regs nl s1_net s2_net ∧
 rem_rel keep regs nl s1 s2 ⇒
 ∃s2'. sum_foldM (reg_run fext s2_net) s2 (FILTER (reg_used keep regs nl) regs) = INR s2' ∧
       rem_rel keep regs nl s1' s2'
Proof
 rpt strip_tac \\ drule_strip regs_run_rem_rel_lem \\
 disch_then (qspecl_then [‘s2’, ‘s2_net’, ‘reg_used keep regs nl’] mp_tac) \\
 impl_tac >- (rpt conj_tac >- metis_tac [rem_rel_reg_inp_MEM_lem] \\
              fs [rem_rel_def, reg_used_def] \\ metis_tac []) \\ strip_tac \\
 imp_res_tac regs_run_fbits \\ imp_res_tac regs_run_cget_var_NetVar \\
 fs [rem_rel_def, reg_used_def] \\ metis_tac []
QED

Theorem netlist_run_rem_rel:
 ∀n nl fext s1 s1' s2 keep regs.
 netlist_run fext s1 nl regs n = INR s1' ∧ rem_rel keep regs nl s1 s2 ⇒
 ∃s2'. netlist_run fext s2 nl (FILTER (reg_used keep regs nl) regs) n = INR s2' ∧ rem_rel keep regs nl s1' s2'
Proof
 Induct \\ simp [netlist_run_def, sum_bind_INR] \\ rpt strip_tac' \\ drule_first \\
 fs [netlist_step_def, sum_bind_INR] \\
 drule_strip cells_run_rem_rel \\
 drule_strip regs_run_rem_rel \\
 fs [rem_rel_def, cget_var_fbits] \\ metis_tac []
QED

Theorem init_run_rem_rel_lem:
 ∀regs s1 s1' s2 (P : regty -> bool).
 init_run s1 regs = INR s1' ∧ deterministic_regs regs ∧
 (∀h0 h1 h2 h3 h4. P (h0, h1, h2, h3, h4) ⇒ cget_var s2 (RegVar h1 h2) = cget_var s1 (RegVar h1 h2)) ∧
 (∀h0 h1 h2 h3 h4 h0' h3' h4'. P (h0,h1,h2,h3,h4) = P (h0',h1,h2,h3',h4')) ⇒
 ∃s2'. init_run s2 (FILTER P regs) = INR s2' ∧
       (∀h0 h1 h2 h3 h4. P (h0, h1, h2, h3, h4) ⇒ cget_var s2' (RegVar h1 h2) = cget_var s1' (RegVar h1 h2))
Proof
 Induct \\ TRY PairCases \\ simp [init_run_def] >- metis_tac [] \\ rpt gen_tac \\
 TOP_CASE_TAC \\ fs [deterministic_regs_def, deterministic_reg_def] \\
 IF_CASES_TAC \\ simp [] \\ rw [init_run_def] \\
 first_x_assum match_mp_tac \\ asm_exists_tac \\ simp [cget_var_cset_var] \\ metis_tac []
QED

Theorem init_run_rem_rel:
 ∀regs s1 s1' s2 keep nl.
 init_run s1 regs = INR s1' ∧ deterministic_regs regs ∧ rem_rel keep regs nl s1 s2 ⇒
 ∃s2'. init_run s2 (FILTER (reg_used keep regs nl) regs) = INR s2' ∧ rem_rel keep regs nl s1' s2'
Proof
 rpt strip_tac \\ drule_strip init_run_rem_rel_lem \\
 disch_then (qspecl_then [‘s2’, ‘reg_used keep regs nl’] mp_tac) \\
 impl_tac >- (fs [rem_rel_def, reg_used_def] \\ metis_tac []) \\ strip_tac \\
 imp_res_tac init_run_deterministic \\ rfs [deterministic_regs_filter] \\
 imp_res_tac init_run_cget_var_NetVar \\
 fs [rem_rel_def, reg_used_def] \\ fs []
QED

Theorem rtl_rem_unused_regs_correct:
 !cir env keep fext fbits n.
 deterministic_circuit cir /\
 circuit_run fext fbits cir n = INR env ==>
 deterministic_circuit (rtl_rem_unused_regs keep cir) /\
 ?env'. circuit_run fext fbits (rtl_rem_unused_regs keep cir) n = INR env' /\
        (!var idx. MEM var keep ==> cget_var env' (RegVar var idx) = cget_var env (RegVar var idx))
Proof
 Cases \\ rename1 ‘Circuit fextenv regs nl’ \\
 rw [circuit_run_def, sum_bind_INR, rtl_rem_unused_regs_def, deterministic_circuit_def]
 >- fs [deterministic_regs_def, EVERY_FILTER_IMP] \\

 drule_strip init_run_rem_rel \\ disch_then (qspecl_then [‘<|env := []; fbits := fbits|>’, ‘keep’, ‘nl’] mp_tac) \\
 impl_tac >- simp [rem_rel_def] \\ strip_tac \\ simp [] \\

 drule_strip netlist_run_rem_rel \\ fs [rem_rel_def]
QED

Theorem circuit_extenv_rtl_rem_unused_regs:
 ∀cir keep. circuit_extenv (rtl_rem_unused_regs keep cir) = circuit_extenv cir
Proof
 Cases \\ simp [rtl_rem_unused_regs_def, circuit_extenv_def]
QED

Triviality all_distinct_map_filter:
 !l f P. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
 Induct \\ rw [MEM_MAP, MEM_FILTER] \\ metis_tac []
QED

Theorem rtl_rem_unused_regs_preserves:
 !cir keep.
 (!min max. circuit_ok min max cir ==> circuit_ok min max (rtl_rem_unused_regs keep cir)) /\
 (circuit_sorted cir ==> circuit_sorted (rtl_rem_unused_regs keep cir))
Proof
 Cases \\ rw [rtl_rem_unused_regs_def, circuit_ok_def, regs_ok_def, EVERY_FILTER_IMP,
              circuit_sorted_def, regs_distinct_def, all_distinct_map_filter]
QED

val _ = export_theory ();
