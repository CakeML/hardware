open hardwarePreamble;

open sumExtraTheory RTLTheory RTLPropsTheory;

open RTLLib;

val _ = new_theory "RTLUnusedRegs";

(** Implementation **)

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
 reg_reg_used reg ((reg', i), rdata) ⇔
 case rdata.inp of
   NONE => F
 | SOME inp => cell_input_reg_used reg inp
End

Definition out_reg_used_def:
 (out_reg_used reg (_, OutInp inp) = cell_input_reg_used reg inp) ∧
 (out_reg_used reg (_, OutInps inps) = EXISTS (cell_input_reg_used reg) inps)
End

(* Limitation: Keeps too many regs, e.g. regs referenced by unused regs (would have to iterate to find those?) *)
Definition reg_used_def:
 reg_used outs regs combs_nl ffs_nl ((reg, i), rdata) ⇔
 EXISTS (out_reg_used (RegVar reg i)) outs
 ∨
 (EXISTS (cell_reg_used (RegVar reg i)) combs_nl ∨
  EXISTS (cell_reg_used (RegVar reg i)) ffs_nl ∨
  EXISTS (reg_reg_used (RegVar reg i)) regs)
End

Definition rtl_rem_unused_regs_def:
 rtl_rem_unused_regs (Circuit extenv outs regs combs_nl ffs_nl) =
 Circuit extenv outs (FILTER (reg_used outs regs combs_nl ffs_nl) regs) combs_nl ffs_nl
End

(** Correctness proof **)

Definition rem_rel_def:
 rem_rel (outs : (string # out_spec) list) regs nl s s' ⇔
 s'.fbits = s.fbits ∧
 (∀var idx.  EXISTS (out_reg_used (RegVar var idx)) outs ∨
            EXISTS (cell_reg_used (RegVar var idx)) nl ∨
            EXISTS (reg_reg_used (RegVar var idx)) regs ⇒
            cget_var s' (RegVar var idx) = cget_var s (RegVar var idx)) ∧
 (∀n. cget_var s' (NetVar n) = cget_var s (NetVar n))
End

Theorem rem_rel_outs_tl:
 ∀k ks regs nl s s'. rem_rel (k::ks) regs nl s s' ⇒ rem_rel ks regs nl s s'
Proof
 simp [rem_rel_def] \\ metis_tac []
QED

Theorem rem_rel_nl_tl:
 ∀outs regs c cs s s'. rem_rel outs regs (c::cs) s s' ⇒ rem_rel outs regs cs s s'
Proof
 simp [rem_rel_def] \\ metis_tac []
QED

Theorem rem_rel_regs_tl:
 ∀outs r rs nl s s'. rem_rel outs (r::rs) nl s s' ⇒ rem_rel outs rs nl s s'
Proof
 simp [rem_rel_def] \\ metis_tac []
QED

(*Theorem rem_rel_nl_append:
 rem_rel keep regs (combs_nl ⧺ ffs_nl) s1 s2 ⇔ rem_rel keep regs combs_nl s1 s2 ∧ rem_rel keep regs ffs_nl s1 s2
Proof
 rw [rem_rel_def] \\ metis_tac []
QED*)

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
 qspecl_then [inps, ‘s2’] assume_tac sum_mapM_cell_inp_run_cong \\ drule_first \\ impl_tac >- metis_tac [EXISTS_MEM] \\ strip_tac;

Theorem cell_mem_nl_lem:
 ∀cell nl inp var idx.
 MEM cell nl ∧ MEM inp (cell_inputs cell) ∧ cell_input_reg_used (RegVar var idx) inp ⇒
 EXISTS (cell_reg_used (RegVar var idx)) nl
Proof
 rw [EXISTS_MEM] \\ asm_exists_tac \\ Cases_on ‘cell’ \\
 gs [cell_reg_used_def, cell_inputs_def, cell_input_reg_used_def] \\
 metis_tac [EXISTS_MEM]
QED

Theorem cell_run_rem_rel:
 ∀cell s1 s1' s2 fext outs (regs : ((string # num), reg_metadata) alist) nl.
 cell_run fext s1 cell = INR s1' ∧
 rem_rel outs regs nl s1 s2 ∧
 MEM cell nl ⇒
 ∃s2'. cell_run fext s2 cell = INR s2' ∧
       rem_rel outs regs nl s1' s2'
Proof
 Cases \\ simp [cell_run_def, rem_rel_def] \\ rpt strip_tac' \\
 drule_strip cell_mem_nl_lem \\ simp [cell_inputs_def] \\ TRY strip_tac

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
 ∀nlall nl (regs : ((string # num), reg_metadata) alist) fext s1 s1' s2 outs.
 sum_foldM (cell_run fext) s1 nl = INR s1' ∧
 rem_rel outs regs nlall s1 s2 ∧
 (∀c. MEM c nl ⇒ MEM c nlall) ⇒
 ∃s2'. sum_foldM (cell_run fext) s2 nl = INR s2' ∧
       rem_rel outs regs nlall s1' s2'
Proof
 gen_tac \\ Induct \\ simp [sum_foldM_def, sum_bind_INR] \\ rpt strip_tac' \\
 drule_strip cell_run_rem_rel \\ impl_tac >- simp [] \\ strip_tac \\
 drule_first \\ simp []
QED

Triviality reg_run_cong:
 ∀P.
 reg_run fext s1_net s1 ((reg, i), rdata) = INR s1' ∧
 (∀var idx. rdata.inp = SOME (VarInp var idx) ⇒ cget_var s2_net var = cget_var s1_net var) ∧
 (∀reg i rdata. P ((reg, i), rdata) ⇒ cget_var s2 (RegVar reg i) = cget_var s1 (RegVar reg i)) ∧
 P ((reg, i), rdata) ⇒
 ∃s2'. reg_run fext s2_net s2 ((reg, i), rdata) = INR s2' ∧
       (∀reg i rdata. P ((reg, i), rdata) ⇒ cget_var s2' (RegVar reg i) = cget_var s1' (RegVar reg i))
Proof
 gen_tac \\ simp [reg_run_def] \\ TOP_CASE_TAC \\ simp [sum_bind_INR] \\ strip_tac \\ rveq >- metis_tac [] \\
 ‘cell_inp_run fext s2_net x = INR v’ by
 (Cases_on ‘x’ \\ fs [cell_inp_run_def, sum_bind_INR] \\ rpt drule_first \\ simp []) \\
 simp [cget_var_cset_var] \\ metis_tac []
QED

Theorem rem_rel_reg_inp_MEM_lem:
 rem_rel outs regs nl s1_net s2_net ⇒
 (∀reg i inp var idx.
  MEM ((reg, i), rdata) regs ∧ rdata.inp = SOME (VarInp var idx) ⇒
  cget_var s2_net var = cget_var s1_net var)
Proof
 rw [rem_rel_def] \\ Cases_on ‘var’ \\ full_simp_tac (srw_ss()++boolSimps.DNF_ss) [EXISTS_MEM] \\
 drule_first \\ simp [reg_reg_used_def, cell_input_reg_used_def]
QED

Theorem regs_run_rem_rel_lem:
 ∀regs fext s1 s1_net s1' s2 s2_net P.
 sum_foldM (reg_run fext s1_net) s1 regs = INR s1' ∧
 (∀reg i rdata var idx.
  MEM ((reg, i), rdata) regs ∧ rdata.inp = SOME (VarInp var idx) ⇒
  cget_var s2_net var = cget_var s1_net var) ∧
 (∀reg i rdata.
  P ((reg, i), rdata) ⇒
  cget_var s2 (RegVar reg i) = cget_var s1 (RegVar reg i)) ∧
 (∀reg i rdata rdata'. P ((reg, i), rdata) = P ((reg, i), rdata')) ⇒
 ∃s2'. sum_foldM (reg_run fext s2_net) s2 (FILTER P regs) = INR s2' ∧
       (∀reg i rdata. P ((reg, i), rdata) ⇒ cget_var s2' (RegVar reg i) = cget_var s1' (RegVar reg i))
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
 ∀regs fext s1 s1_net s1' s2 s2_net outs.
 sum_foldM (reg_run fext s1_net) s1 (FILTER P regs) = INR s1' ∧
 rem_rel outs regs (combs_nl++ffs_nl) s1_net s2_net ∧
 rem_rel outs regs (combs_nl++ffs_nl) s1 s2 ⇒
 ∃s2'. sum_foldM (reg_run fext s2_net) s2 (FILTER (reg_used outs regs combs_nl ffs_nl) (FILTER P regs)) = INR s2' ∧
       rem_rel outs regs (combs_nl++ffs_nl) s1' s2'
Proof
 rpt strip_tac \\ drule_strip regs_run_rem_rel_lem \\
 disch_then (qspecl_then [‘s2’, ‘s2_net’, ‘reg_used outs regs combs_nl ffs_nl’] mp_tac) \\
 impl_tac >- (rpt conj_tac >- (fs [MEM_FILTER] \\ metis_tac [rem_rel_reg_inp_MEM_lem]) \\
              fs [rem_rel_def, reg_used_def] \\ metis_tac []) \\ strip_tac \\
 imp_res_tac regs_run_fbits_const \\ imp_res_tac regs_run_cget_var_NetVar \\
 fs [rem_rel_def, reg_used_def] \\ metis_tac []
QED

Theorem netlist_step_rem_rel:
 ∀combs_nl ffs_nl fext s1 s1' s2 outs regs.
 netlist_step fext s1 combs_nl ffs_nl regs = INR s1' ∧ rem_rel outs regs (combs_nl++ffs_nl) s1 s2 ⇒
 ∃s2'. netlist_step fext s2 combs_nl ffs_nl (FILTER (reg_used outs regs combs_nl ffs_nl) regs) = INR s2' ∧
       rem_rel outs regs (combs_nl++ffs_nl) s1' s2'
Proof
 rw [netlist_step_def, sum_bind_INR] \\
 rev_drule_strip cells_run_rem_rel \\ impl_tac >- simp [] \\ strip_tac \\
 drule_strip regs_run_rem_rel \\ simp [Once rich_listTheory.FILTER_COMM, cells_run_rem_rel, SF SFY_ss]
QED

Theorem netlist_run_rem_rel:
 ∀n combs_nl ffs_nl fext s1 s1' s2 outs regs.
 netlist_run fext s1 combs_nl ffs_nl regs n = INR s1' ∧ rem_rel outs regs (combs_nl++ffs_nl) s1 s2 ⇒
 ∃s2'. netlist_run fext s2 combs_nl ffs_nl (FILTER (reg_used outs regs combs_nl ffs_nl) regs) n = INR s2' ∧
       rem_rel outs regs (combs_nl++ffs_nl) s1' s2'
Proof
 Induct \\ simp [netlist_run_def, sum_bind_INR] \\ rpt strip_tac'
 >- (drule_strip netlist_step_rem_rel \\ simp []) \\
 drule_first \\ simp [] \\
 qmatch_goalsub_abbrev_tac ‘sum_foldM (reg_run _ _) sreg _’ \\
 drule_strip regs_run_rem_rel \\
 disch_then (qspec_then ‘sreg’ mp_tac) \\
 unabbrev_all_tac \\
 impl_tac >- (fs [rem_rel_def, cget_var_def, ALOOKUP_FILTER_FST, is_RegVar_def] \\ metis_tac []) \\ strip_tac \\
 simp [Once rich_listTheory.FILTER_COMM] \\
 drule_strip netlist_step_rem_rel \\ simp []
QED

Theorem init_run_rem_rel_lem:
 ∀regs s1 s1' s2 P.
 init_run s1 regs = INR s1' ∧ deterministic_regs regs ∧
 (∀reg i rdata. P ((reg, i), rdata) ⇒ cget_var s2 (RegVar reg i) = cget_var s1 (RegVar reg i)) ∧
 (∀reg i rdata rdata'. P ((reg, i), rdata) = P ((reg, i), rdata')) ⇒
 ∃s2'. init_run s2 (FILTER P regs) = INR s2' ∧
       (∀reg i rdata. P ((reg, i), rdata) ⇒ cget_var s2' (RegVar reg i) = cget_var s1' (RegVar reg i))
Proof
 Induct \\ TRY PairCases \\ simp [init_run_def] >- metis_tac [] \\ rpt gen_tac \\
 TOP_CASE_TAC \\ fs [deterministic_regs_def, deterministic_reg_def] \\
 IF_CASES_TAC \\ simp [] \\ rw [init_run_def] \\
 first_x_assum match_mp_tac \\ asm_exists_tac \\ simp [cget_var_cset_var] \\ metis_tac []
QED

Theorem init_run_rem_rel:
 ∀regs s1 s1' s2 outs combs_nl ffs_nl.
 init_run s1 regs = INR s1' ∧ deterministic_regs regs ∧ rem_rel outs regs (combs_nl++ffs_nl) s1 s2 ⇒
 ∃s2'. init_run s2 (FILTER (reg_used outs regs combs_nl ffs_nl) regs) = INR s2' ∧
       rem_rel outs regs (combs_nl++ffs_nl) s1' s2'
Proof
 rpt strip_tac \\ drule_strip init_run_rem_rel_lem \\
 disch_then (qspecl_then [‘s2’, ‘reg_used outs regs combs_nl ffs_nl’] mp_tac) \\
 impl_tac >- (fs [rem_rel_def, reg_used_def] \\ metis_tac []) \\ strip_tac \\
 imp_res_tac init_run_deterministic \\ rfs [deterministic_regs_filter] \\
 imp_res_tac init_run_cget_var_NetVar \\
 fs [rem_rel_def, reg_used_def, EXISTS_APPEND] \\ metis_tac []
QED

Theorem outs_run_rem_rel:
 ∀outs fext s1 s1' s2 (regs : ((string # num), reg_metadata) alist) nl.
 sum_mapM (out_run fext s1) outs = INR s1' ∧
 rem_rel outs regs nl s1 s2 ⇒
 ∃s2'. sum_mapM (out_run fext s2) outs = INR s2' ∧
       ∀var. sum_alookup s1' var = sum_alookup s2' var
Proof
 Induct \\ TRY PairCases \\ simp [sum_mapM_INR] \\ rpt strip_tac \\
 drule_strip rem_rel_outs_tl \\ drule_first \\
 Cases_on ‘h1’ \\ gvs [rem_rel_def, out_reg_used_def, out_run_def, sum_bind_INR]
 >- (rename1 ‘cell_inp_run _ _ inp’ \\ cell_inp_run_cong_tac ‘inp’ \\ simp [sum_alookup_cons])
 >- (rename1 ‘sum_mapM _ inps’ \\ sum_mapM_cell_inp_run_cong_tac ‘inps’ \\ simp [sum_alookup_cons])
QED

Theorem rtl_rem_unused_regs_correct:
 !cir env fext fbits fbits' n.
 deterministic_circuit cir /\
 blast_regs_distinct (circuit_regs cir) ∧
 circuit_run fext fbits cir n = INR (env, fbits') ==>
 circuit_extenv (rtl_rem_unused_regs cir) = circuit_extenv cir ∧
 (∀regi rdata. ALOOKUP (circuit_regs (rtl_rem_unused_regs cir)) regi = SOME rdata ⇒
               ALOOKUP (circuit_regs cir) regi = SOME rdata) ∧
 deterministic_circuit (rtl_rem_unused_regs cir) /\
 ?env' fbits'. circuit_run fext fbits (rtl_rem_unused_regs cir) n = INR (env', fbits') /\
               (!var. sum_alookup env' var = sum_alookup env var)
Proof
 Cases \\ rename1 ‘Circuit fextenv outs regs combs_nl ffs_nl’ \\
 rw [circuit_run_def, sum_bind_INR, rtl_rem_unused_regs_def, circuit_extenv_def, deterministic_circuit_def]
 >- (fs [circuit_regs_def] \\
     fs [blast_regs_distinct_def, blast_reg_name_def, ALOOKUP_SOME_FILTER_gen, SF SFY_ss])
 >- fs [deterministic_regs_def, EVERY_FILTER_IMP] \\

 drule_strip init_run_rem_rel \\
 disch_then (qspecl_then [‘<|env := []; fbits := fbits|>’, ‘outs’, ‘combs_nl’, ‘ffs_nl’] mp_tac) \\
 impl_tac >- simp [rem_rel_def] \\ strip_tac \\ simp [] \\

 drule_strip netlist_run_rem_rel \\ simp [] \\

 fs [circuit_ok_def] \\
 drule_strip outs_run_rem_rel \\ 

 simp [rem_rel_def]
QED

Triviality all_distinct_map_filter:
 !l f P. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
 Induct \\ rw [MEM_MAP, MEM_FILTER] \\ metis_tac []
QED

Theorem rtl_rem_unused_regs_preserves:
 !cir.
 (!min combs_max ffs_max. circuit_ok min combs_max ffs_max cir ==> circuit_ok min combs_max ffs_max (rtl_rem_unused_regs cir)) /\
 (circuit_sorted cir ==> circuit_sorted (rtl_rem_unused_regs cir))
Proof
 Cases \\ rw [rtl_rem_unused_regs_def, circuit_ok_def, regs_ok_def, EVERY_FILTER_IMP,
              circuit_sorted_def, regs_distinct_def, all_distinct_map_filter]
QED

Theorem rtl_rem_unused_regs_mem_regs_lem:
 ∀cir regi. MEM regi (MAP FST (circuit_regs (rtl_rem_unused_regs cir))) ⇒
            MEM regi (MAP FST (circuit_regs cir))
Proof
 Cases \\ rw [rtl_rem_unused_regs_def, circuit_regs_def, MEM_MAP, MEM_FILTER] \\ metis_tac []
QED

val _ = export_theory ();
