open hardwarePreamble;

open sptreeTheory balanced_mapTheory;

open oracleTheory sumExtraTheory RTLTheory RTLTypeTheory RTLPropsTheory;

open RTLLib;

val _ = new_theory "BetterLEC";

(** Misc **)

Theorem all_mems:
 ∀l1 l2. l1 = l2 ⇒ EVERY (\e. MEM e l1) l2
Proof
 simp [EVERY_MEM]
QED

Theorem EVERY_MEM_compute:
 (∀l. EVERY (\e. MEM e l) [] ⇔ T) ∧
 (∀l h t. EVERY (\e. MEM e l) (h::t) ⇔ MEM h l ∧ EVERY (\e. MEM e l) t)
Proof
 simp []
QED

(** Lifting **)

Definition reg_in_regs_def:
 (reg_in_regs reg i [] ⇔ F) ∧
 (reg_in_regs reg i ((_,reg',i',_,_)::(regs:regty list)) ⇔
  (reg = reg' ∧ i = i') ∨ reg_in_regs reg i regs)
End

Definition cell_input_ok_def:
 (cell_input_ok regs fextty (ConstInp _) ⇔ T) ∧
 (cell_input_ok regs fextty (ExtInp var idx) ⇔ case ALOOKUP fextty var of
                                                NONE => F
                                               | SOME CBool_t => idx = NONE
                                               | SOME (CArray_t tlen) =>
                                                   case idx of
                                                     NONE => F
                                                   | SOME idx => idx < tlen) ∧
 (cell_input_ok regs fextty (VarInp (RegVar reg i) idx) ⇔ reg_in_regs reg i regs ∧ idx = NONE) ∧
 (cell_input_ok regs fextty (VarInp (NetVar n) idx) ⇔ T) (* Not statically validated *)
End

Definition cell_ok_def:
 (cell_inps_ok regs fextty (NDetCell out t) ⇔ F) ∧
 (cell_inps_ok regs fextty (Cell1 cell1 out in1) ⇔ cell_input_ok regs fextty in1) ∧
 (cell_inps_ok regs fextty (Cell2 cell2 out in1 in2) ⇔ cell_input_ok regs fextty in1 ∧
                                                       cell_input_ok regs fextty in2) ∧
 (cell_inps_ok regs fextty (CellMux out in1 in2 in3) ⇔ cell_input_ok regs fextty in1 ∧
                                                       cell_input_ok regs fextty in2 ∧
                                                       cell_input_ok regs fextty in3) ∧
 (cell_inps_ok regs fextty (CellArrayWrite out in1 idx in2) ⇔ F) ∧
 (cell_inps_ok regs fextty (CellLUT out ins tb) ⇔ EVERY (cell_input_ok regs fextty) ins) ∧
 (cell_inps_ok regs fextty (Carry4 out1 out2 in1 ins1 ins2) ⇔ cell_input_ok regs fextty in1 ∧
                                                              EVERY (cell_input_ok regs fextty) ins1 ∧
                                                              EVERY (cell_input_ok regs fextty) ins2)
End

Definition is_initial_state_def:
 is_initial_state s ⇔ (∀n. cget_var s (NetVar n) = INL UnknownVariable)
End

Definition is_initial_state_with_regs_def:
 is_initial_state_with_regs regs s ⇔
  (∀n. cget_var s (NetVar n) = INL UnknownVariable) ∧
  (∀reg i. reg_in_regs reg i regs ⇒ ∃b. cget_var s (RegVar reg i) = INR (CBool b))
End

Definition Eval_def:
 Eval fext st nl inp b ⇔
  ∀st'. is_initial_state st ∧
        sum_foldM (cell_run fext) st nl = INR st' ⇒
        cell_inp_run fext st' inp = INR (CBool b)
End

Theorem Eval_ConstInp:
 !b nl. Eval fext st nl (ConstInp (CBool b)) b
Proof
 rw [Eval_def, cell_inp_run_def]
QED

Definition fext_bool_def:
 fext_bool fext var b ⇔ fext var = INR (CBool b)
End

Definition fext_array_def:
 fext_array fext var i b ⇔
 ∃bs. fext var = INR (CArray bs) ∧ cget_fext_var (SOME i) (CArray bs) = INR (CBool b)
End

Theorem Eval_ExtInp_NONE:
 !var b nl. fext_bool fext var b ⇒ Eval fext st nl (ExtInp var NONE) b
Proof
 rw [fext_bool_def, Eval_def, cell_inp_run_def, cget_fext_var_def, sum_bind_def]
QED

Theorem Eval_ExtInp_SOME:
 !var i b nl. fext_array fext var i b ⇒ Eval fext st nl (ExtInp var (SOME i)) b
Proof
 rw [fext_array_def, Eval_def, cell_inp_run_def] \\ rw [sum_bind_def]
QED

Theorem Eval_RegVar_CBool:
 !reg i regv nl. cget_var st (RegVar reg i) = INR (CBool regv) ==> Eval fext st nl (VarInp (RegVar reg i) NONE) regv
Proof
 rw [Eval_def, cell_inp_run_def] \\ drule_strip cells_run_cget_var_RegVar \\
 simp [sum_bind_def, cget_fext_var_def]
QED

Theorem Eval_refl_thm_for_NetVar:
 ∀inp b nl. Eval fext st nl inp b ⇒ Eval fext st nl inp b
Proof
 simp []
QED

Theorem cells_run_is_initial_state_NetVar:
 ∀nl fext st st' out v.
 sum_foldM (cell_run fext) st nl = INR st' ∧
 is_initial_state st ∧
 cget_var st' (NetVar out) = INR v ⇒
 MEM out (FLAT (MAP cell_output nl))
Proof
 listLib.SNOC_INDUCT_TAC \\ rpt strip_tac
 >- rfs [sum_foldM_def, is_initial_state_def]
 \\ fs [sum_foldM_SNOC, sum_bind_INR] \\ drule_first \\ simp [MAP_SNOC, rich_listTheory.FLAT_SNOC] \\
    strip_tac \\ Cases_on ‘MEM out (cell_output x)’ \\ simp [] \\ drule_strip cell_run_unchanged \\ fs []
QED

Theorem cells_run_TAKE:
 ∀n nl st st' fext.
 sum_foldM (cell_run fext) st nl = INR st' ∧
 is_initial_state st ∧
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∃st''. sum_foldM (cell_run fext) st (TAKE n nl) = INR st'' ∧
        ∀var v. cget_var st'' var = INR v ⇒ cget_var st' var = INR v
Proof
 rpt gen_tac \\ qspecl_then [‘n’, ‘nl’] (assume_tac o SYM) TAKE_DROP \\
 pop_assum (fn th => once_rewrite_tac [Ntimes th 2]) \\
 PURE_REWRITE_TAC [sum_foldM_append, sum_bind_INR, MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] \\
 rpt strip_tac \\ fs [] \\ Cases \\ rpt strip_tac >- metis_tac [cells_run_cget_var_RegVar] \\
 last_x_assum assume_tac \\ drule_strip cells_run_is_initial_state_NetVar \\ drule_first \\
 metis_tac [cells_run_unchanged]
QED

Theorem MEM_TAKE_EL_DROP:
 ∀l x. MEM x l ⇔ ∃n. n < LENGTH l ∧ x = EL n l ∧ l = TAKE n l ++ [x] ++ DROP (SUC n) l
Proof
 Induct \\ rw [] \\ eq_tac \\ strip_tac
 >- (qexists_tac ‘0’ \\ simp [])
 >- (qexists_tac ‘SUC n’ \\ simp [] \\ metis_tac [])
 >- (Cases_on ‘n’ \\ fs [] \\ metis_tac [])
QED

Theorem cell_run_INR_cell_inputs_INR:
 ∀cell inp fext st st'.
 cell_run fext st cell = INR st' ∧ MEM inp (cell_inputs cell) ⇒
 ∃v'. cell_inp_run fext st inp = INR v'
Proof
 Cases \\ cell_run_tac rw \\ fs [cell_inputs_def]
 >- (imp_res_tac sum_mapM_EVERY \\ fs [EVERY_MEM])
 \\ every_case_tac \\ fs [] \\ imp_res_tac sum_mapM_EVERY \\ fs [EVERY_MEM]
QED

Theorem Eval_MEM_TAKE_EL_DROP:
 ∀nl cell st st' fext.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ∧
 is_initial_state st ∧
 MEM cell nl ∧
 sum_foldM (cell_run fext) st nl = INR st' ⇒
 ∃n st1 st2.
  sum_foldM (cell_run fext) st (TAKE n nl) = INR st1 ∧
  (∀inp. MEM inp (cell_inputs cell) ⇒ cell_inp_run fext st1 inp = cell_inp_run fext st' inp) ∧
  
  cell_run fext st1 cell = INR st2 ∧
  
  sum_foldM (cell_run fext) st2 (DROP (SUC n) nl) = INR st' ∧
  (∀out idx. MEM out (cell_output cell) ⇒
             cell_inp_run fext st' (VarInp (NetVar out) idx) = cell_inp_run fext st2 (VarInp (NetVar out) idx))
Proof
 rw [Once MEM_TAKE_EL_DROP] \\
 qpat_assum ‘sum_foldM _ _ _ = _’ mp_tac \\ qpat_assum ‘nl = _’ (once_rewrite_tac o sing o Once) \\
 simp [sum_foldM_append] \\ simp [sum_foldM_def, sum_bind_INR] \\ strip_tac \\
 rpt asm_exists_any_tac \\ conj_tac
 >-
 (qpat_x_assum ‘sum_foldM _ _ nl = _’ assume_tac \\
 rpt strip_tac \\ drule_strip cells_run_TAKE \\ first_x_assum (qspec_then ‘n’ strip_assume_tac) \\
 fs [] \\ rveq \\ rpt strip_tac \\
 drule_strip cell_run_INR_cell_inputs_INR \\
 drule_strip cell_inp_run_INR_cong \\ simp [])
 \\
 rpt strip_tac \\ drule_strip cells_run_unchanged \\ disch_then (qspec_then ‘out’ mp_tac) \\
 impl_tac >- (qpat_x_assum ‘ALL_DISTINCT _’ mp_tac \\
              qpat_assum ‘nl = _’ (rewrite_tac o sing o Once) \\
              simp [ALL_DISTINCT_APPEND]) \\
 strip_tac \\ simp [cell_inp_run_def]
QED

Theorem Eval_CNot:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀in1 in1b in2 in2b out.
 MEM (Cell1 CNot out in1) nl ∧
 Eval fext st nl in1 in1b ⇒
 Eval fext st nl (VarInp (NetVar out) NONE) ~in1b
Proof
 rw [Eval_def] \\ drule_strip Eval_MEM_TAKE_EL_DROP \\ fs [cell_inputs_def, cell_output_def] \\

 fs [cell_run_def, sum_bind_INR] \\ rfs [] \\ rveq \\ fs [cell1_run_def] \\
 rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def]
QED

Theorem Eval_CAnd:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀in1 in1b in2 in2b out.
 MEM (Cell2 CAnd out in1 in2) nl ∧
 Eval fext st nl in1 in1b /\ Eval fext st nl in2 in2b ==>
 Eval fext st nl (VarInp (NetVar out) NONE) (in1b /\ in2b)
Proof
 rw [Eval_def] \\ drule_strip Eval_MEM_TAKE_EL_DROP \\ fs [cell_inputs_def, cell_output_def] \\

 fs [cell_run_def, sum_bind_INR] \\ rfs [] \\ rveq \\ fs [cell2_run_def] \\
 rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def]
QED

Theorem Eval_COr:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀in1 in1b in2 in2b out.
 MEM (Cell2 COr out in1 in2) nl ∧
 Eval fext st nl in1 in1b /\ Eval fext st nl in2 in2b ==>
 Eval fext st nl (VarInp (NetVar out) NONE) (in1b \/ in2b)
Proof
 (* Same proof as CAnd: *)
 rw [Eval_def] \\ drule_strip Eval_MEM_TAKE_EL_DROP \\ fs [cell_inputs_def, cell_output_def] \\

 fs [cell_run_def, sum_bind_INR] \\ rfs [] \\ rveq \\ fs [cell2_run_def] \\
 rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def]
QED

Theorem Eval_CEqual:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀in1 in1b in2 in2b out.
 MEM (Cell2 CEqual out in1 in2) nl ∧
 Eval fext st nl in1 in1b /\ Eval fext st nl in2 in2b ==>
 Eval fext st nl (VarInp (NetVar out) NONE) (in1b = in2b)
Proof
 (* Same proof as CAnd: *)
 rw [Eval_def] \\ drule_strip Eval_MEM_TAKE_EL_DROP \\ fs [cell_inputs_def, cell_output_def] \\

 fs [cell_run_def, sum_bind_INR] \\ rfs [] \\ rveq \\ fs [cell2_run_def] \\
 rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def]
QED

Theorem Eval_mux:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀in1 in1b in2 in2b in3 in3b out.
 MEM (CellMux out in1 in2 in3) nl ∧
 Eval fext st nl in1 in1b /\ Eval fext st nl in2 in2b /\ Eval fext st nl in3 in3b ==>
 Eval fext st nl (VarInp (NetVar out) NONE) (if in1b then in2b else in3b)
Proof
 (* Not the same as above proofs: *)
 simp [Eval_def] \\ rpt strip_tac' \\ drule_strip Eval_MEM_TAKE_EL_DROP \\ fs [cell_inputs_def, cell_output_def] \\

 fs [cell_run_def, sum_bind_INR] \\ rfs [] \\ rveq \\ fs [cellMux_run_def] \\
 rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def]
QED

val gen_lut_cond_def = Define `
 (gen_lut_cond ins [] <=> F) /\
 (gen_lut_cond ins (i::is) <=> LIST_REL $= ins i \/ gen_lut_cond ins is)`;

Theorem gen_lut_cond_MEM:
 ∀tb bs. gen_lut_cond bs tb ⇔ MEM bs tb
Proof
 Induct \\ rw [gen_lut_cond_def]
QED

val lut_tac =
 rw [Eval_def] \\ drule_strip Eval_MEM_TAKE_EL_DROP \\ fs [cell_inputs_def, cell_output_def] \\

 fs [cell_run_def, cellLUT_run_def, sum_bind_INR] \\
 fs [sum_mapM_INR] \\ rveq \\
 fs [sum_mapM_INR, get_bool_INR] \\ rveq \\

 rfs [] \\ rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def, gen_lut_cond_MEM];

Theorem Eval_LUT2:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀in1 in1b in2 in2b b out tb.
 MEM (CellLUT out [in1; in2] tb) nl ∧
 Eval fext st nl in1 in1b /\
 Eval fext st nl in2 in2b ==>
 Eval fext st nl (VarInp (NetVar out) NONE) (gen_lut_cond [in1b; in2b] tb)
Proof
 lut_tac
QED

Theorem Eval_LUT3:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀in1 in1b in2 in2b in3 in3b b out tb.
 MEM (CellLUT out [in1; in2; in3] tb) nl ∧
 Eval fext st nl in1 in1b /\
 Eval fext st nl in2 in2b /\
 Eval fext st nl in3 in3b ==>
 Eval fext st nl (VarInp (NetVar out) NONE) (gen_lut_cond [in1b; in2b; in3b] tb)
Proof
 lut_tac
QED

Theorem Eval_LUT4:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀in1 in1b in2 in2b in3 in3b in4 in4b b out tb.
 MEM (CellLUT out [in1; in2; in3; in4] tb) nl ∧
 Eval fext st nl in1 in1b /\
 Eval fext st nl in2 in2b /\
 Eval fext st nl in3 in3b ∧
 Eval fext st nl in4 in4b ==>
 Eval fext st nl (VarInp (NetVar out) NONE) (gen_lut_cond [in1b; in2b; in3b; in4b] tb)
Proof
 lut_tac
QED

Theorem Eval_LUT5:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀in1 in1b in2 in2b in3 in3b in4 in4b in5 in5b b out tb.
 MEM (CellLUT out [in1; in2; in3; in4; in5] tb) nl ∧
 Eval fext st nl in1 in1b /\
 Eval fext st nl in2 in2b /\
 Eval fext st nl in3 in3b ∧
 Eval fext st nl in4 in4b ∧
 Eval fext st nl in5 in5b ==>
 Eval fext st nl (VarInp (NetVar out) NONE) (gen_lut_cond [in1b; in2b; in3b; in4b; in5b] tb)
Proof
 lut_tac
QED

Theorem Eval_LUT6:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀in1 in1b in2 in2b in3 in3b in4 in4b in5 in5b in6 in6b b out tb.
 MEM (CellLUT out [in1; in2; in3; in4; in5; in6] tb) nl ∧
 Eval fext st nl in1 in1b /\
 Eval fext st nl in2 in2b /\
 Eval fext st nl in3 in3b ∧
 Eval fext st nl in4 in4b ∧
 Eval fext st nl in5 in5b ∧
 Eval fext st nl in6 in6b ==>
 Eval fext st nl (VarInp (NetVar out) NONE) (gen_lut_cond [in1b; in2b; in3b; in4b; in5b; in6b] tb)
Proof
 lut_tac
QED

Theorem Eval_Carry4:
 ∀nl.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∀cin cinb lhs0 lhs0b lhs1 lhs1b lhs2 lhs2b lhs3 lhs3b rhs0 rhs0b rhs1 rhs1b rhs2 rhs2b rhs3 rhs3b out cout.
 MEM (Carry4 out cout cin [lhs0; lhs1; lhs2; lhs3] [rhs0; rhs1; rhs2; rhs3]) nl ∧
 Eval fext st nl cin cinb ∧
 Eval fext st nl lhs0 lhs0b ∧
 Eval fext st nl lhs1 lhs1b ∧
 Eval fext st nl lhs2 lhs2b ∧
 Eval fext st nl lhs3 lhs3b ∧

 Eval fext st nl rhs0 rhs0b ∧
 Eval fext st nl rhs1 rhs1b ∧
 Eval fext st nl rhs2 rhs2b ∧
 Eval fext st nl rhs3 rhs3b ∧

 out ≠ cout ⇒
 Eval fext st nl
              (VarInp (NetVar out) (SOME 0))
              (rhs3b ⇎ cinb) ∧
 Eval fext st nl
              (VarInp (NetVar out) (SOME 1))
              (rhs2b ⇎ if rhs3b then cinb else lhs3b) ∧
 Eval fext st nl
              (VarInp (NetVar out) (SOME 2))
              (rhs1b ⇎ if rhs2b then if rhs3b then cinb else lhs3b else lhs2b) ∧
 Eval fext st nl
              (VarInp (NetVar out) (SOME 3))
              (rhs0b ⇎ if rhs1b then if rhs2b then if rhs3b then cinb else lhs3b else lhs2b else lhs1b) ∧
 Eval fext st nl
              (VarInp (NetVar cout) (SOME 0))
              (if rhs3b then cinb else lhs3b) ∧
 Eval fext st nl
              (VarInp (NetVar cout) (SOME 1))
              (if rhs2b then if rhs3b then cinb else lhs3b else lhs2b) ∧
 Eval fext st nl
              (VarInp (NetVar cout) (SOME 2))
              (if rhs1b then if rhs2b then if rhs3b then cinb else lhs3b else lhs2b else lhs1b) ∧
 Eval fext st nl
              (VarInp (NetVar cout) (SOME 3))
              (if rhs0b then if rhs1b then if rhs2b then if rhs3b then cinb else lhs3b else lhs2b else lhs1b else lhs0b)
Proof
 rw [Eval_def] \\ drule_strip Eval_MEM_TAKE_EL_DROP \\ fs [cell_inputs_def, cell_output_def] \\

 rfs [cell_run_def, cellCarry4_run_def, get_bool_def, sum_bind_def, sum_map_def, sum_mapM_def] \\
 rveq \\ simp [carry4_muxcy_def, carry4_xor_def, cell_inp_run_cset_var'] \\
 simp [cget_fext_var_def, sum_revEL_revEL, revEL_def, sum_map_def]
QED

(*(* Simple to prove that gates have the same output when in same netlist ... *)
Theorem same_output_in_same_netlist:
 Eval fext st nl out1 b1 /\ Eval fext st nl out2 b2 ==>
 b1 = b2 ==>
 sum_foldM (cell_run fext) st nl = INR st' ==>
 cell_inp_run fext st' out1 = cell_inp_run fext st' out2
Proof
 rw [Eval_def]
QED

Theorem same_output_in_diff_netlist:
 Eval fext st1 nl1 out1 b1 /\ Eval fext st2 nl2 out2 b2 ==>
 (b1 = b2) ==>
 is_initial_state st1 /\ is_initial_state st2 /\ (* <-- temporary line? *)
 sum_foldM (cell_run fext) st1 nl1 = INR st1' /\
 sum_foldM (cell_run fext) st2 nl2 = INR st2' ==>
 cell_inp_run fext st1' out1 = cell_inp_run fext st2' out2
Proof
 rw [Eval_def]
QED*)

(** "Better" LEC **)

Definition cell_inp_rel_def:
 cell_inp_rel regs fextty fext st nl nlnew inp ⇔
  ∀stold stnew.
  is_initial_state_with_regs regs st ∧
  rtltype_extenv_n fextty fext ∧
  sum_foldM (cell_run fext) st nl = INR stold ∧
  sum_foldM (cell_run fext) st nlnew = INR stnew ⇒
  cell_inp_run fext stnew inp = cell_inp_run fext stold inp ∧
  ∃b. cell_inp_run fext stold inp = INR (CBool b)
End

Theorem cell_inp_rel_ConstInp:
 ∀regs fextty nl nlnew b. cell_inp_rel regs fextty fext st nl nlnew (ConstInp (CBool b))
Proof
 rw [cell_inp_rel_def, cell_inp_run_def]
QED

Theorem cell_inp_rel_ExtInp:
 ∀regs fextty nl nlnew var idx.
 cell_input_ok regs fextty (ExtInp var idx) ⇒ cell_inp_rel regs fextty fext st nl nlnew (ExtInp var idx)
Proof
 rw [cell_input_ok_def, cell_inp_rel_def, rtltype_extenv_n_def, cell_inp_run_def] \\
 every_case_tac \\ fs [] \\ drule_first \\
 fs [rtltype_v_cases, sum_bind_def, cget_fext_var_def, sum_revEL_revEL, sum_map_def]
QED

Theorem cell_inp_rel_VarInp_RegVar:
 ∀regs fextty nl nlnew reg i.
 reg_in_regs reg i regs ⇒ cell_inp_rel regs fextty fext st nl nlnew (VarInp (RegVar reg i) NONE)
Proof
 simp [cell_inp_rel_def, cell_inp_run_def, is_initial_state_with_regs_def] \\
 metis_tac [cells_run_cget_var_RegVar]
QED

Theorem is_initial_state_with_regs_is_initial_state:
 ∀regs st. is_initial_state_with_regs regs st ⇒ is_initial_state st
Proof
 rw [is_initial_state_with_regs_def, is_initial_state_def]
QED

(* Just for experiments, CNot will never occur in both netlists... *)
(*Theorem cell_inp_rel_CNot:
 ∀regs fextty nl nlnew in1 out.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ∧
 ALL_DISTINCT (FLAT (MAP cell_output nlnew)) ∧
 MEM (Cell1 CNot out in1) nl ∧
 MEM (Cell1 CNot out in1) nlnew ∧
 cell_inp_rel regs fextty fext st nl nlnew in1 ⇒
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar out) NONE)
Proof
 simp [cell_inp_rel_def] \\ rpt strip_tac' \\ drule_first \\

 drule_strip is_initial_state_with_regs_is_initial_state \\
 drule_strip Eval_MEM_TAKE_EL_DROP \\
 last_x_assum assume_tac \\ drule_strip Eval_MEM_TAKE_EL_DROP \\
 fs [cell_inputs_def, cell_output_def] \\

 fs [cell_run_def, sum_bind_INR] \\ rfs [] \\ rveq \\ fs [cell1_run_def] \\
 rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def]
QED*)

val lut_tac =
 simp [cell_inp_rel_def] \\ rpt strip_tac' \\ rpt drule_first \\

 drule_strip is_initial_state_with_regs_is_initial_state \\
 drule_strip Eval_MEM_TAKE_EL_DROP \\
 last_x_assum assume_tac \\ drule_strip Eval_MEM_TAKE_EL_DROP \\
 fs [cell_inputs_def, cell_output_def] \\

 fs [cell_run_def, cellLUT_run_def, sum_bind_INR] \\ rveq \\

 fs [sum_mapM_INR] \\ rveq \\
 fs [sum_mapM_INR, get_bool_INR] \\ rveq \\

 rfs [] \\ rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def];

Theorem cell_inp_rel_LUT2:
 ∀regs fextty nl nlnew out in1 in2 tb.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ∧
 ALL_DISTINCT (FLAT (MAP cell_output nlnew)) ∧
 MEM (CellLUT out [in1; in2] tb) nl ∧
 MEM (CellLUT out [in1; in2] tb) nlnew ∧
 cell_inp_rel regs fextty fext st nl nlnew in1 ∧
 cell_inp_rel regs fextty fext st nl nlnew in2 ⇒
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar out) NONE)
Proof
 lut_tac
QED

Theorem cell_inp_rel_LUT3:
 ∀regs fextty nl nlnew out in1 in2 in3 tb.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ∧
 ALL_DISTINCT (FLAT (MAP cell_output nlnew)) ∧
 MEM (CellLUT out [in1; in2; in3] tb) nl ∧
 MEM (CellLUT out [in1; in2; in3] tb) nlnew ∧
 cell_inp_rel regs fextty fext st nl nlnew in1 ∧
 cell_inp_rel regs fextty fext st nl nlnew in2 ∧
 cell_inp_rel regs fextty fext st nl nlnew in3 ⇒
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar out) NONE)
Proof
 lut_tac
QED

Theorem cell_inp_rel_LUT4:
 ∀regs fextty nl nlnew out in1 in2 in3 in4 tb.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ∧
 ALL_DISTINCT (FLAT (MAP cell_output nlnew)) ∧
 MEM (CellLUT out [in1; in2; in3; in4] tb) nl ∧
 MEM (CellLUT out [in1; in2; in3; in4] tb) nlnew ∧
 cell_inp_rel regs fextty fext st nl nlnew in1 ∧
 cell_inp_rel regs fextty fext st nl nlnew in2 ∧
 cell_inp_rel regs fextty fext st nl nlnew in3 ∧
 cell_inp_rel regs fextty fext st nl nlnew in4 ⇒
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar out) NONE)
Proof
 lut_tac
QED

Theorem cell_inp_rel_LUT5:
 ∀regs fextty nl nlnew out in1 in2 in3 in4 in5 tb.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ∧
 ALL_DISTINCT (FLAT (MAP cell_output nlnew)) ∧
 MEM (CellLUT out [in1; in2; in3; in4; in5] tb) nl ∧
 MEM (CellLUT out [in1; in2; in3; in4; in5] tb) nlnew ∧
 cell_inp_rel regs fextty fext st nl nlnew in1 ∧
 cell_inp_rel regs fextty fext st nl nlnew in2 ∧
 cell_inp_rel regs fextty fext st nl nlnew in3 ∧
 cell_inp_rel regs fextty fext st nl nlnew in4 ∧
 cell_inp_rel regs fextty fext st nl nlnew in5 ⇒
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar out) NONE)
Proof
 lut_tac
QED

Theorem cell_inp_rel_LUT6:
 ∀regs fextty nl nlnew out in1 in2 in3 in4 in5 in6 tb.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ∧
 ALL_DISTINCT (FLAT (MAP cell_output nlnew)) ∧
 MEM (CellLUT out [in1; in2; in3; in4; in5; in6] tb) nl ∧
 MEM (CellLUT out [in1; in2; in3; in4; in5; in6] tb) nlnew ∧
 cell_inp_rel regs fextty fext st nl nlnew in1 ∧
 cell_inp_rel regs fextty fext st nl nlnew in2 ∧
 cell_inp_rel regs fextty fext st nl nlnew in3 ∧
 cell_inp_rel regs fextty fext st nl nlnew in4 ∧
 cell_inp_rel regs fextty fext st nl nlnew in5 ∧
 cell_inp_rel regs fextty fext st nl nlnew in6 ⇒
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar out) NONE)
Proof
 lut_tac
QED

Theorem cell_inp_rel_Carry4:
 ∀regs fextty nl nlnew out cout cin lhs0 lhs1 lhs2 lhs3 rhs0 rhs1 rhs2 rhs3.
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ∧
 ALL_DISTINCT (FLAT (MAP cell_output nlnew)) ∧
 MEM (Carry4 out cout cin [lhs0; lhs1; lhs2; lhs3] [rhs0; rhs1; rhs2; rhs3]) nl ∧
 MEM (Carry4 out cout cin [lhs0; lhs1; lhs2; lhs3] [rhs0; rhs1; rhs2; rhs3]) nlnew ∧
 cell_inp_rel regs fextty fext st nl nlnew cin ∧
 cell_inp_rel regs fextty fext st nl nlnew lhs0 ∧
 cell_inp_rel regs fextty fext st nl nlnew lhs1 ∧
 cell_inp_rel regs fextty fext st nl nlnew lhs2 ∧
 cell_inp_rel regs fextty fext st nl nlnew lhs3 ∧
 cell_inp_rel regs fextty fext st nl nlnew rhs0 ∧
 cell_inp_rel regs fextty fext st nl nlnew rhs1 ∧
 cell_inp_rel regs fextty fext st nl nlnew rhs2 ∧
 cell_inp_rel regs fextty fext st nl nlnew rhs3 ⇒
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar out) (SOME 0)) ∧
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar out) (SOME 1)) ∧
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar out) (SOME 2)) ∧
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar out) (SOME 3)) ∧
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar cout) (SOME 0)) ∧
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar cout) (SOME 1)) ∧
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar cout) (SOME 2)) ∧
 cell_inp_rel regs fextty fext st nl nlnew (VarInp (NetVar cout) (SOME 3))
Proof
 simp [cell_inp_rel_def] \\ rpt strip_tac' \\ rpt conj_tac \\ rpt strip_tac' \\

 drule_strip is_initial_state_with_regs_is_initial_state \\
 drule_strip Eval_MEM_TAKE_EL_DROP \\
 last_x_assum assume_tac \\ drule_strip Eval_MEM_TAKE_EL_DROP \\
 fs [cell_inputs_def, cell_output_def] \\

 rfs [cell_run_def, cellCarry4_run_def, sum_bind_INR, sum_mapM_INR] \\
 fs [sum_mapM_def, get_bool_def, sum_map_INR] \\ rveq \\ fs [] \\ rveq \\ fs [] \\

 rw [cell_inp_run_def, cget_var_cset_var, cget_fext_var_def,
     sum_bind_def, sum_map_def, sum_revEL_revEL, revEL_def]
QED

Theorem Eval_Eval_cell_inp_rel:
 ∀regs fextty nl nlnew out b1 b2.
 Eval fext st nl out b1 /\ Eval fext st nlnew out b2 ==>
 (b1 = b2) ==>
 cell_inp_rel regs fextty fext st nl nlnew out
Proof
 simp [Eval_def, cell_inp_rel_def] \\ metis_tac [is_initial_state_with_regs_is_initial_state]
QED

Theorem cell_inp_rel_remove_tmp_NetVar:
 cell_inp_rel regs fextty fext st nl nlnew inp1 ⇒
  
 (∀b. Eval fext st nl inp1 b ⇒
      Eval fext st nlnew inp1 b ⇒
      cell_inp_rel regs fextty fext st nl nlnew inp2) ⇒

 cell_inp_rel regs fextty fext st nl nlnew inp2
Proof
 simp [cell_inp_rel_def, Eval_def] \\ rpt strip_tac' \\ rpt drule_first \\
 drule_strip is_initial_state_with_regs_is_initial_state \\
 first_x_assum irule \\ rw []
QED

Theorem cell_inp_rel_remove_tmp_RegVar:
 (∀b. cget_var st (RegVar reg i) = INR (CBool b) ⇒
      cell_inp_rel regs fextty fext st nl nlnew inp) ⇒

 reg_in_regs reg i regs ⇒

 cell_inp_rel regs fextty fext st nl nlnew inp
Proof
 simp [cell_inp_rel_def, is_initial_state_with_regs_def]
QED

Theorem cell_inp_rel_remove_tmp_fext_bool:
 (∀b. fext_bool fext var b ⇒
      cell_inp_rel regs fextty fext st nl nlnew inp) ⇒

 cell_input_ok regs fextty (ExtInp var NONE) ⇒

 cell_inp_rel regs fextty fext st nl nlnew inp
Proof
 simp [fext_bool_def, cell_inp_rel_def, rtltype_extenv_n_def, cell_input_ok_def] \\ rpt strip_tac' \\
 every_case_tac \\ fs [] \\ drule_first \\
 fs [rtltype_v_cases]
QED

Theorem cell_inp_rel_remove_tmp_fext_array:
 (∀b. fext_array fext var i b ⇒
      cell_inp_rel regs fextty fext st nl nlnew inp) ⇒

 cell_input_ok regs fextty (ExtInp var (SOME i)) ⇒

 cell_inp_rel regs fextty fext st nl nlnew inp
Proof
 simp [fext_array_def, cell_inp_rel_def, rtltype_extenv_n_def, cell_input_ok_def] \\ rpt strip_tac' \\
 every_case_tac \\ fs [] \\ drule_first \\
 fs [rtltype_v_cases, cget_fext_var_def, sum_revEL_revEL, sum_map_def] 
QED

(** Thms to lift from netlist level to circuit level **)

Definition populated_by_regs_def:
 populated_by_regs regs st ⇔
 EVERY (λ(t, reg, i, _, _). t = CBool_t ∧ ∃b. cget_var st (RegVar reg i) = INR (CBool b)) regs
End

Definition populated_by_regs_only_def:
 populated_by_regs_only regs st ⇔
 populated_by_regs regs st ∧
 (∀n. cget_var st (NetVar n) = INL UnknownVariable)
End

Theorem populated_by_regs_fbits:
 ∀regs s fbits. populated_by_regs regs (s with fbits := fbits) ⇔ populated_by_regs regs s
Proof
 rw [populated_by_regs_def, cget_var_fbits]
QED

Theorem populated_by_regs_only_fbits:
 ∀regs s fbits. populated_by_regs_only regs (s with fbits := fbits) ⇔ populated_by_regs_only regs s
Proof
 rw [populated_by_regs_only_def, populated_by_regs_fbits, cget_var_fbits]
QED

Theorem populated_by_regs_only_populated_by_regs:
 ∀regs st. populated_by_regs_only regs st ⇒ populated_by_regs regs st
Proof
 rw [populated_by_regs_only_def]
QED

(* Glue thms *)

Theorem cleanup_cget_var_CBool:
 !reg i regs.
 MEM (CBool_t, reg, i) (MAP (λ(ty,reg,i,_,_). (ty, reg, i)) regs) ∧
 populated_by_regs_only regs st ⇒
 ∃b. cget_var st (RegVar reg i) = INR (CBool b)
Proof
 rw [populated_by_regs_only_def, populated_by_regs_def, EVERY_MEM, MEM_MAP] \\ drule_first \\
 pairarg_tac \\ fs [] \\ rveq \\ fs [rtltype_v_cases]
QED

Theorem cleanup_cget_var_CBool_imp:
 ∀regs reg i P.
 (∀b. cget_var st (RegVar reg i) = INR (CBool b) ⇒
      populated_by_regs_only regs st ⇒
      P st)
 ⇒
 (MEM (CBool_t, reg, i) (MAP (λ(ty,reg,i,_,_). (ty, reg, i)) regs) ⇒
  populated_by_regs_only regs st ⇒
  P st)
Proof
 metis_tac [cleanup_cget_var_CBool]
QED

Theorem cleanup_extenv_CBool:
 !extenv var.
 rtltype_extenv_n extenv (fext : string -> error + value) ⇒
 ALOOKUP extenv var = SOME CBool_t ⇒
 ∃b. fext var = INR (CBool b)
Proof
 rw [rtltype_extenv_n_def] \\ drule_first \\ fs [rtltype_v_cases]
QED

Theorem cleanup_extenv_CArray:
 !extenv var i.
 rtltype_extenv_n extenv (fext : string -> error + value) ⇒
 (*ALOOKUP extenv var = SOME (CArray_t len) ∧ i < len ⇒*)
 (case ALOOKUP extenv var of SOME (CArray_t len) => i < len | _ => F) ⇒ (* <-- EVALable *)
 ∃b bs. fext var = INR (CArray bs) ∧ cget_fext_var (SOME i) (CArray bs) = INR (CBool b)
Proof
 rw [rtltype_extenv_n_def] \\ every_case_tac \\ fs [] \\ drule_first \\ rfs [rtltype_v_cases] \\
 rw [cget_fext_var_def, sum_revEL_revEL, sum_map_def]
QED

Theorem init_run_unchanged:
 ∀regs s s' reg i.
 init_run s regs = INR s' ∧ ~MEM (reg, i) (MAP blast_reg_name regs) ⇒
 cget_var s' (RegVar reg i) = cget_var s (RegVar reg i)
Proof
 Induct \\ TRY PairCases \\ fs [init_run_def, blast_regs_distinct_def] \\
 rpt gen_tac \\ TOP_CASE_TAC
 >- (pairarg_tac \\ simp [] \\ strip_tac \\ drule_first \\ fs [cset_var_fbits, cget_var_fbits, cget_var_cset_var] \\
    fs [blast_reg_name_def])
 \\ rw [] \\ drule_first \\ fs [cget_var_cset_var, blast_reg_name_def]
QED

Triviality MEM_reg_regs_IMP_blast_reg_name:
 ∀r0 r1 r2 r3 r4 regs. MEM (r0,r1,r2,r3,r4) regs ⇒ MEM (r1,r2) (MAP blast_reg_name regs)
Proof
 rw [MEM_MAP] \\ qexists_tac ‘(r0,r1,r2,r3,r4)’ \\ simp [blast_reg_name_def]
QED

Theorem init_run_populated_by_regs_only:
 ∀regs s s'.
 init_run s regs = INR s' ∧ blast_regs_distinct regs ∧
 EVERY (λ(t, _, _, _, _). t = CBool_t) regs ∧ (∀n. cget_var s (NetVar n) = INL UnknownVariable) ⇒
 populated_by_regs_only regs s'
Proof
 Induct \\ TRY PairCases \\ fs [init_run_def, blast_regs_distinct_def, populated_by_regs_only_def, populated_by_regs_def] \\
 rpt gen_tac \\ TOP_CASE_TAC
 >- (pairarg_tac \\ drule_strip rtl_nd_value_type_correct \\ simp [blast_reg_name_def] \\ strip_tac \\
    drule_first \\ simp [] \\ drule_strip init_run_unchanged \\
    fs [cset_var_fbits, cget_var_fbits, cget_var_cset_var, rtltype_v_cases])
 \\ IF_CASES_TAC \\ simp [blast_reg_name_def] \\ strip_tac \\ drule_first \\ simp [] \\
    drule_strip init_run_unchanged \\ fs [cget_var_cset_var, has_rtltype_v_correct, rtltype_v_cases]
QED

(*Theorem cells_run_populated_by_regs:
 populated_by_regs regs s ∧ sum_foldM (cell_run fext) s nl = INR s' ⇒ populated_by_regs regs s'
Proof
 rw [populated_by_regs_def] \\ drule_strip cells_run_cget_var_RegVar \\ simp []
QED*)

Theorem reg_run_unchanged:
 reg_run fext s_net s_reg (h0,h1,h2,h3,h4) = INR s_reg' ∧
 blast_reg_name (h0',h1',h2',h3',h4') ≠ blast_reg_name (h0,h1,h2,h3,h4) ⇒
 cget_var s_reg' (RegVar h1' h2') = cget_var s_reg (RegVar h1' h2')
Proof
 rw [reg_run_def, CaseEq"option", sum_bind_INR, blast_reg_name_def] \\ rw [cget_var_cset_var]
QED

Theorem regs_run_unchanged:
 ∀regs fext s_net s_reg s_reg' h0 h1 h2 h3 h4.
 ¬MEM (blast_reg_name (h0,h1,h2,h3,h4)) (MAP blast_reg_name regs) ∧
 sum_foldM (reg_run fext s_net) s_reg regs = INR s_reg' ⇒
 cget_var s_reg' (RegVar h1 h2) = cget_var s_reg (RegVar h1 h2)
Proof
 Induct \\ TRY PairCases \\ simp [sum_foldM_def, sum_bind_INR] \\ rpt strip_tac \\
 drule_strip reg_run_unchanged \\ drule_first \\ simp []
QED

Theorem reg_run_populated_by_regs_only:
 ¬MEM (blast_reg_name (h0,h1,h2,h3,h4)) (MAP blast_reg_name regs) ∧
 reg_run fext s_net s_reg (h0,h1,h2,h3,h4) = INR s_reg' ∧
 populated_by_regs_only regs s_reg ⇒
 populated_by_regs_only regs s_reg'
Proof
 rw [reg_run_def, CaseEq"option", sum_bind_INR, blast_reg_name_def] \\ simp [] \\
 fs [populated_by_regs_only_def, populated_by_regs_def, cget_var_cset_var, EVERY_MEM, MEM_MAP] \\
 PairCases \\ rpt strip_tac \\ drule_first \\
 fs [] \\ metis_tac [blast_reg_name_def]
QED

Theorem regs_run_populated_by_regs_only:
 ∀regs fext s_reg s_reg' s_net.
 sum_foldM (reg_run fext s_net) s_reg regs = INR s_reg' ∧
 blast_regs_distinct regs ∧
 populated_by_regs_only regs s_reg ⇒
 populated_by_regs_only regs s_reg'
Proof
 Induct \\ TRY PairCases \\ fs [sum_foldM_def, sum_bind_INR] \\
 rpt strip_tac' \\ fs [blast_regs_distinct_def] \\ drule_strip reg_run_populated_by_regs_only \\
 fs [populated_by_regs_only_def, populated_by_regs_def] \\ strip_tac \\ drule_first \\ simp [] \\
 drule_strip regs_run_unchanged \\ fs [reg_run_def, CaseEq"option", sum_bind_INR] >- rw [] \\
 fs [cget_var_cset_var, has_rtltype_v_correct, rtltype_v_cases]
QED

Theorem netlist_step_populated_by_regs_only:
 ∀fext regs nl s s'.
 netlist_step fext s nl regs = INR s' ∧ blast_regs_distinct regs ∧
 populated_by_regs_only regs s ⇒
 populated_by_regs_only regs s'
Proof
 rw [netlist_step_def, sum_bind_INR] \\
 drule_strip regs_run_populated_by_regs_only \\
 simp [populated_by_regs_only_fbits]
QED

Theorem netlist_run_populated_by_regs_only:
 ∀n fext regs nl s s'.
 netlist_run fext s nl regs n = INR s' ∧ blast_regs_distinct regs ∧
 populated_by_regs_only regs s ⇒
 populated_by_regs_only regs s'
Proof
 Induct \\ simp [netlist_run_def, sum_bind_INR] \\ rpt strip_tac \\ drule_first \\
 drule_strip netlist_step_populated_by_regs_only
QED

Definition cell_outputs_with_types_def:
 (cell_outputs_with_types seen (CellLUT out ins tb) = insert out CBool_t seen) ∧
 (cell_outputs_with_types seen (Carry4 out cout cin lhs rhs) =
  insert out (CArray_t 4) (insert cout (CArray_t 4) seen)) ∧
 (cell_outputs_with_types seen _ = seen)
End

Definition validate_techmapped_cell_input_type_def:
 validate_techmapped_cell_input_type t idx =
  case (t, idx) of
    (SOME CBool_t, NONE) => T
  | (SOME (CArray_t len), SOME i) => i < len
  | _ => F
End

Definition reg_cmp_def:
 reg_cmp r1 r2 = pair_cmp string_cmp num_cmp r1 r2
End

Theorem reg_cmp_good:
 good_cmp reg_cmp
Proof
 metis_tac [reg_cmp_def, comparisonTheory.pair_cmp_good, comparisonTheory.string_cmp_good, comparisonTheory.num_cmp_good]
QED

Theorem reg_cmp_antisym:
 ∀r1 r2. reg_cmp r1 r2 = Equal ⇔ r1 = r2
Proof
 rpt gen_tac \\ simp [reg_cmp_def] \\ match_mp_tac comparisonTheory.pair_cmp_antisym \\ simp []
QED

Definition validate_techmapped_cell_input_def:
 (validate_techmapped_cell_input extenv regs seen (ConstInp (CBool _)) ⇔ T) ∧
 (validate_techmapped_cell_input extenv regs seen (ConstInp (CArray _)) ⇔ F) ∧
  
 (validate_techmapped_cell_input extenv regs seen (ExtInp var idx) ⇔
  (* Should probably use another data structure for extenv as well... *)
  validate_techmapped_cell_input_type (ALOOKUP extenv var) idx) ∧

 (validate_techmapped_cell_input extenv regs seen (VarInp (NetVar n) idx) ⇔
  validate_techmapped_cell_input_type (lookup n seen) idx) ∧
 (validate_techmapped_cell_input extenv regs seen (VarInp (RegVar reg i) idx) ⇔
  validate_techmapped_cell_input_type (lookup reg_cmp (reg, i) regs) idx)
End

Definition validate_techmapped_cell_def:
 (validate_techmapped_cell extenv regs seen (CellLUT out ins tb) ⇔
  EVERY (validate_techmapped_cell_input extenv regs seen) ins) ∧
 (validate_techmapped_cell extenv regs seen (Carry4 out cout cin lhs rhs) ⇔
  validate_techmapped_cell_input extenv regs seen cin ∧
  EVERY (validate_techmapped_cell_input extenv regs seen) lhs ∧ LENGTH lhs = 4 ∧
  EVERY (validate_techmapped_cell_input extenv regs seen) rhs ∧ LENGTH rhs = 4) ∧
 (validate_techmapped_cell extenv regs seen _ ⇔ F)
End

Definition validate_techmapped_netlist_itr_def:
 (validate_techmapped_netlist_itr extenv regs seen [] = T) ∧
 (validate_techmapped_netlist_itr extenv regs seen (c::cs) ⇔
  validate_techmapped_cell extenv regs seen c ∧
  validate_techmapped_netlist_itr extenv regs (cell_outputs_with_types seen c) cs)
End

Definition validate_techmapped_netlist_def:
 validate_techmapped_netlist extenv regs nl =
  validate_techmapped_netlist_itr
   extenv
   (fromList reg_cmp (MAP (λ(ty,reg,i,v,src). ((reg, i), ty)) regs))
   LN
   nl
End

Definition regs_map_inv_def:
 regs_map_inv regs regs_map ⇔
  ∀k. lookup reg_cmp k regs_map =
       ALOOKUP (MAP (λ(ty,reg,i,v,src). ((reg,i),ty)) regs) k
End

Theorem lookup_empty:
 ∀cmp k. lookup cmp k empty = NONE
Proof
 rpt gen_tac \\ EVAL_TAC
QED

Theorem regs_map_inv_init:
 ∀regs. regs_map_inv regs (fromList reg_cmp (MAP (λ(ty,reg,i,v,src). ((reg, i), ty)) regs))
Proof
 Induct \\ TRY PairCases \\ fs [regs_map_inv_def, fromList_def, lookup_empty] \\
 gen_tac \\ dep_rewrite.DEP_REWRITE_TAC [lookup_insert] \\ rpt conj_tac
 >- simp [reg_cmp_good]
 >- metis_tac [fromList_thm, fromList_def, reg_cmp_good]
 \\ simp [reg_cmp_antisym, EQ_SYM_EQ]
QED

Definition seen_present_def:
 seen_present seen s ⇔
 ∀t n. lookup n seen = SOME t ⇒ ∃v. cget_var s (NetVar n) = INR v ∧ rtltype_v v t
End

Theorem populated_by_regs_lookup:
 ∀regs s reg regs_map i t.
 populated_by_regs regs s ∧ regs_map_inv regs regs_map ∧
 lookup reg_cmp (reg, i) regs_map = SOME t ⇒
 ∃v. cget_var s (RegVar reg i) = INR v ∧ rtltype_v v t
Proof
 rw [populated_by_regs_def, regs_map_inv_def, EVERY_MEM] \\ rfs [] \\
 drule_strip alistTheory.ALOOKUP_MEM \\ fs [MEM_MAP] \\ drule_first \\ pairarg_tac \\ fs [rtltype_v_cases]
QED

Theorem validate_techmapped_cell_input_cell_inp_run:
 ∀inp extenv regs regs_map seen fext s.
 validate_techmapped_cell_input extenv regs_map seen inp ∧
 populated_by_regs regs s ∧ regs_map_inv regs regs_map ∧
 rtltype_extenv_n extenv fext ∧ seen_present seen s ⇒
 ∃v. cell_inp_run fext s inp = INR v ∧ rtltype_v v CBool_t
Proof
 Cases
 >- (* ConstInp *)
 (Cases_on ‘v’ \\ simp [validate_techmapped_cell_input_def, cell_inp_run_def, rtltype_v_cases])
 >- (* ExtInp *)
 (rw [validate_techmapped_cell_input_def, validate_techmapped_cell_input_type_def,
      cell_inp_run_def, rtltype_extenv_n_def] \\
  every_case_tac \\ fs [] \\ drule_first \\ fs [sum_bind_def, cget_fext_var_def, rtltype_v_cases] \\
  simp [sum_revEL_revEL, sum_map_def])
 >- (* VarInp *)
 (Cases_on ‘v’ \\
  rw [validate_techmapped_cell_input_def, validate_techmapped_cell_input_type_def, cell_inp_run_def]
  >- (every_case_tac \\ fs [] \\ drule_strip populated_by_regs_lookup \\
      fs [sum_bind_def, sum_map_def, cget_fext_var_def, rtltype_v_cases, sum_revEL_revEL])
  >- (every_case_tac \\ fs [seen_present_def] \\ drule_first \\
      fs [sum_bind_def, sum_map_def, cget_fext_var_def, rtltype_v_cases, sum_revEL_revEL]))
QED

Theorem validate_techmapped_cell_input_sum_mapM_cell_inp_run:
 ∀ins extenv regs regs_map seen s fext.
 EVERY (validate_techmapped_cell_input extenv regs_map seen) ins ∧
 populated_by_regs regs s ∧ regs_map_inv regs regs_map ∧
 rtltype_extenv_n extenv fext ∧
 seen_present seen s ⇒
 ∃ins'. sum_mapM (cell_inp_run fext s) ins = INR ins' ∧ EVERY (λv. rtltype_v v CBool_t) ins'
Proof
 Induct \\ rw [sum_mapM_def] \\
 drule_first \\ drule_strip validate_techmapped_cell_input_cell_inp_run \\
 simp [sum_map_def]
QED

Triviality EVERY_rtltype_v_CBool_t_sum_mapM_get_bool:
 ∀l. EVERY (λv. rtltype_v v CBool_t) l ⇒ sum_mapM get_bool l = INR (MAP (OUTR o get_bool) l)
Proof
 Induct \\ rw [sum_mapM_def] \\ fs [sum_map_def, rtltype_v_cases, get_bool_def]
QED

Theorem populated_by_regs_cset_var_NetVar:
 ∀regs s n v. populated_by_regs regs (cset_var s (NetVar n) v) ⇔ populated_by_regs regs s
Proof
 rw [populated_by_regs_def, cget_var_cset_var]
QED

Theorem seen_present_cset_var:
 ∀seen s v t out.
 seen_present seen s ∧ rtltype_v v t ⇒ seen_present (insert out t seen) (cset_var s (NetVar out) v)
Proof
 rw [seen_present_def, cget_var_cset_var, sptreeTheory.lookup_insert] \\ rw [] \\ fs []
QED

Theorem validate_techmapped_cell_run_CellLUT:
 ∀out ins tb extenv regs regs_map seen fext s.
 EVERY (validate_techmapped_cell_input extenv regs_map seen) ins ∧
 populated_by_regs regs s ∧ regs_map_inv regs regs_map ∧
 rtltype_extenv_n extenv fext ∧
 seen_present seen s ⇒
 ∃res. cell_run fext s (CellLUT out ins tb) = INR (cset_var s (NetVar out) res) ∧ rtltype_v res CBool_t ∧
       populated_by_regs regs (cset_var s (NetVar out) res) ∧
       seen_present (cell_outputs_with_types seen (CellLUT out ins tb)) (cset_var s (NetVar out) res)
Proof
 rw [cell_run_def, cellLUT_run_def] \\
 drule_strip validate_techmapped_cell_input_sum_mapM_cell_inp_run \\
 drule_strip EVERY_rtltype_v_CBool_t_sum_mapM_get_bool \\
 simp [sum_bind_def, cell_outputs_with_types_def, populated_by_regs_cset_var_NetVar] \\
 metis_tac [rtltype_v_cases, seen_present_cset_var]
QED

Theorem validate_techmapped_cell_run_Carry4:
 ∀lhs rhs out cout cin extenv regs regs_map seen fext s.
 validate_techmapped_cell_input extenv regs_map seen cin ∧
 EVERY (validate_techmapped_cell_input extenv regs_map seen) lhs ∧ LENGTH lhs = 4 ∧
 EVERY (validate_techmapped_cell_input extenv regs_map seen) rhs ∧ LENGTH rhs = 4 ∧
 populated_by_regs regs s ∧ regs_map_inv regs regs_map ∧
 rtltype_extenv_n extenv fext ∧
 seen_present seen s ⇒
 ∃outv coutv.
  cell_run fext s (Carry4 out cout cin lhs rhs) =
  INR (cset_var (cset_var s (NetVar cout) coutv) (NetVar out) outv) ∧
  rtltype_v coutv (CArray_t 4) ∧
  rtltype_v outv (CArray_t 4) ∧
  populated_by_regs regs (cset_var (cset_var s (NetVar cout) coutv) (NetVar out) outv) ∧
  seen_present (cell_outputs_with_types seen (Carry4 out cout cin lhs rhs)) (cset_var (cset_var s (NetVar cout) coutv) (NetVar out) outv)
Proof
 rw [cell_run_def] \\
 drule_strip validate_techmapped_cell_input_cell_inp_run \\
 qspec_then ‘lhs’ assume_tac validate_techmapped_cell_input_sum_mapM_cell_inp_run \\ drule_first \\
 drule_strip EVERY_rtltype_v_CBool_t_sum_mapM_get_bool \\
 qspec_then ‘rhs’ assume_tac validate_techmapped_cell_input_sum_mapM_cell_inp_run \\ drule_first \\
 drule_strip EVERY_rtltype_v_CBool_t_sum_mapM_get_bool \\
 imp_res_tac length_sum_mapM \\
 reverse (Cases_on ‘v’) >- fs [rtltype_v_cases] \\
 
 simp [sum_bind_def, cellCarry4_run_def, get_bool_def] \\ every_case_tac \\ fs [] \\
 simp [sum_bind_def, cell_outputs_with_types_def, populated_by_regs_cset_var_NetVar] \\

 qmatch_goalsub_abbrev_tac ‘cset_var s (NetVar cout) coutv’ \\
 qmatch_goalsub_abbrev_tac ‘cset_var _ (NetVar out) outv’ \\
 Q.LIST_EXISTS_TAC [‘outv’, ‘coutv’] \\
 unabbrev_all_tac \\
 simp [rtltype_v_cases, seen_present_cset_var]
QED

Theorem validate_techmapped_netlist_itr_cells_run:
 ∀nl extenv regs regs_map seen fext s.
 validate_techmapped_netlist_itr extenv regs_map seen nl ∧
 populated_by_regs regs s ∧ regs_map_inv regs regs_map ∧
 rtltype_extenv_n extenv fext ∧
 seen_present seen s ⇒
 deterministic_netlist nl ∧
 ∃s'. sum_foldM (cell_run fext) s nl = INR s'
Proof
 Induct >- simp [sum_foldM_def, deterministic_netlist_def] \\
 Cases \\ fs [sum_foldM_INR, validate_techmapped_netlist_itr_def, validate_techmapped_cell_def] \\ rpt strip_tac'

 >- (* CellLUT *)
 (drule_strip validate_techmapped_cell_run_CellLUT \\ first_x_assum (qspecl_then [‘n’, ‘l0’] strip_assume_tac) \\
 drule_first \\ fs [deterministic_netlist_def, deterministic_cell_def])

 >- (* Carry4 *)
 (drule validate_techmapped_cell_run_Carry4 \\ disch_then (qspecl_then [‘l’, ‘l0’] assume_tac) \\
  drule_first \\ first_x_assum (qspecl_then [‘n’, ‘n0’] strip_assume_tac) \\
  drule_first \\ fs [deterministic_netlist_def, deterministic_cell_def])
QED

Theorem validate_techmapped_netlist_cells_run:
 ∀nl extenv regs fext s.
 validate_techmapped_netlist extenv regs nl ∧
 populated_by_regs regs s ∧
 rtltype_extenv_n extenv fext ⇒
 deterministic_netlist nl ∧
 ∃s'. sum_foldM (cell_run fext) s nl = INR s'
Proof
 simp [validate_techmapped_netlist_def] \\ rpt strip_tac' \\
 drule_strip validate_techmapped_netlist_itr_cells_run \\
 disch_then (qspec_then ‘fext’ mp_tac) \\
 simp [seen_present_def, sptreeTheory.lookup_def, regs_map_inv_init]
QED

Definition reg_inp_rel_def:
  reg_inp_rel extenv regs nl1 nl2 (_, _, _, _, inp) =
  OPTION_ALL (λinp. ∀fext st st1 st2.
                    rtltype_extenv_n extenv fext ∧ populated_by_regs_only regs st ∧
                    sum_foldM (cell_run fext) st nl1 = INR st1 ∧ sum_foldM (cell_run fext) st nl2 = INR st2 ⇒
                    cell_inp_run fext st1 inp = cell_inp_run fext st2 inp) inp
End

Theorem reg_inp_rel_trivial:
 (∀extenv regs nl1 nl2 r0 r1 r2 r3.
   reg_inp_rel extenv regs nl1 nl2 (r0,r1,r2,r3,NONE)) ∧
 (∀extenv regs nl1 nl2 r0 r1 r2 r3 v.
   reg_inp_rel extenv regs nl1 nl2 (r0,r1,r2,r3,SOME (ConstInp v))) ∧
 (∀extenv regs nl1 nl2 r0 r1 r2 r3 var idx.
   reg_inp_rel extenv regs nl1 nl2 (r0,r1,r2,r3,SOME (ExtInp var idx))) ∧
 (∀extenv regs nl1 nl2 r0 r1 r2 r3 reg i idx.
   reg_inp_rel extenv regs nl1 nl2 (r0,r1,r2,r3,SOME (VarInp (RegVar reg i) idx)))
Proof
 rw [reg_inp_rel_def, cell_inp_run_def] \\ imp_res_tac cells_run_cget_var_RegVar \\ simp []
QED

Theorem populated_by_regs_only_is_initial_state_with_regs:
 ∀regs st. populated_by_regs_only regs st ⇒ is_initial_state_with_regs regs st
Proof
 Induct \\ TRY PairCases \\
 fs [populated_by_regs_only_def, reg_in_regs_def, is_initial_state_with_regs_def, populated_by_regs_def] \\
 metis_tac []
QED

Theorem cell_inp_rel_reg_inp_rel:
 ∀extenv regs nl1 nl2 r0 r1 r2 r3 inp.
  (∀fext st. cell_inp_rel regs extenv fext st nl1 nl2 inp) ⇒
  reg_inp_rel extenv regs nl1 nl2 (r0,r1,r2,r3,SOME inp)
Proof
 rw [cell_inp_rel_def, reg_inp_rel_def] \\ metis_tac [populated_by_regs_only_is_initial_state_with_regs]
QED

Theorem regs_run_cong:
 !regs regs' extenv fext s_reg st st1 st2 nl1 nl2.
 EVERY (reg_inp_rel extenv regs' nl1 nl2) regs /\
 (∀reg. MEM reg regs ⇒ MEM reg regs') ∧
 rtltype_extenv_n extenv fext ∧
 populated_by_regs_only regs' st ∧
 sum_foldM (cell_run fext) st nl1 = INR st1 /\
 sum_foldM (cell_run fext) st nl2 = INR st2 ⇒
 sum_foldM (reg_run fext st2) s_reg regs = sum_foldM (reg_run fext st1) s_reg regs
Proof
 Induct \\ TRY PairCases \\ dsimp [sum_foldM_def, sum_bind_INR] \\ rpt strip_tac \\
 drule_first \\ fs [reg_run_def] \\ rpt TOP_CASE_TAC \\ fs [reg_inp_rel_def] \\ drule_first \\ fs []
QED

Theorem netlist_run_cong:
 ∀n nl1 nl2 regs extenv fext s.
 EVERY (λ(t, _, _, _, _). t = CBool_t) regs ∧
 EVERY (reg_inp_rel extenv regs nl1 nl2) regs ∧
 validate_techmapped_netlist extenv regs nl2 ∧
 rtltype_extenv extenv fext ∧
 populated_by_regs_only regs s ∧
 blast_regs_distinct regs ∧
 deterministic_netlist nl1 ∧
 (∀s n. populated_by_regs_only regs s ⇒ ISR (sum_foldM (cell_run (fext n)) s nl1)) ⇒
 netlist_run fext s nl1 regs n = netlist_run fext s nl2 regs n
Proof
 Induct \\ rw [netlist_run_def] \\
 drule_last \\ simp [] \\ Cases_on ‘netlist_run fext s nl2 regs n’ \\ simp [sum_bind_def] \\
 simp [netlist_step_def] \\

 drule_strip rtltype_extenv_rtltype_extenv_n \\ first_x_assum (qspec_then ‘n’ assume_tac) \\
 drule_strip netlist_run_populated_by_regs_only \\

 drule_first \\ fs [ISR_exists] \\ first_x_assum (qspec_then ‘n’ strip_assume_tac) \\
 drule_strip populated_by_regs_only_populated_by_regs \\
 drule_strip validate_techmapped_netlist_cells_run \\

 simp [sum_bind_def] \\

 drule_strip regs_run_cong \\ simp [] \\ disch_then drule_strip \\ simp [] \\
 Cases_on ‘sum_foldM (reg_run (fext n) x') y regs’ \\ simp [sum_bind_def] \\
 imp_res_tac run_cells_deterministic_netlist \\ simp []
QED

Theorem circut_run_cong:
 ∀nl1 nl2 regs extenv.
 EVERY (λ(t, _, _, _, _). t = CBool_t) regs ⇒ (* <-- can be proved in earlier passes *)
 EVERY (reg_inp_rel extenv regs nl1 nl2) regs ⇒
 validate_techmapped_netlist extenv regs nl2 ⇒
 ∀n fext fbits.
 blast_regs_distinct regs ∧ deterministic_netlist nl1 ∧
 (∀s n. populated_by_regs_only regs s ⇒ ISR (sum_foldM (cell_run (fext n)) s nl1)) ∧
 rtltype_extenv extenv fext ⇒
 circuit_run fext fbits (Circuit extenv regs nl2) n = circuit_run fext fbits (Circuit extenv regs nl1) n
Proof
 rw [circuit_run_def] \\ Cases_on ‘init_run <|env := []; fbits := fbits|> regs’ \\ simp [sum_bind_def] \\
 drule_strip init_run_populated_by_regs_only \\ impl_tac >- simp [cget_var_def] \\ strip_tac \\
 drule_strip netlist_run_cong \\ simp []
QED

Definition only_regs_def:
 only_regs s (regs : regty list) ⇔
  ∀reg i v. cget_var s (RegVar reg i) = INR v ⇒ MEM (reg, i) (MAP blast_reg_name regs)
End

Theorem only_regs_fbits:
 ∀s regs fbits. only_regs (s with fbits := fbits) regs = only_regs s regs
Proof
 simp [only_regs_def, cget_var_fbits]
QED

Theorem same_shape_cases:
 ∀v v'.
 same_shape v v' ⇔ (∃b b'. v = CBool b ∧ v' = CBool b') ∨
                   (∃bs bs'. v = CArray bs ∧ v' = CArray bs' ∧ LENGTH bs = LENGTH bs')
Proof
 Cases \\ Cases \\ simp [same_shape_def]
QED

Theorem cell_inp_run_types_cong:
 ∀inp fext s1 s2 v.
 cell_inp_run fext s1 inp = INR v ∧
 (∀var v. cget_var s1 var = INR v ⇒ ∃v'. cget_var s2 var = INR v' ∧ same_shape v v') ⇒
 ∃v'. cell_inp_run fext s2 inp = INR v' ∧ same_shape v v'
Proof
 Cases \\ simp [cell_inp_run_def, same_shape_refl] \\ rw [sum_bind_INR] \\ drule_first \\
 fs [same_shape_cases, cget_fext_var_def] \\ every_case_tac \\ fs [sum_map_INR, sum_revEL_INR] \\ rw []
QED

Theorem cell_run_types_cong_lut_lem:
 ∀ins ins' ins'' fext s1 s2.
 sum_mapM (cell_inp_run fext s1) ins = INR ins' ∧ sum_mapM get_bool ins' = INR ins'' ∧
 (∀var v. cget_var s1 var = INR v ⇒ ∃v'. cget_var s2 var = INR v' ∧ same_shape v v') ⇒
 ∃ins2' ins2''. sum_mapM (cell_inp_run fext s2) ins = INR ins2' ∧ LENGTH ins2' = LENGTH ins' ∧
                sum_mapM get_bool ins2' = INR ins2'' ∧ LENGTH ins2'' = LENGTH ins''
Proof
 Induct \\ simp [sum_mapM_INR] \\ rpt strip_tac' \\ drule_strip cell_inp_run_types_cong \\
 fs [sum_mapM_INR, get_bool_INR] \\ rveq \\ drule_first \\ fs [same_shape_inv, sum_mapM_INR, get_bool_INR]
QED

Theorem cell_run_types_cong:
 ∀cell fext s1 s1' s2.
 cell_run fext s1 cell = INR s1' ∧
 (∀var v. cget_var s1 var = INR v ⇒ ∃v'. cget_var s2 var = INR v' ∧ same_shape v v') ⇒
 ∃s2'. cell_run fext s2 cell = INR s2' ∧
       (∀var v. cget_var s1' var = INR v ⇒ ∃v'. cget_var s2' var = INR v' ∧ same_shape v v')
Proof
 Cases \\ rpt strip_tac'
 >- (rename1 ‘NDetCell out t’ \\ Cases_on ‘t’ \\
     fs [cell_run_def, ndetcell_run_def, oracle_bit_def, oracle_bits_genlist] \\
     rveq \\ rw [cset_var_fbits, cget_var_fbits, cget_var_cset_var] \\ rw [same_shape_def])
 >- (rename1 ‘Cell1 cell1 out in1’ \\ Cases_on ‘cell1’ \\
     fs [cell_run_def, sum_bind_INR] \\
     drule_strip cell_inp_run_types_cong \\ Cases_on ‘in1'’ \\ fs [same_shape_inv, cell1_run_def] \\
     rw [cget_var_cset_var] \\ rw [same_shape_def])
 >- (rename1 ‘Cell2 cell2 out in1 in2’ \\ Cases_on ‘cell2’ \\
     fs [cell_run_def, sum_bind_INR] \\
     qspec_then ‘in1’ assume_tac cell_inp_run_types_cong \\ drule_first \\
     qspec_then ‘in2’ assume_tac cell_inp_run_types_cong \\ drule_first \\
     Cases_on ‘in1'’ \\ Cases_on ‘in2'’ \\ fs [same_shape_inv, cell2_run_def, sum_check_INR, sum_bind_INR] \\
     rw [cget_var_cset_var] \\ rw [same_shape_def])
 >- (rename1 ‘CellMux out in1 in2 in3’ \\
     fs [cell_run_def, sum_bind_INR] \\
     qspec_then ‘in1’ assume_tac cell_inp_run_types_cong \\ drule_first \\
     qspec_then ‘in2’ assume_tac cell_inp_run_types_cong \\ drule_first \\
     qspec_then ‘in3’ assume_tac cell_inp_run_types_cong \\ drule_first \\
     Cases_on ‘c’ \\ Cases_on ‘in1'’ \\ Cases_on ‘in2'’ \\
     fs [same_shape_inv, cellMux_run_def, sum_check_INR, sum_bind_INR] \\
     rw [cget_var_cset_var] \\ rw [same_shape_def])
 >- (rename1 ‘CellArrayWrite out in1 idx in2’ \\
     fs [cell_run_def, sum_bind_INR] \\
     qspec_then ‘in1’ assume_tac cell_inp_run_types_cong \\ drule_first \\
     qspec_then ‘in2’ assume_tac cell_inp_run_types_cong \\ drule_first \\
     Cases_on ‘in1'’ \\ Cases_on ‘in2'’ \\
     fs [same_shape_inv, cellArrayWrite_run_def] \\
     rw [cget_var_cset_var] \\ rw [same_shape_def])
 >- (rename1 ‘CellLUT out ins tb’ \\
     fs [cell_run_def, cellLUT_run_def, sum_bind_INR] \\
     drule_strip cell_run_types_cong_lut_lem \\ simp [] \\
     rw [cget_var_cset_var] \\ rw [same_shape_def])
 >- (rename1 ‘Carry4 out cout cin lhs rhs’ \\
     fs [cell_run_def, cellCarry4_run_def, sum_bind_INR] \\ every_case_tac \\ fs [] \\ rveq \\ fs [] \\ rveq \\
     drule_strip cell_inp_run_types_cong \\
     qspec_then ‘lhs’ assume_tac cell_run_types_cong_lut_lem \\ drule_first \\
     qspec_then ‘rhs’ assume_tac cell_run_types_cong_lut_lem \\ drule_first \\
     fs [LENGTH_EQ_NUM_compute, get_bool_INR] \\ rveq \\ fs [same_shape_inv] \\
     rw [cget_var_cset_var] \\ rw [same_shape_def])
QED

Theorem cells_run_types_cong:
 ∀nl fext s1 s1' s2.
 sum_foldM (cell_run fext) s1 nl = INR s1' ∧
 (∀var v. cget_var s1 var = INR v ⇒ ∃v'. cget_var s2 var = INR v' ∧ same_shape v v') ⇒
 ∃s2'. sum_foldM (cell_run fext) s2 nl = INR s2' ∧
       (∀var v. cget_var s1' var = INR v ⇒ ∃v'. cget_var s2' var = INR v' ∧ same_shape v v')
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_INR] \\ drule_strip cell_run_types_cong \\ simp [] \\ drule_first \\ simp []
QED

Theorem cells_run_populated_by_regs_only:
 ∀nl fext s1 s1' s2 (regs : regty list).
 sum_foldM (cell_run fext) s1 nl = INR s1' ∧
 only_regs s1 regs ∧
 populated_by_regs_only regs s1 ∧
 populated_by_regs_only regs s2 ⇒
 ∃s2'. sum_foldM (cell_run fext) s2 nl = INR s2'
Proof
 rpt strip_tac \\ drule_strip cells_run_types_cong \\ disch_then (qspec_then ‘s2’ mp_tac) \\
 impl_tac >- (Cases \\ fs [populated_by_regs_only_def, populated_by_regs_def, only_regs_def] \\
              rpt strip_tac \\ drule_first \\ fs [EVERY_MEM, MEM_MAP] \\ rpt drule_first \\
              PairCases_on ‘y’ \\ fs [blast_reg_name_def] \\ fs [] \\ rveq \\ match_mp_tac rtltype_v_same_shape \\
              rpt asm_exists_tac \\ simp [rtltype_v_cases]) \\
 strip_tac \\ simp []
QED

Theorem init_run_only_regs:
 ∀regs' regs s s'.
 init_run s regs = INR s' ∧ (∀r. MEM r regs ⇒ MEM r regs') ∧ only_regs s regs' ⇒ only_regs s' regs'
Proof
 gen_tac \\ Induct \\ TRY PairCases \\ simp [init_run_def] \\ rpt gen_tac \\ every_case_tac
 >- (pairarg_tac \\ drule_strip rtl_nd_value_type_correct \\ simp [] \\ strip_tac \\ drule_first \\
     impl_tac >- (fs [only_regs_def, cget_var_fbits, cget_var_cset_var] \\ rw [] \\
                  simp [MEM_MAP] \\ qexists_tac ‘(h0,h1,h2,NONE,h4)’ \\ simp [blast_reg_name_def]) \\ simp [])
 >- (strip_tac \\ drule_first \\
     impl_tac >- (fs [only_regs_def, cget_var_fbits, cget_var_cset_var] \\ rw [] \\
                  simp [MEM_MAP] \\ qexists_tac ‘(h0,h1,h2,SOME v,h4)’ \\ simp [blast_reg_name_def]) \\ simp [])
QED

Theorem cells_run_only_regs:
 ∀fext s s' nl regs.
 sum_foldM (cell_run fext) s nl = INR s' ∧ only_regs s regs ⇒ only_regs s' regs
Proof
 rpt strip_tac \\ drule_strip cells_run_cget_var_RegVar \\ fs [only_regs_def]
QED

Theorem reg_run_only_regs:
 ∀reg regs' fext s_net s s'.
 reg_run fext s_net s reg = INR s' ∧
 only_regs s regs' ∧
 MEM reg regs' ⇒
 only_regs s' regs'
Proof
 PairCases \\ rw [reg_run_def, CaseEq"option", sum_bind_INR] \\ simp [] \\
 fs [only_regs_def, cget_var_cset_var] \\ rw [] \\ simp [MEM_MAP] \\ asm_exists_any_tac \\ simp [blast_reg_name_def]
QED

Theorem regs_run_only_regs:
 ∀regs' regs fext s_net s s'.
 sum_foldM (reg_run fext s_net) s regs = INR s' ∧
 (∀r. MEM r regs ⇒ MEM r regs') ∧
 only_regs s regs' ⇒
 only_regs s' regs'
Proof
 gen_tac \\ Induct \\ simp [sum_foldM_INR] \\ rpt strip_tac \\ drule_strip reg_run_only_regs \\
 impl_tac >- simp [] \\ strip_tac \\ drule_first \\ simp []
QED

Theorem netlist_run_only_regs:
 ∀n fext s s' nl regs.
 netlist_run fext s nl regs n = INR s' ∧ only_regs s regs ⇒ only_regs s' regs
Proof
 Induct \\ simp [netlist_run_def, netlist_step_def, sum_bind_INR] \\ rpt strip_tac \\
 drule_first \\
 drule_strip cells_run_only_regs \\
 drule_strip regs_run_only_regs \\ disch_then (qspec_then ‘regs’ mp_tac) \\ simp [only_regs_fbits]
QED

Theorem populated_by_regs_only_ISR_from_circuit_run:
 ∀fext fbits extenv regs nl.
 (∀n. ISR (circuit_run fext fbits (Circuit extenv regs nl) n)) ∧
 EVERY (λ(t,_,_,_,_). t = CBool_t) regs ∧
 blast_regs_distinct regs ⇒
 (∀s n. populated_by_regs_only regs s ⇒ ISR (sum_foldM (cell_run (fext n)) s nl))
Proof
 rpt strip_tac \\ first_x_assum (qspec_then ‘SUC n’ strip_assume_tac) \\
 fs [circuit_run_def, netlist_run_def, netlist_step_def, ISR_exists, sum_bind_INR] \\
 drule_strip init_run_populated_by_regs_only \\ impl_tac >- simp [cget_var_def] \\ strip_tac \\
 drule_strip init_run_only_regs \\ disch_then (qspec_then ‘regs’ mp_tac) \\
 impl_tac >- simp [only_regs_def, cget_var_def] \\ strip_tac \\
 drule_strip netlist_run_populated_by_regs_only \\
 drule_strip netlist_run_only_regs \\
 match_mp_tac cells_run_populated_by_regs_only \\ rpt asm_exists_tac
QED

val _ = export_theory ();
