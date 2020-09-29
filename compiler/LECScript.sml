open hardwarePreamble;

open oracleTheory sumExtraTheory RTLTheory RTLTypeTheory RTLPropsTheory;

open RTLLib;

val _ = new_theory "LEC";
(*
(** Lifting **)

val Eval_def = Define `
 Eval fext st nl inp b <=>
 !st'. sum_foldM (cell_run fext) st nl = INR st' ==> cell_inp_run fext st' inp = INR (CBool b)`;

Theorem Eval_ConstInp:
 !b nl. Eval fext st nl (ConstInp (CBool b)) b
Proof
 rw [Eval_def, cell_inp_run_def]
QED

Theorem Eval_ExtInp_NONE:
 !var b nl. fext var = INR (CBool b) ⇒ Eval fext st nl (ExtInp var NONE) b
Proof
 rw [Eval_def, cell_inp_run_def, cget_fext_var_def, sum_bind_def]
QED

Theorem Eval_ExtInp_SOME:
 !var i b nl.
 (∃bs. fext var = INR (CArray bs) ∧ cget_fext_var (SOME i) (CArray bs) = INR (CBool b)) ⇒
 Eval fext st nl (ExtInp var (SOME i)) b
Proof
 rw [Eval_def, cell_inp_run_def] \\ rw [sum_bind_def]
QED

Theorem Eval_RegVar_CBool:
 !reg i regv nl. cget_var st (RegVar reg i) = INR (CBool regv) ==> Eval fext st nl (VarInp (RegVar reg i) NONE) regv
Proof
 rw [Eval_def, cell_inp_run_def] \\ drule_strip cells_run_cget_var_RegVar \\
 simp [sum_bind_def, cget_fext_var_def]
QED

Theorem Eval_snoc_CNot:
 !nl in1 in1b in2 in2b out.
 Eval fext st nl in1 in1b ==>
 Eval fext st (SNOC (Cell1 CNot out in1) nl) (VarInp (NetVar out) NONE) ~in1b
Proof
 rw [Eval_def, sum_foldM_SNOC, sum_bind_INR] \\ rpt drule_first \\
 fs [cell_run_def, cell1_run_def, sum_bind_def] \\
 rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def]
QED

Definition st_nl_overlap_def:
 st_nl_overlap st nl ⇔ ∀n v. cget_var st (NetVar n) = INR v ⇒ ~MEM n (FLAT (MAP cell_output nl))
End

Theorem st_nl_overlap_alt:
 ∀st nl. st_nl_overlap st nl ⇔ ∀n v. MEM n (FLAT (MAP cell_output nl)) ⇒ cget_var st (NetVar n) ≠ INR v
Proof
 metis_tac [st_nl_overlap_def]
QED

Theorem st_nl_overlap_TAKE:
 ∀st nl n. st_nl_overlap st nl ⇒ st_nl_overlap st (TAKE n nl)
Proof
 rw [st_nl_overlap_def, MAP_TAKE, MEM_FLAT] \\ drule_first \\ metis_tac [rich_listTheory.MEM_TAKE]
QED

Theorem cells_run_TAKE:
 ∀n nl st st' fext.
 sum_foldM (cell_run fext) st nl = INR st' ∧
 st_nl_overlap st nl ∧
 ALL_DISTINCT (FLAT (MAP cell_output nl)) ⇒
 ∃st''. sum_foldM (cell_run fext) st (TAKE n nl) = INR st'' ∧
        ∀var v. cget_var st'' var = INR v ⇒ cget_var st' var = INR v
Proof
 Induct >- (rw [sum_foldM_def, st_nl_overlap_def] \\
            Cases_on ‘var’ >- metis_tac [cells_run_cget_var_RegVar] \\
            drule_first \\ drule_strip cells_run_unchanged \\ simp []) \\

 rpt strip_tac' \\ Cases_on ‘LENGTH nl ≤ SUC n’ >- simp [TAKE_LENGTH_TOO_LONG] \\
 Cases_on ‘nl’ \\ fs [sum_foldM_INR, ALL_DISTINCT_APPEND] \\ drule_first \\
 impl_tac >- (fs [st_nl_overlap_alt] \\ metis_tac [cell_run_unchanged]) \\
 simp []
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
 st_nl_overlap st nl ∧
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
 drule_strip cells_run_TAKE \\ first_x_assum (qspec_then ‘n’ strip_assume_tac) \\
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
 st_nl_overlap st nl ⇒
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
 st_nl_overlap st nl ⇒
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
 st_nl_overlap st nl ⇒
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
 st_nl_overlap st nl ⇒
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
 st_nl_overlap st nl ⇒
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
 st_nl_overlap st nl ⇒
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
 st_nl_overlap st nl ⇒
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
 st_nl_overlap st nl ⇒
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
 st_nl_overlap st nl ⇒
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
 st_nl_overlap st nl ⇒
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
 st_nl_overlap st nl ⇒
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

(** Other things **)

(*Theorem Eval_snoc_distinct:
 !nl out idx b cell.
 Eval fext st nl (VarInp (NetVar out) idx) b ==>
 ~MEM out (cell_output cell) ==>
 Eval fext st (SNOC cell nl) (VarInp (NetVar out) idx) b
Proof
 rw [Eval_def, sum_foldM_SNOC, sum_bind_INR, cell_inp_run_def] \\ drule_first \\
 drule_strip cell_run_unchanged \\ simp []
QED*)

(* Simple to prove that gates have the same output when in same netlist ... *)
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
 sum_foldM (cell_run fext) st1 nl1 = INR st1' /\
 sum_foldM (cell_run fext) st2 nl2 = INR st2' ==>
 cell_inp_run fext st1' out1 = cell_inp_run fext st2' out2
Proof
 rw [Eval_def]
QED

(* Thms to lift from netlist level to circuit level *)

Definition populated_by_regs_def:
 populated_by_regs regs st ⇔
 EVERY (λ(t, reg, i, _, _). ∃v. cget_var st (RegVar reg i) = INR v ∧ rtltype_v v t) regs
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

Theorem cleanup_populated_by_regs_only_st_nl_overlap:
 ∀regs nl. populated_by_regs_only regs st ⇒ st_nl_overlap st nl
Proof
 rw [populated_by_regs_only_def, st_nl_overlap_def]
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
 init_run s regs = INR s' ∧ blast_regs_distinct regs ∧ (∀n. cget_var s (NetVar n) = INL UnknownVariable) ⇒
 populated_by_regs_only regs s'
Proof
 Induct \\ TRY PairCases \\ fs [init_run_def, blast_regs_distinct_def, populated_by_regs_only_def, populated_by_regs_def] \\
 rpt gen_tac \\ TOP_CASE_TAC
 >- (pairarg_tac \\ drule_strip rtl_nd_value_type_correct \\ simp [blast_reg_name_def] \\ strip_tac \\
    drule_first \\ simp [] \\ drule_strip init_run_unchanged \\
    fs [cset_var_fbits, cget_var_fbits, cget_var_cset_var])
 \\ IF_CASES_TAC \\ simp [blast_reg_name_def] \\ strip_tac \\ drule_first \\ simp [] \\
    drule_strip init_run_unchanged \\ fs [cget_var_cset_var, has_rtltype_v_correct]
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
 fs [cget_var_cset_var, has_rtltype_v_correct]
QED

Theorem netlist_step_populated_by_regs_only:
 ∀fext regs nl s s'.
 netlist_step fext s nl regs = INR s' ∧ blast_regs_distinct regs ∧ populated_by_regs_only regs s ⇒
 populated_by_regs_only regs s'
Proof
 rw [netlist_step_def, sum_bind_INR] \\
 drule_strip regs_run_populated_by_regs_only \\
 simp [populated_by_regs_only_fbits]
QED

Theorem netlist_run_populated_by_regs_only:
 ∀n fext regs nl s s'.
 netlist_run fext s nl regs n = INR s' ∧ blast_regs_distinct regs ∧ populated_by_regs_only regs s ⇒
 populated_by_regs_only regs s'
Proof
 Induct \\ simp [netlist_run_def, sum_bind_INR] \\ rpt strip_tac \\ drule_first \\
 drule_strip netlist_step_populated_by_regs_only
QED

Definition cell_outputs_with_types_def:
 (cell_outputs_with_types (CellLUT out ins tb) = [(out, CBool_t)]) ∧
 (cell_outputs_with_types (Carry4 out cout cin lhs rhs) = [(out, CArray_t 4); (cout, CArray_t 4)]) ∧
 (cell_outputs_with_types _ = [])
End

Definition validate_techmapped_cell_input_type_def:
 validate_techmapped_cell_input_type t idx =
  case (t, idx) of
    (SOME CBool_t, NONE) => T
  | (SOME (CArray_t len), SOME i) => i < len
  | _ => F
End

Definition lookup_reg_type_def:
 (lookup_reg_type [] (reg, i) = NONE) ∧
 (lookup_reg_type ((ty,reg,i,v,src) :: t) (reg', i') =
  if reg' = reg ∧ i' = i then SOME ty else lookup_reg_type t (reg', i'))
End

Theorem lookup_reg_type_alookup_map:
 ∀k regs.
 lookup_reg_type regs k = ALOOKUP (MAP (λ(ty,reg,i,v,src). ((reg,i),ty)) regs) k
Proof
 PairCases \\ Induct \\ TRY PairCases \\ rw [lookup_reg_type_def]
QED

Definition validate_techmapped_cell_input_def:
 (validate_techmapped_cell_input extenv regs seen (ConstInp (CBool _)) ⇔ T) ∧
 (validate_techmapped_cell_input extenv regs seen (ConstInp (CArray _)) ⇔ F) ∧
  
 (validate_techmapped_cell_input extenv regs seen (ExtInp var idx) ⇔
  validate_techmapped_cell_input_type (ALOOKUP extenv var) idx) ∧

 (validate_techmapped_cell_input extenv regs seen (VarInp (NetVar n) idx) ⇔
  validate_techmapped_cell_input_type (ALOOKUP seen n) idx) ∧
 (validate_techmapped_cell_input extenv regs seen (VarInp (RegVar reg i) idx) ⇔
  validate_techmapped_cell_input_type (lookup_reg_type regs (reg, i)) idx)
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

Definition validate_techmapped_netlist_def:
 (validate_techmapped_netlist extenv regs seen [] = T) ∧
 (validate_techmapped_netlist extenv regs seen (c::cs) ⇔
  validate_techmapped_cell extenv regs seen c ∧
  validate_techmapped_netlist extenv regs (cell_outputs_with_types c ++ seen) cs)
End

Definition seen_present_def:
 seen_present seen s ⇔ ∀t n. ALOOKUP seen n = SOME t ⇒ ∃v. cget_var s (NetVar n) = INR v ∧ rtltype_v v t
End

Theorem populated_by_regs_lookup_reg_type:
 ∀regs s reg i t.
 populated_by_regs regs s ∧ lookup_reg_type regs (reg, i) = SOME t ⇒
 ∃v. cget_var s (RegVar reg i) = INR v ∧ rtltype_v v t
Proof
 rw [populated_by_regs_def, lookup_reg_type_alookup_map, EVERY_MEM] \\
 drule_strip alistTheory.ALOOKUP_MEM \\ fs [MEM_MAP] \\ drule_first \\ pairarg_tac \\ fs []
QED

Theorem validate_techmapped_cell_input_cell_inp_run:
 ∀inp extenv regs seen fext s.
 validate_techmapped_cell_input extenv regs seen inp ∧
 populated_by_regs regs s ∧ rtltype_extenv_n extenv fext ∧ seen_present seen s ⇒
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
  >- (every_case_tac \\ fs [] \\ drule_strip populated_by_regs_lookup_reg_type \\
      fs [sum_bind_def, sum_map_def, cget_fext_var_def, rtltype_v_cases, sum_revEL_revEL])
  >- (every_case_tac \\ fs [seen_present_def] \\ drule_first \\
      fs [sum_bind_def, sum_map_def, cget_fext_var_def, rtltype_v_cases, sum_revEL_revEL]))
QED

Theorem validate_techmapped_cell_input_sum_mapM_cell_inp_run:
 ∀ins extenv regs seen s fext.
 EVERY (validate_techmapped_cell_input extenv regs seen) ins ∧
 populated_by_regs regs s ∧
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
 seen_present seen s ∧ rtltype_v v t ⇒ seen_present ((out, t) :: seen) (cset_var s (NetVar out) v)
Proof
 rw [seen_present_def, cget_var_cset_var] \\ rw [] \\ fs []
QED

Theorem validate_techmapped_cell_run_CellLUT:
 ∀out ins tb extenv regs seen fext s.
 EVERY (validate_techmapped_cell_input extenv regs seen) ins ∧
 populated_by_regs regs s ∧
 rtltype_extenv_n extenv fext ∧
 seen_present seen s ⇒
 ∃res. cell_run fext s (CellLUT out ins tb) = INR (cset_var s (NetVar out) res) ∧ rtltype_v res CBool_t ∧
       populated_by_regs regs (cset_var s (NetVar out) res) ∧
       seen_present (cell_outputs_with_types (CellLUT out ins tb) ++ seen) (cset_var s (NetVar out) res)
Proof
 rw [cell_run_def, cellLUT_run_def] \\
 drule_strip validate_techmapped_cell_input_sum_mapM_cell_inp_run \\
 drule_strip EVERY_rtltype_v_CBool_t_sum_mapM_get_bool \\
 simp [sum_bind_def, cell_outputs_with_types_def, populated_by_regs_cset_var_NetVar] \\
 metis_tac [rtltype_v_cases, seen_present_cset_var]
QED

Theorem validate_techmapped_cell_run_Carry4:
 ∀lhs rhs out cout cin extenv regs seen fext s.
 validate_techmapped_cell_input extenv regs seen cin ∧
 EVERY (validate_techmapped_cell_input extenv regs seen) lhs ∧ LENGTH lhs = 4 ∧
 EVERY (validate_techmapped_cell_input extenv regs seen) rhs ∧ LENGTH rhs = 4 ∧
 populated_by_regs regs s ∧
 rtltype_extenv_n extenv fext ∧
 seen_present seen s ⇒
 ∃outv coutv.
  cell_run fext s (Carry4 out cout cin lhs rhs) =
  INR (cset_var (cset_var s (NetVar cout) coutv) (NetVar out) outv) ∧
  rtltype_v coutv (CArray_t 4) ∧
  rtltype_v outv (CArray_t 4) ∧
  populated_by_regs regs (cset_var (cset_var s (NetVar cout) coutv) (NetVar out) outv) ∧
  seen_present (cell_outputs_with_types (Carry4 out cout cin lhs rhs) ++ seen) (cset_var (cset_var s (NetVar cout) coutv) (NetVar out) outv)
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

Theorem validate_techmapped_netlist_cells_run:
 ∀nl extenv regs seen fext s.
 validate_techmapped_netlist extenv regs seen nl ∧
 populated_by_regs regs s ∧
 rtltype_extenv_n extenv fext ∧
 seen_present seen s ⇒
 deterministic_netlist nl ∧
 ∃s'. sum_foldM (cell_run fext) s nl = INR s'
Proof
 Induct >- simp [sum_foldM_def, deterministic_netlist_def] \\
 Cases \\ fs [sum_foldM_INR, validate_techmapped_netlist_def, validate_techmapped_cell_def] \\ rpt strip_tac'

 >- (* CellLUT *)
 (drule_strip validate_techmapped_cell_run_CellLUT \\ first_x_assum (qspecl_then [‘n’, ‘l0’] strip_assume_tac) \\
 drule_first \\ fs [deterministic_netlist_def, deterministic_cell_def])

 >- (* Carry4 *)
 (drule validate_techmapped_cell_run_Carry4 \\ disch_then (qspecl_then [‘l’, ‘l0’] assume_tac) \\
  drule_first \\ first_x_assum (qspecl_then [‘n’, ‘n0’] strip_assume_tac) \\
  drule_first \\ fs [deterministic_netlist_def, deterministic_cell_def])
QED

Definition reg_inp_rel_def:
  reg_inp_rel extenv regs nl1 nl2 (_, _, _, _, inp) =
  OPTION_ALL (λinp. ∀fext st st1 st2.
                    rtltype_extenv_n extenv fext ∧ populated_by_regs_only regs st ∧
                    sum_foldM (cell_run fext) st nl1 = INR st1 ∧ sum_foldM (cell_run fext) st nl2 = INR st2 ⇒
                    cell_inp_run fext st1 inp = cell_inp_run fext st2 inp) inp
End

Theorem reg_inp_rel_trivial:
 (∀extenv regs nl1 nl2 r0 r1 r2 r3. reg_inp_rel extenv regs nl1 nl2 (r0,r1,r2,r3,NONE)) ∧
 (∀extenv regs nl1 nl2 r0 r1 r2 r3 v. reg_inp_rel extenv regs nl1 nl2 (r0,r1,r2,r3,SOME (ConstInp v))) ∧
 (∀extenv regs nl1 nl2 r0 r1 r2 r3 var idx. reg_inp_rel extenv regs nl1 nl2 (r0,r1,r2,r3,SOME (ExtInp var idx))) ∧
 (∀extenv regs nl1 nl2 r0 r1 r2 r3 reg i idx. reg_inp_rel extenv regs nl1 nl2 (r0,r1,r2,r3,SOME (VarInp (RegVar reg i) idx)))
Proof
 rw [reg_inp_rel_def, cell_inp_run_def] \\ imp_res_tac cells_run_cget_var_RegVar \\ simp []
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
 EVERY (reg_inp_rel extenv regs nl1 nl2) regs ∧
 validate_techmapped_netlist extenv regs [] nl2 ∧
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
 drule_strip validate_techmapped_netlist_cells_run \\ impl_tac >- simp [seen_present_def] \\ strip_tac \\

 simp [sum_bind_def] \\

 drule_strip regs_run_cong \\ simp [] \\ disch_then drule_strip \\ simp [] \\
 Cases_on ‘sum_foldM (reg_run (fext n) x') y regs’ \\ simp [sum_bind_def] \\
 imp_res_tac run_cells_deterministic_netlist \\ simp []
QED

Theorem circut_run_cong:
 ∀nl1 nl2 regs extenv.
 EVERY (reg_inp_rel extenv regs nl1 nl2) regs ⇒
 validate_techmapped_netlist extenv regs [] nl2 ⇒
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
              rpt asm_exists_tac) \\ strip_tac \\ simp []
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
*)
val _ = export_theory ();
