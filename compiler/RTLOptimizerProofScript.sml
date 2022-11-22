open hardwarePreamble;

open alistTheory wordsTheory;
open dep_rewrite wordsLib;

open sumExtraTheory verilogTheory verilogTypeTheory verilogMetaTheory;
open RTLTheory RTLTypeTheory RTLPropsTheory;

open comparisonTheory balanced_mapTheory;

open RTLBlasterProofTheory; (* <-- move blasted_circuit *)

open RTLOptimizerTheory;

val _ = new_theory "RTLOptimizerProof";

infix THEN2;
infix THEN3;

Definition opt_rel_regs_def:
 opt_rel_regs (m:optm_t) s opts ⇔
  opts.fbits = s.fbits ∧
  (∀n v. cget_var opts (NetVar n) = INR v ⇒ cget_var s (NetVar n) = INR v) ∧
  (∀reg i. cget_var opts (RegVar reg i) = cget_var s (RegVar reg i)) ∧
  (∀n. cget_var s (NetVar n) = INL UnknownVariable ⇒ cget_var opts (NetVar n) = INL UnknownVariable) ∧
  invariant num_cmp m ∧
  (∀n. case lookup num_cmp n m of
       | NONE => cget_var opts (NetVar n) = cget_var s (NetVar n)
       | _ => T)
End

Definition opt_rel_def:
 opt_rel fext (m:optm_t) s opts ⇔
  opt_rel_regs m s opts ∧
  (∀n. case lookup num_cmp n m of
       | NONE => cget_var opts (NetVar n) = cget_var s (NetVar n)
       | SOME inp => ∃b. cget_var s (NetVar n) = INR (CBool b) ∧ cell_inp_run fext opts inp = INR (CBool b))
End

Definition outs_not_in_env_def:
 outs_not_in_env nl s ⇔ ∀out. MEM out (FLAT $ MAP cell_output nl) ⇒ cget_var s (NetVar out) = INL UnknownVariable
End

Triviality only_regs_outs_not_in_env:
 ∀s nl. only_regs s ⇒ outs_not_in_env nl s
Proof
 rw [only_regs_def, outs_not_in_env_def]
QED

(*
Actually, cannot prove this because we don't have enough type-information here,
e.g. Cell1's might be array not... could abort if see such cell with constant input,
but let's ignore for now and wait for better netlist representation with static types.

Definition is_ConstInp_def:
 (is_ConstInp (ConstInp _) = T) ∧
 (is_ConstInp (ExtInp _ _) = F) ∧
 (is_ConstInp (VarInp _ _) = F)
End

(* only relevant for gol cells *)
Definition cell_has_no_ConstInp_def:
 (cell_has_no_ConstInp (Cell1 t out inp1) ⇔ ~is_ConstInp inp1) ∧
 (cell_has_no_ConstInp (Cell2 t out inp1 inp2) ⇔ ~is_ConstInp inp2 ∧ ~is_ConstInp inp1) ∧
 (* overapproximate the rest *)
 (cell_has_no_ConstInp _ ⇔ T)
End

(* only checks cells! *)
Definition circuit_has_no_ConstInp_def:
 circuit_has_no_ConstInp (Circuit _ _ _ nl1 nl2) ⇔
 EVERY cell_has_no_ConstInp nl1 ∧ EVERY cell_has_no_ConstInp nl2
End
*)

Triviality opt_rel_regs_sym:
 ∀s. opt_rel_regs empty s s
Proof
 simp [opt_rel_regs_def, invariant_def, empty_def] \\ gen_tac \\ CASE_TAC
QED

Triviality opt_rel_opt_rel_regs:
 ∀fext s opts. opt_rel fext empty s opts ⇔ opt_rel_regs empty s opts
Proof
 rw [opt_rel_regs_def, opt_rel_def] \\ eq_tac \\ rw [empty_def, lookup_def, invariant_def]
QED

Triviality opt_rel_regs_cset_var:
 opt_rel_regs m s1 s2 ⇒
 opt_rel_regs m (cset_var s1 (RegVar reg i) v) (cset_var s2 (RegVar reg i) v)
Proof
 rw [opt_rel_regs_def, cget_var_cset_var]
QED

Triviality opt_rel_cset_var:
 ∀fext m s1 s2 n v.
 opt_rel fext m s1 s2 ∧
 cget_var s1 (NetVar n) = INL UnknownVariable ⇒
 opt_rel fext m (cset_var s1 (NetVar n) v) (cset_var s2 (NetVar n) v)
Proof
 rw [opt_rel_def]
 >- (fs [opt_rel_regs_def, cget_var_cset_var] \\ rw [] \\ CASE_TAC)
 >- (CASE_TAC \\ rw [cget_var_cset_var]
     >- (last_x_assum (qspec_then ‘n'’ assume_tac) \\ gs [])
     >- (last_x_assum (qspec_then ‘n’ assume_tac) \\ gs [])
     >- (last_x_assum (qspec_then ‘n'’ assume_tac) \\ gs [] \\
         fs [opt_rel_regs_def] \\ drule_first \\
         rename1 ‘cell_inp_run _ _ inp’ \\ Cases_on ‘inp’ \\
         fs [cell_inp_run_def, cget_var_cset_var] \\
         rw [] \\ fs [sum_bind_def]))
QED

val lookup_insert_num_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) lookup_insert) num_cmp_good
 |> REWRITE_RULE [num_cmp_antisym];

val insert_thm_num_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) (SPEC_ALL insert_thm)) num_cmp_good;

Triviality opt_rel_cset_var_insert_inp:
 ∀inp fext m s1 s2 n b.
 opt_rel fext m s1 s2 ∧
 cell_inp_run fext s2 inp = INR (CBool b) ∧
 cget_var s1 (NetVar n) = INL UnknownVariable ⇒
 opt_rel fext (insert num_cmp n inp m) (cset_var s1 (NetVar n) (CBool b)) s2
Proof
 rw [opt_rel_def, opt_rel_regs_def]
 THEN3 (fs [cget_var_cset_var] \\ every_case_tac \\ gvs [])
 >- simp [insert_thm_num_cmp]
 THEN2 (rw [lookup_insert_num_cmp] \\ simp [cget_var_cset_var, cell_inp_run_def])
QED

Triviality opt_rel_cset_var_insert:
 ∀fext m s1 s2 n b.
 opt_rel fext m s1 s2 ∧
 cget_var s1 (NetVar n) = INL UnknownVariable ⇒
 opt_rel fext (insert num_cmp n (ConstInp (CBool b)) m) (cset_var s1 (NetVar n) (CBool b)) s2
Proof
 metis_tac [opt_rel_cset_var_insert_inp, cell_inp_run_def]
QED

Triviality opt_cell_input_correct:
 ∀inp m s1 s2 v fext.
 cell_inp_run fext s1 inp = INR v ∧
 opt_rel fext m s1 s2 ⇒
 cell_inp_run fext s2 (opt_cell_input m inp) = INR v
Proof
 Cases \\ simp [opt_cell_input_def] THEN2 (simp [cell_inp_run_def]) \\ rpt strip_tac \\
 rename1 ‘VarInp var idx’ \\ Cases_on ‘var’ \\ fs [opt_cell_input_def, opt_rel_def]
 >- fs [opt_rel_regs_def, cell_inp_run_def] \\
 last_x_assum (qspec_then ‘n’ assume_tac) \\ CASE_TAC \\
 gvs [cell_inp_run_def, sum_bind_INR] \\
 Cases_on ‘idx’ \\ fs [cget_fext_var_def]
QED

Triviality sum_mapM_opt_cell_input_correct:
 ∀inps m s1 s2 v fext.
 sum_mapM (cell_inp_run fext s1) inps = INR v ∧
 opt_rel fext m s1 s2 ⇒
 sum_mapM (cell_inp_run fext s2) (MAP (opt_cell_input m) inps) = INR v
Proof
 Induct \\ simp [sum_mapM_INR] \\ metis_tac [opt_cell_input_correct]
QED

Triviality bool_of_cell_input_correct:
 ∀inp fext s v b.
 bool_of_cell_input inp = SOME b ∧ cell_inp_run fext s inp = INR v ⇒
 v = CBool b
Proof
 Cases \\ TRY (Cases_on ‘v’) \\ rw [cell_inp_run_def, bool_of_cell_input_def]
QED

Triviality opt_cell2_1_correct:
 ∀t inp1 inp2 b v v' fext s sopt m m' cellopt out.
 opt_cell2_1 m t out b inp2 = (m', cellopt) ∧
 cell2_run t (CBool b) v' = INR v ∧
 cell_inp_run fext sopt inp1 = INR (CBool b) ∧
 cell_inp_run fext sopt inp2 = INR v' ∧
 gol_cell (Cell2 t out inp1 inp2) ∧
 opt_rel fext m s sopt ∧
 cget_var s (NetVar out) = INL UnknownVariable ⇒
 (case cellopt of
 | NONE => opt_rel fext m' (cset_var s (NetVar out) v) sopt
 | SOME cellopt => ∃sopt'. cell_run fext sopt cellopt = INR sopt' ∧
                           opt_rel fext m' (cset_var s (NetVar out) v) sopt') ∧
 OPTION_ALL gol_cell cellopt
Proof
 Cases \\ rw [opt_cell2_1_def, gol_cell_def] \\
 Cases_on ‘v'’ \\ gvs [cell2_run_def] \\
 TRY (match_mp_tac opt_rel_cset_var_insert_inp \\ simp [cell_inp_run_def]) \\
 simp [cell_run_def, cell1_run_def, sum_bind_def, gol_cell_def] \\
 match_mp_tac opt_rel_cset_var \\ simp []
QED

Triviality cell2_run_comm:
 ∀t v1 v2. cell2_run t v1 v2 = cell2_run t v2 v1
Proof
 rpt Cases \\ rw [cell2_run_def] \\ simp [EQ_SYM_EQ] \\
 rw [sum_check_def, sum_bind_def] \\ metis_tac []
QED

Triviality gol_cell_Cell2_new_inps:
 ∀t. gol_cell (Cell2 t out inp1 inp2) ⇔ gol_cell (Cell2 t out inp1' inp2')
Proof
 Cases \\ rw [gol_cell_def]
QED

Triviality opt_circuit_run_cell:
 ∀cell cellopt m m' s1 s1' s2 fext.
 opt_cell m cell = (m', cellopt) ∧
 cell_run fext s1 cell = INR s1' ∧
 opt_rel fext m s1 s2 ∧
 (∀out. MEM out (cell_output cell) ⇒ cget_var s1 (NetVar out) = INL UnknownVariable) ∧
 gol_cell cell ⇒
 (case cellopt of
  | NONE => opt_rel fext m' s1' s2
  | SOME cellopt => ∃s2'. cell_run fext s2 cellopt = INR s2' ∧
                          opt_rel fext m' s1' s2') ∧
 OPTION_ALL gol_cell cellopt
Proof
 Cases \\ TRY (simp [gol_cell_def] \\ NO_TAC) \\ rpt strip_tac'

 (* Cell1 *)
 >- (rename1 ‘Cell1 t _ _’ \\ Cases_on ‘t’ \\
     fs [cell_output_def, cell_run_def, cell1_run_def, sum_bind_INR, opt_cell_def] \\

     drule_strip opt_cell_input_correct \\

     every_case_tac \\ gvs [] \\ simp [cell_run_def, gol_cell_def]
     >- (drule_strip bool_of_cell_input_correct \\
         gvs [cell1_run_def] \\
         match_mp_tac opt_rel_cset_var_insert \\ simp [])
     >- (simp [sum_bind_def] \\
         match_mp_tac opt_rel_cset_var \\ simp []))

 (* Cell2 *)
 >- (rename1 ‘Cell2 t out inp1 inp2’ \\
     fs [cell_output_def, cell_run_def, cell2_run_def, sum_bind_INR, opt_cell_def] \\
     qspec_then ‘inp1’ assume_tac opt_cell_input_correct \\ drule_first \\
     qspec_then ‘inp2’ assume_tac opt_cell_input_correct \\ drule_first \\

     last_x_assum mp_tac \\ CASE_TAC \\ CASE_TAC \\ strip_tac

     >- (rveq \\ fs [cell_run_def, sum_bind_def] \\ conj_tac
         >- (match_mp_tac opt_rel_cset_var \\ simp [])
         >- (Cases_on ‘t’ \\ fs [gol_cell_def]))
     >- (drule_strip bool_of_cell_input_correct \\
         drule_strip opt_cell2_1_correct \\ metis_tac [gol_cell_Cell2_new_inps])
     >- (fs [Once cell2_run_comm] \\
         drule_strip bool_of_cell_input_correct \\
         drule_strip opt_cell2_1_correct \\ metis_tac [gol_cell_Cell2_new_inps])
     >- (rveq \\
         imp_res_tac bool_of_cell_input_correct \\ gvs [] \\
         Cases_on ‘t’ \\ fs [gol_cell_def] \\ Cases_on ‘x’ \\ Cases_on ‘x'’ \\
         fs [cell2_run_def] \\
         match_mp_tac opt_rel_cset_var_insert_inp \\
         simp [cell_inp_run_def, opt_cell2_2_def]))
QED

Triviality opt_circuit_run_cells:
 ∀nl1 nl1' m m' s1 s1' s2 fext.
 opt_netlist m nl1 = (m', nl1') ∧
 sum_foldM (cell_run fext) s1 nl1 = INR s1' ∧
 opt_rel fext m s1 s2 ∧
 outs_not_in_env nl1 s1 ∧
 ALL_DISTINCT (FLAT $ MAP cell_output nl1) ∧
 EVERY gol_cell nl1 ⇒
 ∃s2'. sum_foldM (cell_run fext) s2 nl1' = INR s2' ∧
       opt_rel fext m' s1' s2' ∧
       EVERY gol_cell nl1'
Proof
 Induct \\ simp [opt_netlist_def, sum_foldM_INR] \\ rpt strip_tac' \\
 fs [outs_not_in_env_def] \\ fs [ALL_DISTINCT_APPEND] \\

 pairarg_tac \\ fs [] \\
 drule_strip opt_circuit_run_cell \\ impl_tac >- simp [] \\ strip_tac \\
 pairarg_tac \\ fs [] \\ rveq \\

 CASE_TAC \\ fs [] \\
 drule_first \\ (impl_tac >- metis_tac [cell_run_unchanged]) \\ simp [sum_foldM_INR]
QED

Triviality opt_reg_correct:
 ∀regs fext snet1 snet2 sreg1 sreg1' sreg2 m.
 sum_foldM (reg_run fext snet1) sreg1 regs = INR sreg1' ∧
 opt_rel fext m snet1 snet2 ∧
 opt_rel_regs empty sreg1 sreg2 ⇒
 ∃sreg2'. sum_foldM (reg_run fext snet2) sreg2 (MAP (opt_reg m) regs) = INR sreg2' ∧
          opt_rel_regs empty sreg1' sreg2'
Proof
 Induct >- simp [sum_foldM_def] \\ Cases \\ rename1 ‘(regi, _)’ \\ Cases_on ‘regi’ \\
 simp [sum_foldM_INR, reg_run_def] \\ rpt gen_tac \\
 CASE_TAC >- (rpt strip_tac \\ drule_first \\ simp [opt_reg_def, reg_run_def]) \\
 rpt strip_tac \\ fs [sum_bind_INR] \\ rveq \\
 drule_strip opt_cell_input_correct \\
 simp [opt_reg_def, reg_run_def, sum_bind_def] \\
 qmatch_goalsub_abbrev_tac ‘sum_foldM _ sreg2' _’ \\
 drule_first \\ disch_then (qspec_then ‘sreg2'’ mp_tac) \\
 unabbrev_all_tac \\ impl_tac >- (match_mp_tac opt_rel_regs_cset_var \\ simp []) \\
 strip_tac \\ simp []
QED

Triviality cget_var_FILTER_is_RegVar_NetVar:
 ∀s n. cget_var (s with env := FILTER (is_RegVar ∘ FST) s.env) (NetVar n) = INL UnknownVariable
Proof
 rw [cget_var_def, ALOOKUP_FILTER_FST, is_RegVar_def]
QED

Triviality cget_var_FILTER_is_RegVar_RegVar:
 ∀s reg i.
 cget_var (s with env := FILTER (is_RegVar ∘ FST) s.env) (RegVar reg i) = cget_var s (RegVar reg i)
Proof
 rw [cget_var_def, ALOOKUP_FILTER_FST, is_RegVar_def]
QED

Triviality opt_circuit_netlist_run_no_pseudos:
 ∀n nl1 nl1' m fext s1 s1' s2 regs.
 opt_netlist empty nl1 = (m, nl1') ∧
 netlist_run_no_pseudos fext s1 nl1 regs n = INR s1' ∧
 opt_rel_regs empty s1 s2 ∧
 outs_not_in_env nl1 s1 ∧
 ALL_DISTINCT (FLAT $ MAP cell_output nl1) ∧
 EVERY gol_cell nl1 ⇒
 ∃s2'. netlist_run_no_pseudos fext s2 nl1' (MAP (opt_reg m) regs) n = INR s2' ∧
       opt_rel (fext n) m s1' s2' ∧
       EVERY gol_cell nl1'
Proof
 Induct
 >- (rpt strip_tac' \\
     fs [netlist_run_no_pseudos_def] \\
     drule_strip opt_circuit_run_cells \\
     simp [opt_rel_opt_rel_regs])

 >- (rpt strip_tac' \\
     fs [netlist_run_no_pseudos_def, sum_bind_INR] \\
     drule_first \\
     simp [] \\
     qmatch_goalsub_abbrev_tac ‘sum_foldM _ s2'reg _’ \\
     drule_strip opt_reg_correct \\
     disch_then (qspec_then ‘s2'reg’ mp_tac) \\
     unabbrev_all_tac \\
     impl_tac >- (fs [opt_rel_def, opt_rel_regs_def,
                      cget_var_FILTER_is_RegVar_NetVar, cget_var_FILTER_is_RegVar_RegVar] \\
                  simp [lookup_def, empty_def]) \\ strip_tac \\
     simp [] \\
     drule_strip opt_circuit_run_cells \\
     disch_then (qspec_then ‘sreg2'’ mp_tac) \\
     impl_tac >- (metis_tac [opt_rel_opt_rel_regs, regs_run_only_regs,
                             only_regs_FILTER_is_RegVar, only_regs_outs_not_in_env]) \\ strip_tac \\
     simp [])
QED

Triviality opt_circuit_init_run:
 ∀regs m s s'.
 init_run s regs = INR s' ⇒ init_run s (MAP (opt_reg m) regs) = INR s'
Proof
 Induct >- rw [init_run_def] \\ Cases \\ rename1 ‘(regi, _)’ \\ Cases_on ‘regi’ \\ rw [opt_reg_def, init_run_def] \\
 every_case_tac \\ gs [] \\ pairarg_tac \\ fs []
QED

Triviality opt_outs_correct:
 ∀outs s1 s2 s' fext m.
 sum_mapM (out_run fext s1) outs = INR s' ∧
 opt_rel fext m s1 s2 ⇒
 sum_mapM (out_run fext s2) (MAP (opt_outs m) outs) = INR s'
Proof
 Induct >- simp [sum_mapM_def] \\ Cases \\ rename1 ‘(out, spec)’ \\ simp [sum_mapM_INR] \\ rpt strip_tac \\
 rveq \\ Cases_on ‘spec’
 >- (fs [opt_outs_def, out_run_def, sum_bind_INR] \\
     drule_strip opt_cell_input_correct \\
     simp [] \\ drule_first)
 >- (fs [opt_outs_def, out_run_def, sum_bind_INR] \\
     drule_strip sum_mapM_opt_cell_input_correct \\
     simp [] \\ drule_first)
QED

Triviality opt_circuit_regs_type_and_nl_ffs_lem:
 ∀cir cir'.
 opt_circuit cir = INR cir' ⇒
 EVERY (λ(_,rdata). rdata.reg_type = Reg) (circuit_regs cir') =
 EVERY (λ(_,rdata). rdata.reg_type = Reg) (circuit_regs cir) ∧
 circuit_nl_ffs cir' = circuit_nl_ffs cir
Proof
 Cases \\ simp [opt_circuit_def] \\ rpt strip_tac' \\ every_case_tac \\ fs [] \\ pairarg_tac \\ fs [] \\ rveq \\
 simp [circuit_regs_def, circuit_nl_ffs_def, EVERY_MAP] \\ match_mp_tac EVERY_CONG \\ simp [] \\
 Cases \\ rw [opt_reg_def] \\ every_case_tac \\ simp []
QED

Triviality EVERY_gol_cell_deterministic_netlist:
 ∀nl. EVERY gol_cell nl ⇒ deterministic_netlist nl
Proof
 rw [deterministic_netlist_def, EVERY_MEM] \\ drule_first \\
 Cases_on ‘e’ \\ fs [gol_cell_def, deterministic_cell_def]
QED

Triviality FST_opt_reg:
 FST ∘ (opt_reg m) = FST
Proof
 simp [FUN_EQ_THM] \\ Cases \\ simp [opt_reg_def]
QED

Triviality blast_regs_distinct_opt_reg:
 ∀regs m. blast_regs_distinct (MAP (opt_reg m) regs) = blast_regs_distinct regs
Proof
 rw [blast_regs_distinct_def, MAP_MAP_o, blast_reg_name_def, FST_opt_reg]
QED

Triviality reg_reg_type_opt_reg_lem:
 EVERY (λ(_,rdata). rdata.reg_type = Reg) (MAP (opt_reg m) regs) =
 EVERY (λ(_,rdata). rdata.reg_type = Reg) regs
Proof
 rw [EVERY_MAP] \\ match_mp_tac EVERY_CONG \\ simp [] \\ PairCases \\ rw [opt_reg_def] \\
 CASE_TAC \\ rw []
QED

Triviality reg_type_opt_reg_lem:
 EVERY (λ(_,rdata). rdata.type = CBool_t) (MAP (opt_reg m) regs) =
 EVERY (λ(_,rdata). rdata.type = CBool_t) regs
Proof
 rw [EVERY_MAP] \\ match_mp_tac EVERY_CONG \\ simp [] \\ PairCases \\ rw [opt_reg_def] \\
 CASE_TAC \\ rw []
QED

Triviality deterministic_regs_opt_reg_lem:
 deterministic_regs (MAP (opt_reg m) regs) = deterministic_regs regs
Proof
 rw [deterministic_regs_def, EVERY_MAP] \\ match_mp_tac EVERY_CONG \\ simp [] \\ PairCases \\ rw [opt_reg_def] \\
 CASE_TAC \\ rw [deterministic_reg_def]
QED

Theorem opt_circuit_correct:
 ∀cir cir' fext fbits n s.
 opt_circuit cir = INR cir' ∧
 blasted_circuit cir ∧
 circuit_run fext fbits cir n = INR s ⇒
 blasted_circuit cir' ∧
 circuit_run fext fbits cir' n = INR s
Proof
 Cases \\ simp [blasted_circuit_def] \\ rpt strip_tac' \\ first_x_assum mp_tac \\
 DEP_REWRITE_TAC [circuit_run_circuit_run_no_pseudos] \\
 conj_tac >- (drule_strip opt_circuit_regs_type_and_nl_ffs_lem \\
              fs [circuit_regs_def, circuit_nl_ffs_def]) \\ strip_tac \\

 fs [opt_circuit_def] \\ every_case_tac \\ fs [] \\ pairarg_tac \\ fs [] \\ rveq \\
 fs [circuit_run_no_pseudos_def, sum_bind_INR] \\ rveq \\

 drule_strip opt_circuit_init_run \\ simp [] \\
 drule_strip opt_circuit_netlist_run_no_pseudos \\
 disch_then (qspec_then ‘s'’ mp_tac) \\
 impl_tac >- (drule_strip init_run_only_regs \\ simp [only_regs_nil] \\ strip_tac \\
              simp [only_regs_outs_not_in_env, opt_rel_regs_sym]) \\ strip_tac \\
 simp [] \\
 conj_tac >- (drule_strip EVERY_gol_cell_deterministic_netlist \\
              fs [blasted_circuit_def] \\
              metis_tac [blast_regs_distinct_opt_reg, reg_reg_type_opt_reg_lem,
                         reg_type_opt_reg_lem, deterministic_regs_opt_reg_lem]) \\
 drule_strip opt_outs_correct \\
 fs [opt_rel_def, opt_rel_regs_def]
QED

Theorem opt_circuit_const:
 ∀cir cir' fext.
 opt_circuit cir = INR cir' ⇒
 (rtltype_extenv (circuit_extenv cir') fext = rtltype_extenv (circuit_extenv cir) fext) ∧
 (MAP FST (circuit_regs cir') = MAP FST (circuit_regs cir))
Proof
 Cases \\ rw [opt_circuit_def] \\ pairarg_tac \\ fs [] \\ rveq \\
 simp [circuit_extenv_def, circuit_regs_def, MAP_MAP_o, FST_opt_reg]
QED

val _ = export_theory ();
