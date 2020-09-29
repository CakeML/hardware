open hardwarePreamble;

open sortingTheory;

open oracleTheory sumExtraTheory RTLTheory RTLTypeTheory;

open RTLLib;

val _ = new_theory "RTLProps";

(** Some fbits thms **)

Theorem rtlstate_fbits_fbits:
 !(s:rtlstate). s with fbits := s.fbits = s
Proof
 simp [rtlstate_component_equality]
QED

Theorem cget_var_fbits:
 !cenv fbits var. cget_var (cenv with fbits := fbits) var = cget_var cenv var
Proof
 rw [cget_var_def]
QED

Theorem cset_var_fbits:
 (!s k v fbits. cset_var (s with fbits := fbits) k v = (cset_var s k v) with fbits := fbits) /\
 (!s k v fbits. (cset_var s k v).fbits = s.fbits)
Proof
 rw [cset_var_def]
QED

Theorem cell_inp_run_fbits:
 !inp fext s fbits. cell_inp_run fext (s with fbits := fbits) inp = cell_inp_run fext s inp
Proof
 Cases_on `inp` \\ rw [cell_inp_run_def, cget_var_def]
QED

Theorem rtl_nd_value_fbits:
 ∀t fbits fbits' v.
 rtl_nd_value fbits t = (v, fbits') ⇒
 fbits' = shift_seq (rtltype_v_size t) fbits ∧
 ∀newfbits. init_seq_eq newfbits fbits (rtltype_v_size t) ⇒
            rtl_nd_value newfbits t = (v, shift_seq (rtltype_v_size t) newfbits)
Proof
 Cases \\ simp [rtl_nd_value_def, rtltype_v_size_def, init_seq_eq_def, oracle_bit_def, oracle_bits_genlist] \\
 rpt strip_tac \\ match_mp_tac GENLIST_CONG \\ rw []
QED

Theorem init_run_fbits:
 ∀regs cenv cenv'.
 init_run cenv regs = INR cenv' ⇒
 ∃n. cenv'.fbits = shift_seq n cenv.fbits ∧
     ∀fbits. init_seq_eq fbits cenv.fbits n ⇒
             init_run (cenv with fbits := fbits) regs = INR (cenv' with fbits := shift_seq n fbits)
Proof
 Induct >- (rw [init_run_def] \\ qexists_tac ‘0’ \\ simp [shift_seq_0]) \\
 PairCases \\ simp [init_run_def] \\ TOP_CASE_TAC \\ rw []
 >- (pairarg_tac \\ drule_strip rtl_nd_value_fbits \\ fs [] \\ drule_first \\ fs [] \\
    qexists_tac ‘rtltype_v_size h0 + n’ \\ rw [shift_seq_add] \\

    last_x_assum (qspec_then ‘fbits’ mp_tac) \\ impl_tac >- fs [init_seq_eq_def] \\ strip_tac \\ simp [] \\

    first_x_assum (qspec_then ‘shift_seq (rtltype_v_size h0) fbits’ mp_tac) \\
    simp [init_seq_eq_shift_seq, cset_var_fbits])

 \\ drule_first \\ qexists_tac ‘n’ \\ fs [cset_var_fbits]
QED

Theorem reg_run_fbits:
 !fext s_net s_reg fbits fbits' destsrc.
 reg_run fext (s_net with fbits := fbits) (s_reg with fbits := fbits') destsrc =
 sum_map (\s. s with fbits := fbits') (reg_run fext s_net s_reg destsrc)
Proof
 rpt gen_tac \\ PairCases_on `destsrc` \\ rw [reg_run_def, cell_inp_run_fbits] \\
 TOP_CASE_TAC >- simp [sum_map_def] \\
 Cases_on `cell_inp_run fext s_net x` \\ simp [sum_bind_def, sum_map_def, cset_var_fbits] \\
 IF_CASES_TAC \\ simp [sum_map_def]
QED

Theorem sum_foldM_reg_run_fbits:
 !regs fext s_net s_reg s fbits fbits'. 
 sum_foldM (reg_run fext s_net) s_reg regs = INR s ==>
 ?s'. sum_foldM (reg_run fext (s_net with fbits := fbits)) (s_reg with fbits := fbits') regs = INR s' /\
      s'.env = s.env /\ s'.fbits = fbits'
Proof
 Induct \\ rw [sum_foldM_def, sum_map_def, sum_bind_INR, reg_run_fbits] \\ simp [sum_map_def]
QED

Triviality cell_inp_run_fbits_without_inp:
 ∀fext cenv fbits. cell_inp_run fext (cenv with fbits := fbits) = cell_inp_run fext cenv
Proof
 simp [FUN_EQ_THM, cell_inp_run_fbits]
QED

Theorem cell_run_fbits:
 ∀cell fext cenv cenv'.
 cell_run fext cenv cell = INR cenv' ⇒
 ∃m. cenv'.fbits = shift_seq m cenv.fbits ∧
     ∀fbits. init_seq_eq fbits cenv.fbits m ⇒
             cell_run fext (cenv with fbits := fbits) cell = INR (cenv' with fbits := shift_seq m fbits)
Proof
 Cases \\ cell_run_tac rw
 >- (* NDetCell bool *)
 (qexists_tac ‘1’ \\ fs [oracle_bit_def] \\ rw [cset_var_fbits, init_seq_eq_def])
 >- (* NDetCell array *)
 (qexists_tac ‘n’ \\ fs [oracle_bits_genlist] \\ rw [cset_var_fbits] \\
  drule_strip init_seq_eq_genlist \\ simp [])
 \\ (* ... other cells *)
 qexists_tac ‘0’ \\ simp [cell_inp_run_fbits_without_inp, cset_var_fbits, shift_seq_0] \\
 (* Carry... *)
 every_case_tac \\ fs [] \\ rveq \\ fs [] \\ rw [cset_var_fbits]
QED

Theorem cells_run_fbits:
 ∀nl fext cenv cenv'.
 sum_foldM (cell_run fext) cenv nl = INR cenv' ⇒
 ∃m. cenv'.fbits = shift_seq m cenv.fbits ∧
     ∀fbits. init_seq_eq fbits cenv.fbits m ⇒
             sum_foldM (cell_run fext) (cenv with fbits := fbits) nl = INR (cenv' with fbits := shift_seq m fbits)
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_INR] >- (qexists_tac ‘0’ \\ simp [shift_seq_0]) \\
 drule_strip cell_run_fbits \\ drule_first \\ qexists_tac ‘m + m'’ \\ rw [shift_seq_add] \\
 last_x_assum (qspec_then ‘fbits’ mp_tac) \\ impl_tac >- fs [init_seq_eq_def] \\ strip_tac \\
 first_x_assum (qspec_then ‘shift_seq m fbits’ mp_tac) \\ simp [init_seq_eq_shift_seq]
QED

Theorem netlist_step_fbits:
 ∀nl fext cenv cenv' regs.
 netlist_step fext cenv nl regs = INR cenv' ⇒
 ∃m. cenv'.fbits = shift_seq m cenv.fbits ∧
     ∀fbits. init_seq_eq fbits cenv.fbits m ⇒
             netlist_step fext (cenv with fbits := fbits) nl regs = INR (cenv' with fbits := shift_seq m fbits)
Proof
 rw [netlist_step_def, sum_bind_INR] \\ rw [] \\
 drule_strip cells_run_fbits \\ qexists_tac ‘m’ \\ rw [] \\ drule_first \\
 drule_strip sum_foldM_reg_run_fbits \\
 first_x_assum (qspecl_then [‘shift_seq m fbits’, ‘fbits’] strip_assume_tac) \\
 rw [] \\ rw [rtlstate_component_equality]
QED

Theorem netlist_run_fbits:
 ∀n fext cenv cenv' nl regs.
 netlist_run fext cenv nl regs n = INR cenv' ⇒
 ∃m. cenv'.fbits = shift_seq m cenv.fbits ∧
     ∀fbits. init_seq_eq fbits cenv.fbits m ⇒
             netlist_run fext (cenv with fbits := fbits) nl regs n = INR (cenv' with fbits := shift_seq m fbits)
Proof
 Induct \\ rw [netlist_run_def, sum_bind_INR] >- (qexists_tac ‘0’ \\ simp [shift_seq_0]) \\ drule_first \\
 drule_strip netlist_step_fbits \\ qexists_tac ‘m + m'’ \\ rw [shift_seq_add] \\
 last_x_assum (qspec_then ‘fbits’ mp_tac) \\ impl_tac >- fs [init_seq_eq_def] \\ strip_tac \\ simp [] \\
 first_x_assum (qspec_then ‘shift_seq m fbits’ mp_tac) \\ simp [init_seq_eq_shift_seq] 
QED

(* ... *)

Theorem cget_var_cset_var:
 !env var var' v. cget_var (cset_var env var' v) var = if var = var' then INR v else cget_var env var
Proof
 rw [cget_var_def, cset_var_def]
QED

Theorem cell_inp_run_cset_var:
 !cenv var1 var2 idx v fext.
 cell_inp_run fext (cset_var cenv var2 v) (VarInp var1 NONE) =
 if var1 = var2 then INR v else cell_inp_run fext cenv (VarInp var1 NONE)
Proof
 rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def]
QED

(* TODO: Merge with above... *)
Theorem cell_inp_run_cset_var':
 !cenv var1 var2 idx v fext.
 cell_inp_run fext (cset_var cenv var2 v) (VarInp var1 idx) =
 if var1 = var2 then cget_fext_var idx v else cell_inp_run fext cenv (VarInp var1 idx)
Proof
 rw [cell_inp_run_def, cget_var_cset_var, sum_bind_def]
QED

Theorem cell_inp_run_cset_var_ConstInp:
 !cenv var v v' fext.
 cell_inp_run fext (cset_var cenv var v) (ConstInp v') = cell_inp_run fext cenv (ConstInp v')
Proof
 rw [cell_inp_run_def, cget_var_cset_var]
QED

Theorem cell_inp_run_cset_var_ExtInp:
 !cenv var var' v fext i.
 cell_inp_run fext (cset_var cenv var' v) (ExtInp var i) = cell_inp_run fext cenv (ExtInp var i)
Proof
 rw [cell_inp_run_def, cget_var_cset_var]
QED

Theorem cell_inp_run_INR_cong:
 ∀inp st st' fext v.
 (∀var v. cget_var st' var = INR v ⇒ cget_var st var = INR v) ∧
 cell_inp_run fext st' inp = INR v ⇒
 cell_inp_run fext st inp = INR v
Proof
 Cases \\ rw [cell_inp_run_def, sum_bind_INR] \\ drule_first \\ simp []
QED

(*Theorem cell_inp_run_cset_var_uninformative:
 !cenv var1 var2 v fext.
 (cell_inp_run fext (cset_var cenv var2 v) var1 = INR v) \/
 (cell_inp_run fext (cset_var cenv var2 v) var1 = cell_inp_run fext cenv var1)
Proof
 Cases_on `var1` \\ rw [cell_inp_run_def, cget_var_cset_var]
QED*)

(*Theorem circuit_run_empty:
 !env n. circuit_run (Circuit [] []) env n = INR env
Proof
 Induct_on `n` \\ rw [circuit_run_def, circuit_step_def, sum_foldM_def, sum_bind_def]
QED*)

Theorem cells_run_cget_var_mono:
 !nl cenv cenv' var cv fext.
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 cget_var cenv var = INR cv ==>
 ?cv'. cget_var cenv' var = INR cv'
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_INR] >- rw [] \\ drule_first \\
 Cases_on `h` \\ cell_run_tac fs \\ rveq \\ disch_then (qspec_then `var` mp_tac) \\ rw [cget_var_cset_var] \\
 (* NDetCell: *)
 rpt (pairarg_tac \\ rveq \\ fs []) \\ rveq \\ fs [cget_var_cset_var] \\ every_case_tac \\ fs [cget_var_def]
QED

(*Theorem cells_run_cell_inp_run_mono:
 !nl cenv cenv' inp cv fext.
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 cell_inp_run fext cenv inp = INR cv ==>
 ?cv'. cell_inp_run fext cenv' inp = INR cv'
Proof
 Cases_on `inp` \\ rw [cell_inp_run_def, sum_bind_INR] \\ metis_tac [cells_run_cget_var_mono]
QED*)

Theorem cells_run_cget_var_RegVar:
 !nl cenv cenv' var fext i.
 sum_foldM (cell_run fext) cenv nl = INR cenv' ==>
 cget_var cenv' (RegVar var i) = cget_var cenv (RegVar var i)
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_INR] \\ drule_first \\
 Cases_on `h` \\ cell_run_tac fs \\ rveq \\ fs [cget_var_cset_var] \\
 (* NDetCell: *)
 rpt (pairarg_tac \\ rveq \\ fs []) \\ rveq \\ fs [cget_var_cset_var] \\ every_case_tac \\ fs [cget_var_def]
QED

Theorem cells_run_cell_inp_run_RegVar:
 !nl cenv cenv' var fext i idx.
 sum_foldM (cell_run fext) cenv nl = INR cenv' ==>
 cell_inp_run fext cenv' (VarInp (RegVar var i) idx) = cell_inp_run fext cenv (VarInp (RegVar var i) idx)
Proof
 rw [cell_inp_run_def] \\ drule_strip cells_run_cget_var_RegVar \\ simp []
QED

(*Theorem cells_run_cget_var_NetVar:
 !nl cenv cenv' n fext.
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\ ~MEM n (MAP cell_output nl) ==>
 cget_var cenv' (NetVar n) = cget_var cenv (NetVar n)
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_INR] \\ drule_first \\
 Cases_on `h` \\ cell_run_tac fs \\ rveq \\ fs [cget_var_cset_var] \\
 (* NDetCell: *)
 rpt (pairarg_tac \\ rveq \\ fs []) \\ rveq \\ fs [cget_var_cset_var] \\ every_case_tac \\ fs [cget_var_def]
QED*)

Theorem cell_run_unchanged:
 !cell fext st st' out.
 cell_run fext st cell = INR st' /\ ~MEM out (cell_output cell) ==>
 cget_var st' (NetVar out) = cget_var st (NetVar out) 
Proof
 Cases \\ simp [cell_output_def] \\ cell_run_tac rw \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ rw [cget_var_cset_var, cget_var_def]
QED

Theorem cells_run_unchanged:
 !nl fext st st' out.
 sum_foldM (cell_run fext) st nl = INR st' /\ ~MEM out (FLAT (MAP cell_output nl)) ==>
 cget_var st' (NetVar out) = cget_var st (NetVar out) 
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_INR] \\ metis_tac [cell_run_unchanged]
QED

(* Cell/netlist wf definitions and related *)

Definition cell_input_covered_by_extenv_def:
 (cell_input_covered_by_extenv extenv (ExtInp var idx) <=> ?t. ALOOKUP extenv var = SOME t) /\
 (cell_input_covered_by_extenv extenv _ <=> T)
End

Definition cell_covered_by_extenv_def:
 (cell_covered_by_extenv extenv (NDetCell out t) <=> T) /\
 (cell_covered_by_extenv extenv (Cell1 cell1 out inp1) <=> cell_input_covered_by_extenv extenv inp1) /\
 (cell_covered_by_extenv extenv (Cell2 cell2 out inp1 inp2) <=> cell_input_covered_by_extenv extenv inp1 /\ cell_input_covered_by_extenv extenv inp2) /\
 (cell_covered_by_extenv extenv (CellMux out inp1 inp2 inp3) <=> cell_input_covered_by_extenv extenv inp1 /\ cell_input_covered_by_extenv extenv inp2 /\ cell_input_covered_by_extenv extenv inp3) /\
 (cell_covered_by_extenv extenv (CellArrayWrite out inp1 idx inp2) <=> cell_input_covered_by_extenv extenv inp1 /\ cell_input_covered_by_extenv extenv inp2) /\
 (cell_covered_by_extenv extenv _ <=> F)
End

val var_lt_def = Define `
 (var_lt (RegVar _ _) n <=> T) /\
 (var_lt (NetVar m) n <=> m < n)`;

val cell_input_lt_def = Define `
 (cell_input_lt (ConstInp value) n <=> T) /\
 (cell_input_lt (ExtInp var _) n <=> T) /\
 (cell_input_lt (VarInp var _) n <=> var_lt var n)`;

Theorem cell_inp_run_cong_lt:
 ∀inp s2 s1 fext n.
 (∀var. var_lt var n ⇒ cget_var s2 var = cget_var s1 var) ∧
 cell_input_lt inp n ⇒
 cell_inp_run fext s2 inp = cell_inp_run fext s1 inp
Proof
 Cases \\ simp [cell_inp_run_def, cell_input_lt_def]
QED

Definition reg_ok_def:
 reg_ok extenv max (ty, reg, i, v, inp) <=>
  i = 0 /\
  OPTION_ALL (\v. has_rtltype_v v ty) v /\
  OPTION_ALL (\inp. cell_input_lt inp max) inp /\
  OPTION_ALL (cell_input_covered_by_extenv extenv) inp
End

val regs_ok_def = Define `
 regs_ok extenv max regs <=> EVERY (reg_ok extenv max) regs`;

val cell_output_ok_def = Define `
 (cell_output_ok min max (out:num) <=> min <= out /\ out < max)`;

val cell_ok_def = Define `
 (cell_ok min max (NDetCell out _) <=> cell_output_ok min max out) /\
 (cell_ok min max (Cell1 _ out in1) <=> cell_output_ok min max out /\ cell_input_lt in1 out) /\
 (cell_ok min max (Cell2 _ out in1 in2) <=> cell_output_ok min max out /\ cell_input_lt in1 out /\ cell_input_lt in2 out) /\
 (cell_ok min max (CellMux out in1 in2 in3) <=> cell_output_ok min max out /\ cell_input_lt in1 out /\ cell_input_lt in2 out /\ cell_input_lt in3 out) /\
 (cell_ok min max (CellArrayWrite out in1 n in2) <=> cell_output_ok min max out /\ cell_input_lt in1 out /\ cell_input_lt in2 out) /\
 (cell_ok min max _ <=> F)`;

val netlist_ok_def = Define `
 netlist_ok extenv min max nl <=>
  EVERY (cell_covered_by_extenv extenv) nl /\
  EVERY (cell_ok min max) nl`;

Theorem netlist_ok_cons:
 ∀extenv min max c cs.
 netlist_ok extenv min max (c::cs) <=>
 cell_covered_by_extenv extenv c ∧
 cell_ok min max c ∧
 netlist_ok extenv min max cs
Proof
 rw [netlist_ok_def] \\ eq_tac \\ rw []
QED

(* Local properties *)
Definition circuit_ok_def:
 circuit_ok min max (Circuit extenv regs nl) <=>
  regs_ok extenv max regs /\
  netlist_ok extenv min max nl
End

Definition netlist_sorted_def:
 netlist_sorted nl <=> SORTED ($<) (FLAT (MAP cell_output nl))
End

Theorem netlist_sorted_nil:
 netlist_sorted []
Proof
 rw [netlist_sorted_def]
QED

Theorem less_sorted_append:
 ∀(L1 : num list) L2. (SORTED $< (L1 ⧺ L2) ⇔ SORTED $< L1 ∧ SORTED $< L2 ∧ ∀x y. MEM x L1 ⇒ MEM y L2 ⇒ x < y)
Proof
 match_mp_tac SORTED_APPEND \\ simp []
QED

Theorem netlist_sorted_cons:
 ∀c cs.
 netlist_sorted (c::cs) ⇔
 SORTED $< (cell_output c) ∧
 netlist_sorted cs ∧
 (∀out out'. MEM out (cell_output c) ∧ MEM out' (FLAT (MAP cell_output cs)) ⇒ out < out')
Proof
 rw [netlist_sorted_def, less_sorted_append] \\ eq_tac \\ rw []
QED

Theorem netlist_sorted_all_distinct:
 ∀nl. netlist_sorted nl ⇒ ALL_DISTINCT (FLAT (MAP cell_output nl))
Proof
 rw [netlist_sorted_def] \\ irule SORTED_ALL_DISTINCT \\ asm_exists_any_tac \\
 simp [relationTheory.irreflexive_def]
QED

Definition reg_name_def:
 reg_name (ty, dest, i, v, inp) = dest
End

Definition reg_idx_def:
 reg_idx (ty, dest, i, v, inp) = i
End

Definition regs_distinct_def:
 regs_distinct regs <=> ALL_DISTINCT (MAP reg_name regs)
End

Definition blast_reg_name_def:
 blast_reg_name (ty,dest,i,v,inp) = (dest, i)
End

Definition blast_regs_distinct_def:
 blast_regs_distinct regs = ALL_DISTINCT (MAP blast_reg_name regs)
End

Theorem regs_distinct_tl:
 ∀reg regs. regs_distinct (reg::regs) ⇒ regs_distinct regs
Proof
 rw [regs_distinct_def]
QED

Theorem regs_distinct_blast_regs_distinct:
 ∀regs. regs_distinct regs ⇒ blast_regs_distinct regs
Proof
 rw [regs_distinct_def, blast_regs_distinct_def] \\
 qsuff_tac ‘MAP reg_name regs = MAP FST (MAP blast_reg_name regs)’ >- metis_tac [ALL_DISTINCT_MAP] \\
 simp [MAP_MAP_o] \\ irule MAP_CONG \\ simp [] \\ PairCases \\ simp [reg_name_def, blast_reg_name_def]
QED

(* Global properties, TODO: rename... *)
Definition circuit_sorted_def:
 circuit_sorted (Circuit _ regs nl) <=> regs_distinct regs /\ netlist_sorted nl
End

Theorem var_lt_le:
 !var n m. var_lt var n /\ n <= m ==> var_lt var m
Proof
 Cases \\ rw [var_lt_def]
QED

Theorem cell_input_lt_le:
 !inp n m. cell_input_lt inp n /\ n <= m ==> cell_input_lt inp m
Proof
 Cases \\ rw [cell_input_lt_def] \\ metis_tac [var_lt_le]
QED

Theorem cell_input_lt_SUC:
 !inp n. cell_input_lt inp n ==> cell_input_lt inp (SUC n)
Proof
 rpt strip_tac \\ match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp []
QED

Theorem EVERY_cell_input_lt_le:
 !l n m. EVERY (λinp. cell_input_lt inp n) l /\ n <= m ==> EVERY (λinp. cell_input_lt inp m) l
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [] \\
 match_mp_tac cell_input_lt_le \\ rpt asm_exists_tac
QED

Theorem cell_ok_le:
 !cell min min' max max'.
  cell_ok min' max' cell /\ min <= min' /\ max' <= max ==> cell_ok min max cell
Proof
 Cases \\ rw [cell_ok_def, cell_output_ok_def]
QED

Theorem netlist_ok_le:
 !extenv min min' max max' nl.
  netlist_ok extenv min' max' nl /\ min <= min' /\ max' <= max ==>
  netlist_ok extenv min max nl
Proof
 rw [netlist_ok_def] \\ irule EVERY_MONOTONIC \\ metis_tac [cell_ok_le]
QED

(*Theorem netlist_ok_cons:
 !min max c cs.
  netlist_ok min max (c::cs) <=> cell_ok min max c /\ netlist_ok min max cs
Proof
 rw [netlist_ok_def]
QED*)

Theorem netlist_ok_append:
 !extenv min max l1 l2.
  netlist_ok extenv min max (l1 ++ l2) <=> netlist_ok extenv min max l1 /\ netlist_ok extenv min max l2
Proof
 rw [netlist_ok_def] \\ eq_tac \\ rw []
QED

(* Can be made more general... *)
Theorem cell_input_lt_cell_inp_run_cset_var:
 !inp fext s n v.
 cell_input_lt inp n ==>
 cell_inp_run fext (cset_var s (NetVar n) v) inp = cell_inp_run fext s inp
Proof
 Cases \\ rw [cell_inp_run_def, cell_input_lt_def] \\
 Cases_on `v` \\ fs [var_lt_def, cget_var_cset_var]
QED

Theorem netlist_ok_mem_cell_output:
 !nl EEv min max ml out.
 netlist_ok EEv min max nl /\ MEM out (FLAT (MAP cell_output nl)) ==> min <= out /\ out < max
Proof
 simp [netlist_ok_def, MEM_FLAT, MEM_MAP, EVERY_MEM] \\ rpt strip_tac' \\ rveq \\ drule_first \\
 Cases_on ‘y’ \\ fs [cell_ok_def, cell_output_ok_def, cell_output_def]
QED

Theorem netlist_sorted_append:
 !EEv min1 max1 max2 nl1 nl2.
 netlist_ok EEv min1 max1 nl1 /\ netlist_ok EEv max1 max2 nl2 /\
 netlist_sorted nl1 /\ netlist_sorted nl2 ==>
 netlist_sorted (nl1 ++ nl2)
Proof
 rw [netlist_sorted_def] \\ match_mp_tac SORTED_APPEND_IMP \\ rw [] \\
 imp_res_tac netlist_ok_mem_cell_output \\ simp []
QED

Theorem cell_ok_cell_output_lt:
 !cell min max out. cell_ok min max cell ∧ MEM out (cell_output cell) ⇒ out < max
Proof
 Cases \\ rw [cell_ok_def, cell_output_ok_def, cell_output_def]
QED
 
Theorem netlist_sorted_snoc:
 ∀EE nl cell min max.
 netlist_ok EE min max nl ∧ netlist_sorted nl ∧
 SORTED $< (cell_output cell) ∧ (∀out. MEM out (cell_output cell) ⇒ max ≤ out) ⇒
 netlist_sorted (nl ⧺ [cell])
Proof
 rw [netlist_sorted_def, netlist_ok_def, EVERY_MEM] \\
 match_mp_tac SORTED_APPEND_IMP \\ rw [MEM_FLAT, MEM_MAP] \\
 rpt drule_first \\ drule_strip cell_ok_cell_output_lt \\ decide_tac
QED

(* Special case that is sometimes useful *)
Theorem netlist_sorted_append_snoc:
 ∀EE nl1 nl2 cell min1 max1 max2.
 netlist_ok EE min1 max1 nl1 ∧ netlist_ok EE max1 max2 nl2 ∧
 min1 ≤ max1 ∧ max1 ≤ max2 ∧
 netlist_sorted nl1 ∧ netlist_sorted nl2 ∧
 SORTED $< (cell_output cell) ∧ (∀out. MEM out (cell_output cell) ⇒ max2 ≤ out) ⇒
 netlist_sorted (nl1 ++ nl2 ++ [cell])
Proof
 rpt strip_tac \\ match_mp_tac netlist_sorted_snoc \\
 Q.LIST_EXISTS_TAC [‘EE’, ‘min1’, ‘max2’] \\ simp [netlist_ok_append] \\ rpt conj_tac
 >- (match_mp_tac netlist_ok_le \\ asm_exists_tac \\ simp [])
 >- (match_mp_tac netlist_ok_le \\ asm_exists_tac \\ simp [])
 \\ match_mp_tac netlist_sorted_append \\ rpt asm_exists_tac
QED

(*Theorem cells_run_unchanged_lt:
 ∀inp nl fext s s' n.
 sum_foldM (cell_run fext) s nl = INR s' ∧
 cell_input_lt inp n ∧ EVERY (λcell. EVERY (λout. n <= out) (cell_output cell)) nl ⇒
 cell_inp_run fext s' inp = cell_inp_run fext s inp
Proof
 Cases \\ simp [cell_inp_run_def] \\ Cases_on ‘v’
 >- (rpt strip_tac \\ drule_strip cells_run_cget_var_RegVar \\ simp [])
 \\ Induct \\ simp [sum_foldM_def, sum_bind_INR] \\ rpt strip_tac \\
    drule_first \\ simp [] \\ drule_strip cell_run_unchanged \\ disch_then (qspec_then ‘n’ mp_tac) \\
    impl_tac >- (fs [EVERY_MEM, cell_input_lt_def, var_lt_def] \\ strip_tac \\ drule_first \\ fs []) \\ simp []
QED*)
      
(*(* Special form of the above, sometimes useful *)
Theorem cells_run_unchanged_EVERY:
 ∀inps nl fext s s' n.
 sum_foldM (cell_run fext) s nl = INR s' ∧
 EVERY (λinp. cell_input_lt inp n) inps ∧
 EVERY (λcell. EVERY (λout. n <= out) (cell_output cell)) nl ⇒
 EVERY (λinp. cell_inp_run fext s' inp = cell_inp_run fext s inp) inps
Proof
 rpt strip_tac \\ qpat_x_assum ‘EVERY _ inps’ mp_tac \\ simp [EVERY_MEM] \\ rpt strip_tac \\ drule_first \\
 drule_strip cells_run_unchanged
QED*)

(* Properties of deterministic netlists... *)

val deterministic_cell_def = Define `
 (deterministic_cell (NDetCell _ _) = F) /\
 (deterministic_cell _ = T)`;

val deterministic_netlist_def = Define `
 deterministic_netlist nl <=> EVERY deterministic_cell nl`;

val deterministic_reg_def = Define `
 deterministic_reg (t, reg, i, v, inp) <=> v <> NONE`;

val deterministic_regs_def = Define `
 deterministic_regs regs <=> EVERY deterministic_reg regs`;

val deterministic_circuit_def = Define `
 deterministic_circuit (Circuit _ regs nl) <=> deterministic_regs regs /\ deterministic_netlist nl`;

Theorem deterministic_regs_filter:
 ∀regs P. deterministic_regs regs ⇒ deterministic_regs (FILTER P regs)
Proof
 simp [deterministic_regs_def, EVERY_FILTER_IMP]
QED

Theorem deterministic_netlist_append:
 ∀nl1 nl2. deterministic_netlist (nl1 ⧺ nl2) ⇔ deterministic_netlist nl1 ∧ deterministic_netlist nl2
Proof
 simp [deterministic_netlist_def]
QED
 
Theorem run_cell_deterministic_cell:
 !cell fext s s'. cell_run fext s cell = INR s' /\ deterministic_cell cell ==> s'.fbits = s.fbits
Proof
 Cases \\ cell_run_tac rw \\ fs [deterministic_cell_def, cset_var_def] \\
 every_case_tac \\ fs [] \\ rveq \\ fs [] \\ rw []
QED

Theorem run_cells_deterministic_netlist:
 !nl fext s s'.
 sum_foldM (cell_run fext) s nl = INR s' /\ deterministic_netlist nl ==> s'.fbits = s.fbits
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_INR] \\ drule_first \\
 fs [deterministic_netlist_def] \\ drule_strip run_cell_deterministic_cell \\ simp []
QED

Theorem init_run_append:
 !regs1 regs2 s s'.
 init_run s (regs1 ++ regs2) = INR s' <=>
 ?s''. init_run s regs1 = INR s'' /\
       init_run s'' regs2 = INR s'
Proof
 Induct >- simp [init_run_def] \\ gen_tac \\ PairCases_on `h` \\ rw [init_run_def] \\ TOP_CASE_TAC
 >- (pairarg_tac \\ simp [])
 >- (IF_CASES_TAC \\ simp [])
QED

Theorem init_run_cons:
 !reg regs s s'.
 init_run s (reg::regs) = INR s' <=>
 ?s''. init_run s [reg] = INR s'' /\
       init_run s'' regs = INR s'
Proof
 rewrite_tac [Once rich_listTheory.CONS_APPEND, init_run_append]
QED

Theorem init_run_deterministic:
 ∀regs s1 s1'. init_run s1 regs = INR s1' ∧ deterministic_regs regs ⇒ s1'.fbits = s1.fbits
Proof
 Induct \\ TRY PairCases \\ rw [init_run_def] \\
 every_case_tac \\ fs [deterministic_regs_def, deterministic_reg_def] \\
 drule_first \\ fs [cset_var_fbits]
QED

Theorem init_run_cget_var_NetVar:
 !decls s s'. init_run s decls = INR s' ==> !n. cget_var s' (NetVar n) = cget_var s (NetVar n)
Proof
 Induct >- rw [init_run_def] \\ PairCases \\ simp [init_run_def] \\ TOP_CASE_TAC \\ rpt strip_tac
 >- (pairarg_tac \\ rveq \\ fs [] \\ drule_first \\ simp [cget_var_cset_var, cget_var_fbits])
 \\ every_case_tac \\ fs [] \\ drule_first \\ simp [cget_var_cset_var]
QED

Theorem reg_run_cget_var:
 !reg snet sreg s' fext.
  reg_run fext snet sreg reg = INR s' ==>
  s'.fbits = sreg.fbits ∧
  (!n. cget_var s' (NetVar n) = cget_var sreg (NetVar n)) ∧
  (!reg' i. reg' ≠ reg_name reg ∨ i ≠ reg_idx reg ⇒ cget_var s' (RegVar reg' i) = cget_var sreg (RegVar reg' i))
Proof
 PairCases \\ simp [reg_run_def, reg_name_def, reg_idx_def] \\ TOP_CASE_TAC \\
 rw [sum_bind_INR] \\ rw [cget_var_cset_var, cset_var_fbits]
QED

Theorem regs_run_fbits:
 ∀regs snet sreg s' fext.
 sum_foldM (reg_run fext snet) sreg regs = INR s' ==>
 s'.fbits = sreg.fbits
Proof
 Induct \\ rw [sum_foldM_INR] \\ drule_strip reg_run_cget_var \\ metis_tac []
QED

Theorem regs_run_cget_var_RegVar:
 !regs snet sreg s' fext reg.
  sum_foldM (reg_run fext snet) sreg regs = INR s' ∧ ~MEM reg (MAP reg_name regs) ==>
  !i. cget_var s' (RegVar reg i) = cget_var sreg (RegVar reg i)
Proof
 Induct \\ rw [sum_foldM_INR] \\ drule_strip reg_run_cget_var \\ metis_tac []
QED

Theorem regs_run_cget_var_NetVar:
 !regs snet sreg s' fext.
  sum_foldM (reg_run fext snet) sreg regs = INR s' ==>
  !n. cget_var s' (NetVar n) = cget_var sreg (NetVar n)
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_INR] \\ drule_strip reg_run_cget_var \\ drule_first \\ simp []
QED

(* some more lemmas *)

Theorem cell_run_new_value:
 !cell fext st st' out.
 cell_run fext st cell = INR st' ∧ MEM out (cell_output cell) ⇒
 ∃v. cget_var st' (NetVar out) = INR v
Proof
 Cases \\ cell_run_tac rw \\ fs [cell_output_def, cget_var_cset_var]
 >- (fs [oracle_bit_def] \\ rw [cget_var_cset_var])
 >- (fs [oracle_bits_genlist] \\ rw [cget_var_cset_var])
 \\ every_case_tac \\ fs [] \\ rw [] \\ fs [] \\ rw [cget_var_cset_var]
QED

Theorem cells_run_cget_var_INL:
 !nl cenv cenv' n fext e.
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\ cget_var cenv' (NetVar n) = INL e ==>
 ~MEM n (FLAT (MAP cell_output nl))
Proof
 Induct \\ simp [sum_foldM_def, sum_bind_INR] \\ rpt strip_tac' \\ drule_first \\ simp [] \\
 strip_tac \\ drule_strip cell_run_new_value \\ drule_strip cells_run_cget_var_mono \\ fs []
QED

Theorem rtl_nd_value_type_correct:
 !t v oracle oracle'. rtl_nd_value oracle t = (v, oracle') ==> rtltype_v v t
Proof
 Cases \\ rw [rtl_nd_value_def]
 >- (fs [oracle_bit_def] \\ rw [rtltype_v_cases])
 \\ pairarg_tac \\ drule_strip oracle_bits_correct \\ fs [] \\ rw [rtltype_v_cases]
QED

Theorem ndetcell_run_type:
 !t cenv. ?fbits v. ndetcell_run cenv t = (cenv with fbits := fbits, v) /\ rtltype_v v t
Proof
 Cases \\ rw [ndetcell_run_def]
 >- (pairarg_tac \\ simp [rtltype_v_cases] \\ metis_tac [])
 \\ pairarg_tac \\ drule_strip oracleTheory.oracle_bits_correct \\ simp [rtltype_v_cases] \\ metis_tac []
QED

(* drule version of above thm <-- todo: refactor... *)
Theorem ndetcell_run_type_drule:
 !t v cenv cenv'.
 ndetcell_run cenv t = (cenv', v) ⇒
 ?fbits. cenv' = cenv with fbits := fbits ∧ rtltype_v v t
Proof
 rpt strip_tac \\ qspecl_then [‘t’, ‘cenv’] strip_assume_tac ndetcell_run_type \\ fs [] \\ metis_tac []
QED

Theorem same_shape_refl:
 ∀v. same_shape v v
Proof
 Cases \\ rw [same_shape_def]
QED

Theorem same_shape_sym:
 ∀v1 v2. same_shape v1 v2 ⇔ same_shape v2 v1
Proof
 Cases \\ Cases \\ rw [same_shape_def]
QED

Theorem same_shape_trans:
 ∀a b c. same_shape a b ∧ same_shape b c ⇒ same_shape a c
Proof
 rpt Cases \\ rw [same_shape_def]
QED

Theorem same_shape_inv:
 (∀v b. same_shape (CBool b) v ⇔ ∃b'. v = CBool b') ∧
 (∀v b. same_shape v (CBool b) ⇔ ∃b'. v = CBool b') ∧
 (∀v bs. same_shape (CArray bs) v ⇔ ∃bs'. v = CArray bs' ∧ LENGTH bs' = LENGTH bs) ∧
 (∀v bs. same_shape v (CArray bs) ⇔ ∃bs'. v = CArray bs' ∧ LENGTH bs' = LENGTH bs)
Proof
 rpt conj_tac \\ Cases \\ rw [same_shape_def]
QED

Theorem rtltype_v_same_shape:
 ∀t v v'. rtltype_v v t ∧ rtltype_v v' t ⇒ same_shape v v'
Proof
 Cases \\ rw [rtltype_v_cases] \\ rw [same_shape_def]
QED

Theorem rtltype_v_same_shape_rtltype_v:
 ∀t v1 v2. rtltype_v v1 t ∧ same_shape v2 v1 ⇒ rtltype_v v2 t
Proof
 Cases \\ rw [rtltype_v_cases] \\ fs [same_shape_inv]
QED

val _ = export_theory ();
