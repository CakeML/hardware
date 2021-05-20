open hardwarePreamble;

open sumExtraTheory RTLTheory RTLPropsTheory;
 
open verilogSortTheory;
open verilogWriteCheckerTheory verilogTypeCheckerTheory PreCompilerTheory RTLCompilerTheory RTLDeterminizerTheory RTLUnusedRegsTheory RTLBlasterTheory;
open PreCompilerProofTheory RTLCompilerProofTheory RTLDeterminizerProofTheory RTLBlasterProofTheory;

val _ = new_theory "fullCompiler";

(** Run everything except technology mapping **)

Definition compile_def:
 compile m = do
  pseudos <<- compute_writes_bw m.combs;
  check_module pseudos m;
  combs <- sort_by_deps m.combs;
  m <<- m with combs := combs;
  m <- typecheck m;
  m <- preprocess m;
  (* Temporary hack, no need to fix this properly now since the preprocessing step should be replaced.
     We update the pseudos here since we can't do it entierly after preprocessing since preprocessing can drop
     writes, and not entierly after proprocessing since preprocessing adds writes (to temporary vars). *)
  pseudos <<- compute_writes_bw_inc pseudos m.combs;
  (circuit, tmpnum) <- RTLCompiler$compile pseudos m;
  circuit <- rtl_determinizer circuit;
  circuit <<- rtl_rem_unused_regs circuit;
  (circuit, blast_s) <- blast_circuit circuit tmpnum;
  (* Do another round of clean-up since the first round did not do element-level analysis *)
  circuit <<- rtl_rem_unused_regs circuit;
  return circuit
 od
End

Definition verilog_netlist_rel_def:
 verilog_netlist_rel m venv cenv <=>
  !var rdata.
   ALOOKUP m.decls var = SOME rdata ∧ rdata.output ⇒
   case sum_alookup venv var of
     INL e => T
   | INR (VBool b) => sum_alookup cenv var = INR (CBool b)
   | INR (VArray bs) => sum_alookup cenv var = INR (CArray bs)
End

Triviality blast_regs_distinct_FILTER_IMP:
 ∀P regs. blast_regs_distinct regs ⇒ blast_regs_distinct (FILTER P regs)
Proof
 simp [blast_regs_distinct_def, ALL_DISTINCT_MAP_FILTER]
QED

Triviality blasted_circuit_rtl_rem_unused_regs:
 ∀c. blasted_circuit c ⇒ blasted_circuit (rtl_rem_unused_regs c)
Proof
 Cases \\ simp [blasted_circuit_def, rtl_rem_unused_regs_def, deterministic_regs_def,
                blast_regs_distinct_FILTER_IMP, EVERY_FILTER_IMP]
QED

Triviality circuit_sorted_regs_distinct:
 ∀c. circuit_sorted c ⇒ regs_distinct (circuit_regs c)
Proof
 Cases \\ simp [circuit_sorted_def, circuit_regs_def]
QED

Triviality blasted_circuit_deterministic_distinct:
 ∀c. blasted_circuit c ⇒ deterministic_circuit c ∧ blast_regs_distinct (circuit_regs c)
Proof
 Cases \\ simp [blasted_circuit_def, deterministic_circuit_def, circuit_regs_def, deterministic_netlist_def]
QED

Triviality ALOOKUP_SOME:
 ∀l k v. ALOOKUP l k = SOME v ⇒ ∃v'. MEM (k, v') l
Proof
 Induct \\ TRY PairCases \\ rw [] \\ metis_tac []
QED

Theorem compile_correct:
 !m circuit fbits vfext rtlfext n.
 compile m = INR circuit ⇒
 
 vertype_fext m.fextty vfext ∧
 same_fext vfext rtlfext ⇒
 blasted_circuit circuit ∧
 rtltype_extenv (circuit_extenv circuit) rtlfext ∧
 (∀var i. MEM var (FLAT (MAP vwrites m.combs)) ⇒ ~MEM (var, i) (MAP FST (circuit_regs circuit))) ∧
 ?cenv' fbits'. circuit_run_no_pseudos rtlfext fbits circuit n = INR (cenv', fbits') /\
                ?vfbits. 
                  case sort_run vfext vfbits m n of
                    INL e => T
                  | INR (venv', vfbits') => verilog_netlist_rel m venv' cenv'
Proof
 simp [compile_def, sum_bind_INR] \\ rpt strip_tac' \\ rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\

 qspec_then ‘m.combs’ strip_assume_tac compute_writes_bw_correct \\
 drule_strip check_module_correct \\

 drule_strip sort_by_deps_correct \\
 drule_strip sort_by_deps_module_ok \\

 drule_strip typecheck_sound \\
 drule_strip typecheck_vwrites_comb \\
 drule_strip typecheck_module_ok \\

 drule_strip preprocess_correct \\

 qspecl_then [‘m.combs’, ‘m''.combs’] assume_tac compute_writes_bw_inc_correct \\

 drule_strip rtl_compile_correct \\ fs [] \\ disch_then drule_strip \\
 impl_tac >- (fs [verilogTheory.module_ok_def,
                  verilogTheory.writes_overlap_ok_def, 
                  verilogTheory.writes_overlap_ok_pseudos_def] \\ metis_tac []) \\ strip_tac \\
 first_assum (qspecl_then [‘n’, ‘fbits’] strip_assume_tac) \\

 drule_strip rtl_determinizer_correct \\

 drule_strip circuit_sorted_regs_distinct \\
 drule_strip regs_distinct_blast_regs_distinct \\
 drule_strip rtl_rem_unused_regs_correct \\
 qmatch_asmsub_abbrev_tac ‘rtl_rem_unused_regs cir_rem_inp’ \\
 qspec_then ‘cir_rem_inp’ strip_assume_tac rtl_rem_unused_regs_preserves \\
 unabbrev_all_tac \\
 ntac 2 drule_first \\

 drule_strip blast_circuit_correct \\ simp [] \\ disch_then drule_strip \\

 drule_strip blasted_circuit_deterministic_distinct \\
 drule_strip rtl_rem_unused_regs_correct \\

 simp [blasted_circuit_rtl_rem_unused_regs] \\
 conj_tac >- metis_tac [rtl_rem_unused_regs_mem_regs_lem, reg_type_distinct] \\
 (*rpt strip_tac \\ rpt drule_first \\ gvs [] \\
   drule_strip alistTheory.ALOOKUP_MEM \\
   drule_strip MEM_pair \\
   rpt drule_first \\ gvs [verilogTheory.module_ok_def, verilogTheory.writes_overlap_ok_def]*)
 
 rename1 ‘rtl_rem_unused_regs circuit’ \\
 qspec_then ‘rtl_rem_unused_regs circuit’ (mp_tac o GSYM) circuit_run_circuit_run_no_pseudos \\
 impl_tac >- (Cases_on ‘circuit’ \\ fs [blasted_circuit_def, circuit_regs_def, circuit_nl_ffs_def] \\
             (* Little hack for now:*)
             simp [rtl_rem_unused_regs_def, circuit_regs_def, circuit_nl_ffs_def, EVERY_FILTER_IMP]) \\ strip_tac \\

 rename1 ‘compile _ _ = INR (compile_circuit, _)’ \\
 rename1 ‘circuit_run _ compile_fbits compile_circuit _ = _’ \\
 first_x_assum (qspecl_then [‘n’, ‘compile_fbits’] strip_assume_tac) \\ 
 simp [] \\
 (* fbits generated from above: *)
 qexists_tac ‘fbits'⁸'’ \\ rpt TOP_CASE_TAC \\

 rw [verilog_netlist_rel_def] \\
 gvs [det_rel_reg_out_def, RTLCompilerProofTheory.same_state_outs_def, RTLBlasterProofTheory.same_state_outs_def] \\
 TOP_CASE_TAC \\ rpt drule_first \\ gs [] \\ drule_first \\
 rpt TOP_CASE_TAC \\ fs [same_value_cases]
QED

Triviality compile_correct_alt:
 !m circuit fbits vfbits' vfext rtlfext venv' n.
 compile m = INR circuit ∧
 vertype_fext m.fextty vfext ∧
 same_fext vfext rtlfext ⇒
 ?cenv' fbits'. circuit_run_no_pseudos rtlfext fbits circuit n = INR (cenv', fbits') /\
                ?vfbits. sort_run vfext vfbits m n = INR (venv', vfbits') ⇒ verilog_netlist_rel m venv' cenv'
Proof
 rpt strip_tac \\
 drule_strip compile_correct \\
 first_x_assum (qspecl_then [‘fbits’, ‘n’] strip_assume_tac) \\
 simp [] \\ qexists_tac ‘vfbits’ \\ every_case_tac \\ strip_tac \\ rveq \\ simp []
QED

val _ = export_theory ();
