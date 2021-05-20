open hardwarePreamble;

open FSMCircuitsTheory;

open newTranslatorLib compileLib RTLPrintLib;

val _ = new_theory "FSMCircuitsCompile";

val moore_def' =
 moore_def
 |> ONCE_REWRITE_RULE [procs_sing |> ISPEC “moore_seq” |> SYM,
                       moore_comb_def];
val moore_trans_thm = module2hardware moore_def' ["out_seq"] ["state"];
val (moore_circuit, moore_circuit_corr) = compile (definition "moore_v_def");

(* Basically same proofs as in avg theory: *)

(* Transport correctness to Verilog level *)
Theorem moore_v_correct:
 !n vfext fext vfbits.
 fext_rel_n fextv_rel vfext fext ⇒
 ?vs vfbits'.
  run vfext vfbits moore_v n = INR (vs, vfbits') /\
  sum_alookup vs "out_seq" = INR (VBool (moore_spec fext n))
Proof
 rpt strip_tac \\
 drule_strip moore_trans_thm \\
 first_x_assum (qspecl_then [‘n’, ‘vfbits’] strip_assume_tac) \\
 fs [definition"module_state_rel_def", module_state_rel_var_def, sum_alookup_INR, BOOL_def, moore_correct]
QED

(* Can generated this automatically? *)
Triviality moore_fextv_rel_vertype_fext:
 ∀fext vfext. fext_rel_n fextv_rel vfext fext ⇒ vertype_fext moore_v.fextty vfext
Proof
 rw [fext_rel_n_def, vertype_fext_def, definition"moore_v_def", sum_alookup_def, definition"fextv_rel_def"] \\
 every_case_tac \\ fs [] \\ simp [w2ver_def, vertype_v_cases]
QED

(* Transport correctness to netlist level *)
(* TODO: Fix fext assumptions somehow... *)
Theorem moore_circuit_correct:
 !n fext vfext rtlfext fbits.
 fext_rel_n fextv_rel vfext fext ∧ same_fext vfext rtlfext ⇒
 ?s fbits'.
  circuit_run_no_pseudos rtlfext fbits moore_v_tech_circuit n = INR (s, fbits') ∧
  sum_alookup s "out_seq" = INR (CBool (moore_spec fext n))
Proof
 rpt strip_tac \\
 drule_strip moore_fextv_rel_vertype_fext \\
 drule_strip moore_circuit_corr \\
 first_x_assum (qspecl_then [‘fbits’, ‘n’] strip_assume_tac) \\
 simp [] \\

 qspec_then ‘moore_v’ mp_tac verilogSortTheory.already_sorted_sort_run \\
 impl_tac >- EVAL_TAC \\ strip_tac \\

 drule_strip moore_v_correct \\
 first_x_assum (qspecl_then [‘n’, ‘vfbits’] strip_assume_tac) \\

 fs [verilog_netlist_rel_def] \\
 first_x_assum (qspec_then ‘"out_seq"’ mp_tac) \\
 simp [definition"moore_v_def", definition"moore_v_decls_def"]
QED

val mealy_def' =
 mealy_def
 |> ONCE_REWRITE_RULE [procs_sing |> ISPEC “mealy_comb” |> SYM,
                       mealy_seq_def];
val mealy_trans_thm = module2hardware mealy_def' ["out_seq"] ["state", "in_seq_reg"];
val (mealy_circuit, mealy_circuit_corr) = compile (definition "mealy_v_def");

(* print_Circuit (mealy_circuit |> concl |> rhs) |> writeFile "mealy.sv" *)

val _ = export_theory ();
