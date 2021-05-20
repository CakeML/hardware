open hardwarePreamble;

open avgCircuitTheory;

open newTranslatorLib compileLib RTLPrintLib;

val _ = new_theory "avgCircuitCompile";

(** HOL -> Verilog **)

val trans_thm = module2hardware avg_def ["avg"] ["h0", "h1", "h2", "h3"];

(*

always_ff @ (posedge clk) begin
 h0 <= signal;
 h1 <= h0;
 h2 <= h1;
 h3 <= h2;
end

always_comb begin
 avg = h0 + h1 + h2 + h3;
 avg[0] = avg[2];
 avg[1] = avg[3];
 avg[2] = avg[4];
 avg[3] = avg[5];
 avg[4] = avg[6];
 avg[5] = avg[7];
 avg[6] = 0;
 avg[7] = 0;
end

*)

(** Verilog -> netlist **)

val (circuit, circuit_correct) = compile (definition "avg_v_def")

(*
print_Circuit (circuit |> concl |> rhs) |> print
writeFile "avg.sv"
*)

(** Transport proof to netlist level **)

(* Transport correctness to Verilog level *)
Theorem avg_v_correct:
 !n vfext fext vfbits.
 fext_rel_n fextv_rel vfext fext ⇒
 ?vs vfbits'.
  run vfext vfbits avg_v n = INR (vs, vfbits') /\
  sum_alookup vs "avg" = INR (w2ver (avg_spec fext n))
Proof
 rpt strip_tac \\
 drule_strip trans_thm \\
 first_x_assum (qspecl_then [‘n’, ‘vfbits’] strip_assume_tac) \\
 fs [definition"module_state_rel_def", module_state_rel_var_def, sum_alookup_INR, WORD_def, avg_correct]
QED

Definition w2net_def:
 w2net w = CArray (w2v w)
End

(* More direct way to handle fext... could/should be generated automatically... *)
Definition nfext_rel_def:
 nfext_rel nfext fext ⇔
 ∀n. nfext n "signal" = INR (w2net (fext n).signal) ∧
     ∀var. var ∉ {"signal"} ⇒ nfext n var = INL UnknownVariable
End

(* Move this fext stuff: *)
open RTLCompilerProofTheory;

Theorem sum_same_value_cases:
 ∀x y. sum_same_value x y ⇔ (∃e. x = INL e ∧ y = INL e) ∨ (∃x' y'. x = INR x' ∧ y = INR y' ∧ same_value x' y')
Proof
 rpt Cases \\ simp [sum_same_value_def] \\ simp [EQ_SYM_EQ]
QED

Theorem same_value_cases:
 ∀x y. same_value x y ⇔ (∃b. x = VBool b ∧ y = CBool b) ∨ (∃bs. x = VArray bs ∧ y = CArray bs)
Proof
 rpt Cases \\ simp [same_value_def] \\ simp [EQ_SYM_EQ]
QED

Definition net2ver_def:
 (net2ver (CBool b) = VBool b) ∧
 (net2ver (CArray bs) = VArray bs)
End

Theorem same_value_net2ver:
 ∀v. same_value (net2ver v) v
Proof
 Cases \\ simp [net2ver_def, same_value_def]
QED

Theorem net2ver_w2net:
 ∀w. net2ver (w2net w) = w2ver w
Proof
 simp [net2ver_def, w2net_def, w2ver_def]
QED

(*Definition ver2net_def:
 (ver2net (VBool b) = CBool b) ∧
 (ver2net (VArray bs) = CArray bs)
End*)

Definition rtlfext_to_vfext_def:
 rtlfext_to_vfext rtlfext n var = sum_map net2ver (rtlfext n var)
End

Theorem same_fext_net2ver:
 ∀rtlfext. same_fext (rtlfext_to_vfext rtlfext) rtlfext
Proof
 rw [rtlfext_to_vfext_def, same_fext_def, sum_same_value_cases] \\
 Cases_on ‘rtlfext n var’ \\ simp [sum_map_def, same_value_net2ver]
QED

Triviality nfext_rel_vfext_lem:
 ∀nfext fext. nfext_rel nfext fext ⇔ ∃vfext. fext_rel_n fextv_rel vfext fext ∧ same_fext vfext nfext
Proof
 rw [nfext_rel_def, fext_rel_n_def, definition"fextv_rel_def"] \\ eq_tac \\ rw []
 >- (qexists_tac ‘rtlfext_to_vfext nfext’ \\ rw [same_fext_net2ver] \\
     simp [rtlfext_to_vfext_def, sum_map_def, net2ver_w2net])
 >- (first_x_assum (qspec_then ‘n’ strip_assume_tac) \\
     fs [same_fext_def] \\ first_x_assum (qspecl_then [‘n’, ‘"signal"’] assume_tac) \\
     gvs [sum_same_value_cases, same_value_cases, w2ver_def, w2net_def])
 >- (fs [same_fext_def] \\
     first_x_assum (qspecl_then [‘n’, ‘var’] assume_tac) \\
     first_x_assum (qspec_then ‘n’ strip_assume_tac) \\ drule_first \\
     fs [sum_same_value_cases])
QED

(* Can generated this automatically? *)
Triviality avg_fextv_rel_vertype_fext:
 ∀fext vfext. fext_rel_n fextv_rel vfext fext ⇒ vertype_fext avg_v.fextty vfext
Proof
 rw [fext_rel_n_def, vertype_fext_def, definition"avg_v_def", sum_alookup_def, definition"fextv_rel_def"] \\
 every_case_tac \\ fs [] \\ simp [w2ver_def, vertype_v_cases]
QED

(* Transport correctness to netlist level *)
(* TODO: Fix fext assumptions somehow... *)
Theorem avg_circuit_correct:
 !n fext nfext fbits.
 (*fext_rel_n fextv_rel vfext fext ∧ same_fext vfext nfext ⇒*)
 nfext_rel nfext fext ⇒
 ?s fbits'.
  circuit_run_no_pseudos nfext fbits avg_v_tech_circuit n = INR (s, fbits') ∧
  ALOOKUP s "avg" = SOME (w2net (avg_spec fext n))
Proof
 rewrite_tac [nfext_rel_vfext_lem] \\
 rpt strip_tac \\
 drule_strip avg_fextv_rel_vertype_fext \\
 drule_strip circuit_correct \\
 first_x_assum (qspecl_then [‘fbits’, ‘n’] strip_assume_tac) \\
 simp [] \\

 qspec_then ‘avg_v’ mp_tac verilogSortTheory.already_sorted_sort_run \\
 impl_tac >- EVAL_TAC \\ strip_tac \\

 drule_strip avg_v_correct \\
 first_x_assum (qspecl_then [‘n’, ‘vfbits’] strip_assume_tac) \\

 fs [verilog_netlist_rel_def] \\
 first_x_assum (qspec_then ‘"avg"’ mp_tac) \\
 simp [definition"avg_v_def", definition"avg_v_decls_def", w2ver_def, w2net_def, sum_alookup_INR]
QED

val _ = export_theory ();
