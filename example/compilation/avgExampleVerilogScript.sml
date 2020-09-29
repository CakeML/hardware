open hardwarePreamble;

open verilogTranslatorLib moduleTranslatorTheory;
open fullCompilerTheory TechMapLib BetterLECLib RTLPrintLib;

val _ = new_theory "avgExampleVerilog";

(** Step 1: HOL to Verilog **)

val trans = hol2hardware_step_function (avg_step_def |> REWRITE_RULE [soft_div_by_4_def]);
val prog_def = EvalS_get_prog (trans |> concl);
val vavg_step_def = Define `vavg_step = ^prog_def`;
val trans = REWRITE_RULE [GSYM vavg_step_def] trans;

(* Ad-hoc lifting as we only have one process and no non-blocking writes *)
Theorem avg_step_relM:
 !n fext fextv fbits init vs ps.
 relM (avg fext init n) vs /\ lift_fext fextv fext ⇒
 ?vs' fbits'.
  mstep_commit (fextv n) fbits [vavg_step] vs = INR (vs', fbits') /\
  relM (avg fext init (SUC n)) vs'
Proof
 rw [mstep_commit_def, mstep_def, sum_foldM_def, lift_fext_relS_fextv_fext] \\
 first_x_assum (qspec_then `n` assume_tac) \\
 drule_strip relM_relS \\
 drule_strip (trans |> REWRITE_RULE [EvalS_def]) \\
 drule_strip deterministic_process_prun \\ impl_tac >- EVAL_TAC \\
 disch_then (qspec_then ‘fbits’ assume_tac) \\
 drule vnwrites_nil_correct \\ impl_tac >- EVAL_TAC \\ strip_tac \\
 fs [sum_bind_def, sum_map_def, avg_def] \\
 fs [relS_def, relM_def, relS_var_def, relM_var_def, GSYM get_var_sum_alookup]
QED

Theorem avg_step_relM_run:
 !n fextv fext fbits init vs.
 relM init vs /\ lift_fext fextv fext ⇒
 ?vs' fbits'.
  mrun fextv fbits [vavg_step] vs n = INR (vs', fbits') /\
  relM (avg fext init n) vs'
Proof
 rpt strip_tac \\ match_mp_tac mstep_commit_mrun \\ rpt conj_tac
 >- simp [avg_def]
 \\ rpt strip_tac \\ match_mp_tac avg_step_relM \\ simp []
QED

val decls = avg_init_def |> concl |> rhs |> state_to_decls;
val vavg_decls_def = Define `vavg_decls = ^decls`;

Theorem vavg_decls_correct:
 ∀fbits. ∃s fbits'. run_decls fbits vavg_decls [] = (fbits, s) ∧ relM avg_init s
Proof
 gen_tac \\ simp [run_decls_def, vavg_decls_def] \\
 simp [relM_def, relM_var_def, sum_alookup_def, avg_init_def] \\
 simp [WORD_def]
QED

Definition vavg_def:
 vavg = Module [("signal", VArray_t 8); ("enabled", VBool_t)] vavg_decls [vavg_step]
End

Theorem vavg_correct:
 !n vfext fext vfbits.
 lift_fext vfext fext ⇒
 ?vs vfbits'.
  run vfext vfbits vavg n = INR (vs, vfbits') /\
  sum_alookup vs "avg" = INR (w2ver (avg_spec fext n))
Proof
 simp [run_def, vavg_def] \\ rpt strip_tac \\
 qspec_then ‘vfbits’ strip_assume_tac vavg_decls_correct \\
 drule_strip avg_step_relM_run \\ first_x_assum (qspecl_then [‘n’, ‘vfbits’] strip_assume_tac) \\
 fs [relM_def, relM_var_def, WORD_def, avg_correct]
QED

(** Step 2: Verilog to RTL **)

val compile_result = EVAL “compile ["avg"] vavg”;

val circuit = compile_result |> concl |> rhs |> sumSyntax.dest_inr |> fst;
val newnl = tech_map circuit;

val (extenv, regs, nl) = dest_Circuit circuit;

Definition avg_extenv_def:
 avg_extenv = ^extenv
End

Definition avg_regs_def:
 avg_regs = ^regs
End

Definition avg_high_nl_def:
 avg_high_nl = ^nl
End

Definition avg_nl_def:
 avg_nl = ^newnl
End

val th = betterlec avg_extenv_def avg_regs_def avg_high_nl_def avg_nl_def;
val th = th |> REWRITE_RULE [GSYM avg_extenv_def, GSYM avg_regs_def, GSYM avg_high_nl_def, GSYM avg_nl_def];
val compile_result = compile_result |> REWRITE_RULE [GSYM avg_extenv_def, GSYM avg_regs_def, GSYM avg_high_nl_def];
val circuit = th |> concl |> strip_forall |> snd |> dest_imp |> snd |> lhs |> rator |> rand;

Definition navg_def:
 navg = ^circuit
End

Definition w2net_def:
 w2net w = CArray (w2v w)
End

Definition sum_alookup_blasted_def:
 sum_alookup_blasted s reg v =
  case v of
    CBool b => cget_var s (RegVar reg 0) = INR (CBool b)
  | CArray bs => ∀i. i < LENGTH bs ⇒ cget_var s (RegVar reg i) = INR (CBool (EL i bs))
End

open RTLCompilerTheory;
open RTLCompilerProofTheory;

Definition rtlfext_to_vfext_def:
 rtlfext_to_vfext rtlfext n var =
  case (rtlfext n var) of
    INL e => INL e
  | INR (CBool b) => INR (VBool b)
  | INR (CArray bs) => INR (VArray bs)
End

Theorem same_fext_rtlfext_to_vfext:
 ∀rtlfext. same_fext (rtlfext_to_vfext rtlfext) rtlfext
Proof
 rw [same_fext_def, rtlfext_to_vfext_def] \\
 every_case_tac \\ simp [sum_same_value_def, same_value_def]
QED

(* Could/should be generated automatically... *)
Definition lift_nfext_def:
 lift_nfext rtlfext fext ⇔
 ∀n. rtlfext n "signal" = INR (w2net (fext n).signal) ∧
     rtlfext n "enabled" = INR (CBool (fext n).enabled) ∧
     ∀var. var ∉ {"signal"; "enabled"} ⇒ rtlfext n var = INL UnknownVariable
End

Theorem lift_nfext_lift_fext:
 ∀rtlfext fext. lift_nfext rtlfext fext ⇒ lift_fext (rtlfext_to_vfext rtlfext) fext
Proof
 simp [lift_nfext_def, lift_fext_def] \\ rpt strip_tac' \\ first_x_assum (qspec_then ‘n’ strip_assume_tac) \\
 simp [rtlfext_to_vfext_def, w2ver_def, w2net_def]
QED

Theorem verilog_netlist_rel_sum_alookup_sum_alookup_blasted:
 ∀keep vs cenv var keep v.
 verilog_netlist_rel keep vs cenv ∧
 sum_alookup vs var = INR (w2ver v) ∧
 MEM var keep ⇒
 sum_alookup_blasted cenv var (w2net v)
Proof
 rw [verilog_netlist_rel_def, sum_alookup_blasted_def] \\ drule_first \\ rfs [w2ver_def, w2net_def]
QED

Theorem lift_nfext_rtltype_extenv_avgv_circuit:
 lift_nfext fextrtl fext ⇒ rtltype_extenv (circuit_extenv navg) fextrtl
Proof
 rw [circuit_extenv_def, navg_def, lift_nfext_def, RTLTypeTheory.rtltype_extenv_def, avg_extenv_def] \\
 every_case_tac \\ fs [] \\ simp [RTLTypeTheory.rtltype_v_cases, w2net_def]
QED

Theorem avgv_rtlcircuit_correct:
 !n nfext fext nfbits.
 lift_nfext nfext fext ⇒
 ?s.
  circuit_run nfext nfbits navg n = INR s ∧
  sum_alookup_blasted s "avg" (w2net (avg_spec fext n))
Proof
 rpt strip_tac \\
 drule_strip lift_nfext_rtltype_extenv_avgv_circuit \\
 assume_tac compile_result \\ fs [vavg_def] \\
 drule (SIMP_RULE (srw_ss()) [LET_THM] compile_correct) \\
 disch_then (qspecl_then [‘nfbits’, ‘rtlfext_to_vfext nfext’, ‘nfext’] mp_tac) \\
 impl_tac >- (
 conj_tac >- (simp [verilogTypeCheckerTheory.writes_ok_compute] \\ EVAL_TAC) \\
 conj_asm2_tac >- (drule_strip (GSYM rtltype_extenv_compile_fextenv) \\
                   fs [circuit_extenv_def, navg_def, avg_extenv_def,
                       compile_fextenv_def, compile_type_def]) \\
 simp [same_fext_rtlfext_to_vfext]) \\ simp [RTLBlasterProofTheory.blasted_circuit_def] \\ strip_tac \\

 qmatch_asmsub_abbrev_tac ‘Circuit cext cregs cnl’ \\
 qspecl_then [‘nfext’, ‘nfbits’, ‘cext’, ‘cregs’, ‘cnl’] mp_tac populated_by_regs_only_ISR_from_circuit_run \\
 unabbrev_all_tac \\
 impl_tac >- (rw []
              >- (first_x_assum (qspec_then ‘n’ strip_assume_tac) \\ simp [])
              >- EVAL_TAC) \\ strip_tac \\
 first_x_assum (qspec_then ‘n’ strip_assume_tac) \\
 
 drule_strip lift_nfext_lift_fext \\
 drule_strip vavg_correct \\
 first_x_assum (qspecl_then [‘n’, ‘vfbits’] strip_assume_tac) \\ fs [vavg_def] \\

 drule_strip th \\ impl_tac >- fs [circuit_extenv_def, navg_def] \\
 disch_then (qspecl_then [‘n’, ‘nfbits’] assume_tac) \\ fs [navg_def] \\
 
 match_mp_tac verilog_netlist_rel_sum_alookup_sum_alookup_blasted \\ rpt asm_exists_any_tac \\ simp []
QED

(* Print to Verilog...

navg_def |> REWRITE_RULE [avg_extenv_def, avg_regs_def, avg_nl_def] |> concl |> rhs
         |> print_Circuit |> writeFile "avg.sv";

output logic[7:0] avg
assign avg = {avg0, avg1, avg2, avg3, avg4, avg5, avg6, avg7};

*)

val _ = export_theory ();
