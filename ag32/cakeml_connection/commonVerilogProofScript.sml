open hardwarePreamble;

open verilogTheory verilogTranslatorTheory moduleTranslatorTheory;
open ag32MachineTheory ag32EqTheory ag32VerilogTheory;

open ag32_machine_configTheory;

open verilogTranslatorLib;

val _ = new_theory "commonVerilogProof";

val _ = guess_lengths ();
val _ = prefer_num ();

val ag32_verilog_init_def = Define `
 ag32_verilog_init (code, data, config') (cl, input) init fext <=>
  (fext 0).mem = (init_memory code data (THE config'.ffi_names) (cl, input)) /\
  vars_has_type init (relMtypes ++ ag32types) /\
  INIT_verilog (fext 0) init`;

val lift_fext_exists = Q.store_thm("lift_fext_exists",
  `∀fext. ∃fextv. lift_fext fextv fext`,
  rw[moduleTranslatorTheory.lift_fext_def, GSYM SKOLEM_THM]
  \\ qmatch_goalsub_abbrev_tac`_ "error" = v1`
  \\ qmatch_goalsub_abbrev_tac`_ "ready" = v2`
  \\ qmatch_goalsub_abbrev_tac`_ "data_rdata" = v3`
  \\ qmatch_goalsub_abbrev_tac`_ "inst_rdata" = v4`
  \\ qmatch_goalsub_abbrev_tac`_ "mem_start_ready" = v5`
  \\ qmatch_goalsub_abbrev_tac`_ "interrupt_ack" = v6`
  \\ qexists_tac`λs.
      if s = "error" then v1 else
      if s = "ready" then v2 else
      if s = "data_rdata" then v3 else
      if s = "inst_rdata" then v4 else
      if s = "mem_start_ready" then v5 else
      if s = "interrupt_ack" then v6 else INL UnknownVariable`
  \\ rw[]);

val mrun_change_fextv = Q.store_thm("mrun_change_fextv",
  `lift_fext fextv1 fext ∧
   lift_fext fextv2 fext ⇒
     mrun fextv1 = mrun fextv2`,
  metis_tac[moduleTranslatorTheory.lift_fext_unique]);

val verilog_sem_def = Define`
  verilog_sem fext vprog ms =
    mrun (@fextv. lift_fext fextv fext) vprog ms`;

val exit_code_0_def = Define `
 exit_code_0 vs <=>
  erun ARB <| vars := vs |> (ArrayIndex (Var "R") [Const (w2ver (1w:word6))]) = INR (w2ver (0w:word32))`;

(* Should be replaced by event-based definition? *)
val is_halted_def = Define `
 is_halted (_, _, config') fin <=>
 let num_ffis = LENGTH (THE config'.ffi_names) in
  (mget_var fin "PC") = INR (w2ver (n2w (ffi_jumps_offset + (num_ffis + 1) * ffi_offset):word32))`;

val is_halted_lem = Q.prove(
 `!fext1 fext2 vs.
   erun fext1 vs (ArrayIndex (Var "R") [Const (w2ver (1w:'a word))]) =
   erun fext2 vs (ArrayIndex (Var "R") [Const (w2ver (1w:'a word))])`,
 rw [erun_def, erun_get_var_def, sum_mapM_def, sum_map_def, sum_bind_def]);

val after_R_1w_lift = Q.store_thm("after_R_1w_lift",
 `!env (hol_s:state_circuit) (s:ag32_state) fext fextv.
   lift_fext fextv fext /\ relM hol_s env /\ hol_s.R 1w = s.R 1w /\ exit_code_0 env ==>
   s.R 1w = 0w`,
 rw [exit_code_0_def] \\
 assume_tac (hol2hardware_exp ``s:state_circuit`` ``(s:state_circuit).R 1w`` |> GEN_ALL) \\
 fs [Eval_def] \\

 drule_strip relM_relS \\
 fs [lift_fext_relS_fextv_fext] \\
 last_x_assum (qspec_then `n` assume_tac) \\
 first_x_assum (qspecl_then [`hol_s`, `fext n`, `env`, `fextv n`, `<| vars := env |>`] mp_tac) \\

 impl_tac >- (fs [relS_def, relS_var_def, get_var_def] \\ metis_tac []) \\
 strip_tac \\ fs [WORD_def] \\ rveq \\
 qmatch_asmsub_abbrev_tac `erun (fextv n) vs exp = res` \\
 `erun ARB vs exp = res` by metis_tac [is_halted_lem] \\
 unabbrev_all_tac \\ fs [w2ver_bij]);

val after_R_lift = Q.store_thm("after_R_lift",
 `!env (hol_s:state_circuit) (s:ag32_state) fext fextv.
   lift_fext fextv fext /\ relM hol_s env /\ hol_s.R = s.R /\ exit_code_0 env ==>
   s.R 1w = 0w`,
 metis_tac [after_R_1w_lift]);

(* Move *)
val get_mem_word_word_at_addr = Q.store_thm("get_mem_word_word_at_addr",
 `!mem addr. get_mem_word mem addr = word_at_addr mem addr`,
 rw [word_at_addr_def, ag32_memoryTheory.get_mem_word_def]);

val is_prefix_extract_writes = Q.store_thm("is_prefix_extract_writes",
 `!l1 l2 fd. l1 ≼ l2 ==> extract_writes fd l1 ≼ extract_writes fd l2`,
 Induct >- rw [ag32_basis_ffiProofTheory.extract_writes_def] \\

 rw [] \\ every_case_tac \\ fs [] \\
 rveq \\ first_x_assum drule \\ disch_then (qspec_then `fd` assume_tac) \\
 fs [ag32_basis_ffiProofTheory.extract_writes_def] \\ rw []);

val _ = export_theory ();
