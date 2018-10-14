open hardwarePreamble;

open helloProofTheory;

open verilogTheory verilogTypeTheory verilogTranslatorTheory moduleTranslatorTheory;
open ag32MachineTheory ag32EqTheory ag32VerilogTheory;

open verilogTranslatorLib;

val _ = new_theory "hello_ag32Verilog";

val _ = guess_lengths ();
val _ = prefer_num ();

val exit_code_0_def = Define `
 exit_code_0 vs fextv <=>
  erun fextv <| vars := vs |> (ArrayIndex (Var "R") [Const (w2ver (1w:word6))]) = INR (w2ver (0w:word32))`;

(* Should be moved, and replaced by event-based definition... *)
val ag32_is_halted_def = Define `
 ag32_is_halted fin mem_start <=>
 (mget_var fin "PC") = INR (w2ver (hello_machine_config mem_start).halt_pc)`;

val init_R_lift = Q.store_thm("init_R_lift",
 `!init hol_s s fext i.
   INIT_verilog_vars init /\ relM hol_s init /\ INIT fext hol_s s /\ i <> 0w ==> s.R i = 0w`,
 rw [INIT_verilog_vars_def, relM_def, relM_var_def, INIT_def, INIT_R_def] \\

 drule_first \\ pop_assum (fn th => rewrite_tac [GSYM th]) \\

 qmatch_asmsub_rename_tac `mget_var init "R" = INR r` \\
 fs [WORD_ARRAY_def, mget_var_ALOOKUP] \\
 Cases_on `r` \\ fs [w2ver_bij]);

val after_R_lift = Q.store_thm("after_R_lift",
 `!env (hol_s:state_circuit) (s:ag32_state) fext fextv n.
   lift_fext fextv fext /\ relM hol_s env /\ hol_s.R = s.R /\ exit_code_0 env (fextv n) ==>
   s.R 1w = 0w`,
 rw [exit_code_0_def] \\
 assume_tac (hol2hardware_exp ``s:state_circuit`` ``(s:state_circuit).R 1w`` |> GEN_ALL) \\
 fs [Eval_def] \\

 drule_strip relM_relS \\
 fs [lift_fext_relS_fextv_fext] \\
 last_x_assum (qspec_then `n` assume_tac) \\
 first_x_assum (qspecl_then [`hol_s`, `fext n`, `env`, `fextv n`, `<| vars := env |>`] mp_tac) \\

 impl_tac >- (fs [relS_def, relS_var_def, get_var_def] \\ metis_tac []) \\
 strip_tac \\ fs [WORD_def] \\ rveq \\ fs [w2ver_bij] \\ metis_tac []);

val external_memory_configured_def = Define`
 external_memory_configured fext start contents ⇔
  fext.mem = contents ∧
  byte_aligned start ∧
  w2n start + memory_size < dimword (:32)`;

val ag32_verilog_types_def = Define `
 ag32_verilog_types = relMtypes ++ ag32types`;

val hello_verilog = Q.store_thm("hello_verilog",
 `!vstep fext fextv init mem_start cl inp.
   vars_has_type init ag32_verilog_types ∧
   INIT_verilog (fext 0) init ∧

   vstep = mrun fextv computer init ∧

   is_lab_env fext_accessor_verilog vstep fext mem_start ∧
   external_memory_configured (fext 0) mem_start (hello_init_memory mem_start (cl, inp)) ∧
   lift_fext fextv fext ∧

   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   wfcl cl ∧
   LENGTH inp ≤ stdin_size ∧
   2 ≤ maxFD
   ⇒
   ?k fin.
    vstep k = INR fin /\
    let outs = MAP (get_ag32_io_event mem_start) (fext k).io_events;
        outs_spec = MAP get_output_io_event (hello_io_events cl (stdin_fs inp)) in
      ag32_is_halted fin mem_start ∧
      outs ≼ outs_spec ∧
      (exit_code_0 fin (fextv k) ⇒ (outs = outs_spec))`,
 rewrite_tac[external_memory_configured_def,ag32_verilog_types_def] \\
 rpt strip_tac \\
 drule_strip (vars_has_type_append |> SPEC_ALL |> EQ_IMP_RULE |> fst |> SPEC_ALL) \\

 drule_strip relM_backwards \\
 drule_strip INIT_backwards \\
 pop_assum (qspec_then `mem_start` strip_assume_tac) \\
 qmatch_asmsub_abbrev_tac `INIT _ _ s'` \\

 drule_strip (GEN_ALL hello_ag32_next) \\

 `INIT_ISA s' mem_start` by (qunabbrev_tac `s'` \\ simp [INIT_ISA_def, combinTheory.UPDATE_APPLY]) \\
 disch_then (qspec_then `s'` mp_tac) \\
 impl_tac >-
 (qunabbrev_tac `s'` \\
  fs [INIT_verilog_def, ag32_targetTheory.is_ag32_init_state_def] \\
  match_mp_tac EQ_EXT \\
  rw [ag32_targetTheory.ag32_init_regs_def, combinTheory.UPDATE_APPLY] \\
  drule_strip init_R_lift \\ fs [] \\ metis_tac [combinTheory.UPDATE_APPLY]) \\

 strip_tac \\
 first_x_assum(qspec_then`k1`mp_tac) \\
 impl_tac >- simp[] \\ strip_tac \\

 drule_strip (SIMP_RULE (srw_ss()) [] INIT_REL_circuit_verilog) \\
 pop_assum(qspec_then`k1`strip_assume_tac) \\
 asm_exists_tac \\
 fs [REL_def, ag32_is_halted_def, hello_machine_config_def, ag32_machine_config_def] \\ conj_tac

 >- fs [relM_def, relM_var_def, WORD_def]

 \\ strip_tac \\ drule_strip after_R_lift \\ drule_first);

val _ = export_theory ();
