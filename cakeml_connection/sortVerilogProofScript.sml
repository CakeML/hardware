open hardwarePreamble;

open sortProofTheory;

open commonVerilogProofLib;

val _ = new_theory "sortVerilogProof";

val sort_spec_def = Define `
 sort_spec input output <=>
  ?output'.
   output = explode (concat output') /\
   PERM output' (lines_of (implode input)) /\
   SORTED mlstring_le output'`;

(* Another case where lift_tac is not general enough *)

val sort_ag32_next_verilog_lem = Q.prove(
 `!vstep fext ms input.
   vstep = verilog_sem fext computer ms ∧

   STRLEN input ≤ stdin_size ∧
   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) ([strlit "sort"], input) ms fext
   ⇒
   ?k1. !k. k1 ≤ k ==> ?fin.
    vstep k = INR fin /\
    let stdout = extract_writes 1 (MAP get_ag32_io_event (fext k).io_events);
        stdout_spec = extract_writes 1 (MAP get_output_io_event (sort_io_events input))
    in
      is_halted (code, data, config) fin ∧
      stdout ≼ stdout_spec ∧
      (exit_code_0 fin ⇒ stdout = stdout_spec)`,
 rewrite_tac [verilog_sem_def] \\ rpt gen_tac \\
 SELECT_ELIM_TAC \\ conj_tac >- metis_tac[lift_fext_exists] \\

 rewrite_tac [ag32_verilog_init_def] \\ rpt strip_tac \\
 drule_strip (vars_has_type_append |> SPEC_ALL |> EQ_IMP_RULE |> fst |> SPEC_ALL) \\

 drule_strip relM_backwards \\
 drule_strip INIT_backwards \\
 qmatch_asmsub_abbrev_tac `INIT _ _ s'` \\

 drule_strip (sort_ag32_next |> GEN_ALL) \\

 disch_then (qspec_then `s'` mp_tac) \\
 impl_tac >- (qunabbrev_tac `s'` \\ simp [ag32_targetTheory.is_ag32_init_state_def]) \\

 strip_tac \\
 first_x_assum(qspec_then`k1`mp_tac) \\
 impl_tac >- simp[] \\ strip_tac \\

 drule_strip (SIMP_RULE (srw_ss()) [] INIT_REL_circuit_verilog) \\
 pop_assum(qspec_then`k1`strip_assume_tac) \\
 qexists_tac `m` \\ rpt strip_tac' \\

 fs [is_lab_env_def] \\
 drule_strip is_mem_verilog \\
 drule_strip is_interrupt_interface_verilog \\
 drule_strip (SIMP_RULE (srw_ss()) [] circuit_halt_compute_step_full_actual') \\
 fs [arithmeticTheory.LESS_EQ_EXISTS] \\
 qmatch_assum_rename_tac `k = m + m1` \\ rveq \\
 disch_then (qspecl_then [`m`, `m1`] mp_tac) \\ impl_tac
 >- (rpt conj_tac
    >- (fs [REL_def] \\
       CONV_TAC (RAND_CONV (REWRITE_CONV [sortCompileTheory.config_def] THENC EVAL)) \\
       EVAL_TAC)
    >- rfs [REL_def, get_mem_word_word_at_addr]
    \\ fs [halt_inv_def, REL_def]) \\
 strip_tac \\

 drule_strip computer_Next_relM_run \\ pop_assum (qspec_then `m1 + m` strip_assume_tac) \\
 fs [REL_def, is_halted_def, ag32_machine_configTheory.ag32_machine_config_def] \\

 (* Overkill: *)
 lift_stdout_tac sort_extract_writes_stdout);

val sort_ag32_next_verilog = Q.store_thm("sort_ag32_next_verilog",
 `!vstep fext ms input.
   vstep = verilog_sem fext computer ms ∧

   STRLEN input ≤ stdin_size ∧
   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) ([strlit "sort"], input) ms fext
   ⇒
   ?output. ?k1. !k. k1 ≤ k ==> ?fin.
    sort_spec input output /\
    vstep k = INR fin /\
    let stdout = extract_writes 1 (MAP get_ag32_io_event (fext k).io_events);
    in
      is_halted (code, data, config) fin ∧
      stdout ≼ output ∧
      (exit_code_0 fin ⇒ stdout = output)`,
 rewrite_tac [sort_spec_def] \\
 metis_tac [sort_ag32_next_verilog_lem, sort_extract_writes_stdout]);

val _ = export_theory ();
