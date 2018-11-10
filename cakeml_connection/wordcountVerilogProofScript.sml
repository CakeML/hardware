open hardwarePreamble;

open wordcountProofTheory;

open verilogTypeTheory moduleTranslatorTheory;
open ag32MachineTheory ag32EqTheory ag32HaltTheory ag32VerilogTheory;

open commonVerilogProofTheory;

val _ = new_theory "wordcountVerilogProof";

val _ = guess_lengths ();
val _ = prefer_num ();

val get_mem_word_word_at_addr = Q.store_thm("get_mem_word_word_at_addr",
 `!mem addr. get_mem_word mem addr = word_at_addr mem addr`,
 rw [word_at_addr_def, ag32_memoryTheory.get_mem_word_def]);

val wordcount_ag32_next_verilog = Q.store_thm("wordcount_ag32_next_verilog",
 `!vstep fext fextv init inp.
   vars_has_type init ag32_verilog_types ∧
   INIT_verilog (fext 0) init ∧

   vstep = mrun fextv computer init ∧

   is_lab_env fext_accessor_verilog vstep fext ∧
   (fext 0).mem = (init_memory code data (THE config.ffi_names) ([strlit "wordcount"], inp)) ∧
   lift_fext fextv fext ∧

   STRLEN inp ≤ stdin_size
   ⇒
   ?k1. !k. k1 ≤ k ==>
    ?fin. vstep k = INR fin /\
    let outs = MAP get_ag32_io_event (fext k).io_events;
        outs_spec = MAP get_output_io_event (wordcount_io_events inp) in
      ag32_is_halted fin wordcount_machine_config ∧
      outs ≼ outs_spec ∧
      (exit_code_0 fin (fextv k) ⇒ (outs = outs_spec))`,
 rewrite_tac[ag32_verilog_types_def] \\
 rpt strip_tac \\
 drule_strip (vars_has_type_append |> SPEC_ALL |> EQ_IMP_RULE |> fst |> SPEC_ALL) \\

 drule_strip relM_backwards \\
 drule_strip INIT_backwards \\
 qmatch_asmsub_abbrev_tac `INIT _ _ s'` \\

 drule_strip (wordcount_ag32_next |> GEN_ALL) \\

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
 fs [arithmeticTheory.LESS_EQ_EXISTS] \\ rveq \\
 disch_then (qspecl_then [`m`, `p'`] mp_tac) \\ impl_tac
 >- (rpt conj_tac
    >- (fs [REL_def] \\ EVAL_TAC \\ simp [wordcountCompileTheory.config_def])
    >- rfs [REL_def, get_mem_word_word_at_addr]
    >- fs [halt_inv_def, REL_def]) \\
 strip_tac \\

 drule_strip computer_Next_relM_run \\ pop_assum (qspec_then `p' + m` strip_assume_tac) \\
 fs [REL_def, ag32_is_halted_def, ag32_machine_configTheory.ag32_machine_config_def] \\ conj_tac

 >- fs [relM_def, relM_var_def, WORD_def]

 \\ strip_tac \\ rfs [] \\ drule_strip after_R_1w_lift \\ drule_first);

val is_prefix_extract_writes = Q.store_thm("is_prefix_extract_writes",
 `!l1 l2 fd. l1 ≼ l2 ==> extract_writes fd l1 ≼ extract_writes fd l2`,
 Induct >- rw [ag32_basis_ffiProofTheory.extract_writes_def] \\

 rw [] \\ every_case_tac \\ fs [] \\
 rveq \\ first_x_assum drule \\ disch_then (qspec_then `fd` assume_tac) \\
 fs [ag32_basis_ffiProofTheory.extract_writes_def] \\ rw []);

val wordcount_ag32_next_verilog_prettier = Q.store_thm("wordcount_ag32_next_verilog_prettier",
 `!vstep fext fextv init inp.
   vars_has_type init ag32_verilog_types ∧
   INIT_verilog (fext 0) init ∧

   vstep = mrun fextv computer init ∧

   is_lab_env fext_accessor_verilog vstep fext ∧
   (fext 0).mem = (init_memory code data (THE config.ffi_names) ([strlit "wordcount"], inp)) ∧
   lift_fext fextv fext ∧

   STRLEN inp ≤ stdin_size
   ⇒
   ?k1.
    !k. k1 ≤ k ==>
    ?fin. vstep k = INR fin /\
    let outs = MAP get_ag32_io_event (fext k).io_events;
        outs_stdout = extract_writes 1 outs;
        outs_stdout_spec = explode (concat
                             [toString (LENGTH (TOKENS isSpace inp)); strlit " ";
                              toString (LENGTH (splitlines inp)); strlit "\n"])
    in
      ag32_is_halted fin wordcount_machine_config ∧
      outs_stdout ≼ outs_stdout_spec ∧
      (exit_code_0 fin (fextv k) ⇒
       outs_stdout = outs_stdout_spec)`,
 metis_tac [wordcount_ag32_next_verilog,
            wordcount_extract_writes_stdout,
            is_prefix_extract_writes]);

val _ = export_theory ();
