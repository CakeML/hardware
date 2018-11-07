open hardwarePreamble;

open helloProofTheory;

open verilogTypeTheory moduleTranslatorTheory;
open ag32MachineTheory ag32EqTheory ag32VerilogTheory;

open commonVerilogProofTheory;

val _ = new_theory "helloVerilogProof";

val _ = guess_lengths ();
val _ = prefer_num ();

val hello_ag32_next_verilog = Q.store_thm("hello_ag32_next_verilog",
 `!vstep fext fextv init cl inp.
   vars_has_type init ag32_verilog_types ∧
   INIT_verilog (fext 0) init ∧

   vstep = mrun fextv computer init ∧

   is_lab_env fext_accessor_verilog vstep fext ∧
   (fext 0).mem = (hello_init_memory (cl, inp)) ∧
   lift_fext fextv fext ∧

   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   wfcl cl ∧
   STRLEN inp ≤ stdin_size
   ⇒
   ?k fin.
    vstep k = INR fin /\
    let outs = MAP get_ag32_io_event (fext k).io_events;
        outs_spec = MAP get_output_io_event (hello_io_events cl (stdin_fs inp)) in
      ag32_is_halted fin hello_machine_config ∧
      outs ≼ outs_spec ∧
      (exit_code_0 fin (fextv k) ⇒ (outs = outs_spec))`,
 rewrite_tac[ag32_verilog_types_def] \\
 rpt strip_tac \\
 drule_strip (vars_has_type_append |> SPEC_ALL |> EQ_IMP_RULE |> fst |> SPEC_ALL) \\

 drule_strip relM_backwards \\
 drule_strip INIT_backwards \\
 qmatch_asmsub_abbrev_tac `INIT _ _ s'` \\

 drule_strip (hello_ag32_next |> GEN_ALL) \\

 disch_then (qspec_then `s'` mp_tac) \\
 impl_tac >- (qunabbrev_tac `s'` \\ simp [ag32_targetTheory.is_ag32_init_state_def]) \\

 strip_tac \\
 first_x_assum(qspec_then`k1`mp_tac) \\
 impl_tac >- simp[] \\ strip_tac \\

 drule_strip (SIMP_RULE (srw_ss()) [] INIT_REL_circuit_verilog) \\
 pop_assum(qspec_then`k1`strip_assume_tac) \\
 asm_exists_tac \\
 fs [REL_def, ag32_is_halted_def, hello_machine_config_def,
     ag32_machine_configTheory.ag32_machine_config_def] \\ conj_tac

 >- fs [relM_def, relM_var_def, WORD_def]

 \\ strip_tac \\ drule_strip after_R_lift \\ drule_first);

val _ = export_theory ();
