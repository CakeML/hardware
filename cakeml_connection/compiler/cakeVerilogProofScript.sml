open hardwarePreamble;

open ag32BootstrapProofTheory;

open commonVerilogProofLib;

val _ = new_theory "cakeVerilogProof";

val cake_ag32_next_verilog = Q.store_thm("cake_ag32_next_verilog",
 `!vstep fext fextv init cl inp.
   vars_has_type init ag32_verilog_types ∧
   INIT_verilog (fext 0) init ∧

   vstep = mrun fextv computer init ∧

   is_lab_env fext_accessor_verilog vstep fext ∧
   (fext 0).mem = (init_memory code data (THE config.ffi_names) (cl, inp)) ∧
   lift_fext fextv fext ∧

   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   wfcl cl ∧
   STRLEN inp ≤ stdin_size
   ⇒
   ?k1.
    !k. k1 ≤ k ==>
    ?fin. vstep k = INR fin /\
    let outs = MAP get_ag32_io_event (fext k).io_events;
        outs_stdout = extract_writes 1 outs;
        outs_stderr = extract_writes 2 outs;
        (outs_stdout_spec, outs_stderr_spec) =
         if has_version_flag (TL cl) then
          (explode current_build_info_str, "")
         else
          let (cout, cerr) = compile_32 (TL cl) inp in
           (explode (concat (append cout)), explode cerr)
    in
      ag32_is_halted fin cake_machine_config ∧
      outs_stdout ≼ outs_stdout_spec ∧
      outs_stderr ≼ outs_stderr_spec ∧
      (exit_code_0 fin (fextv k) ⇒
       outs_stdout = outs_stdout_spec ∧
       outs_stderr = outs_stderr_spec)`,
 lift_tac cake_ag32_next
          ag32BootstrapTheory.config_def \\
 pairarg_tac \\ simp [] \\
 pairarg_tac \\ fs [] \\
 drule cake_extract_writes \\ simp [] \\ strip_tac \\
 rpt conj_tac

 >- fs [relM_def, relM_var_def, WORD_def]

 >- (every_case_tac \\ metis_tac [is_prefix_extract_writes])

 >- (every_case_tac \\ metis_tac [is_prefix_extract_writes])

 \\ strip_tac \\ rfs [] \\ drule_strip after_R_1w_lift \\ drule_first \\
    every_case_tac \\ fs [cake_extract_writes]);

val _ = export_theory ();
