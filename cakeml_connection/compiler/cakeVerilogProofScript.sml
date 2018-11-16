open hardwarePreamble;

open ag32BootstrapProofTheory;

open commonVerilogProofLib;

val _ = new_theory "cakeVerilogProof";

val compiler_spec_def = Define `
 compiler_spec input cl stdout stderr <=>
  (stdout, stderr) =
   if has_version_flag (TL cl) then
    (explode current_build_info_str, "")
   else
    let (cout, cerr) = compile_32 (TL cl) input in
        (explode (concat (append cout)), explode cerr)`;

val compiler_spec_alt = Q.prove(
 `!input cl stdout stderr.
   compiler_spec input cl stdout stderr <=>
   (stdout =
   if has_version_flag (TL cl) then
    explode current_build_info_str
   else
    explode (concat (append (FST (compile_32 (TL cl) input))))) /\
   (stderr =
   if has_version_flag (TL cl) then
    ""
   else
    explode (SND (compile_32 (TL cl) input)))`,
 rw [compiler_spec_def] \\ pairarg_tac \\ fs []);

val cl_ok_def = Define `
 cl_ok cl <=>
  SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
  wfcl cl`;

val cake_ag32_next_verilog = Q.prove(
 `!vstep fext ms cl input.
   vstep = verilog_sem fext computer ms ∧

   cl_ok cl ∧
   STRLEN input ≤ stdin_size ∧

   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) (cl, input) ms fext
   ⇒
   ?stdout stderr k1. !k. k1 ≤ k ==> ?fin.
    compiler_spec input cl stdout stderr /\
    vstep k = INR fin /\
    let outs = MAP get_ag32_io_event (fext k).io_events;
        outs_stdout = extract_writes 1 outs;
        outs_stderr = extract_writes 2 outs
    in
      is_halted fin (code, data, config) ∧
      outs_stdout ≼ stdout ∧
      outs_stderr ≼ stderr ∧
      (exit_code_0 fin ⇒
       outs_stdout = stdout ∧
       outs_stderr = stderr)`,
 rewrite_tac [cl_ok_def, compiler_spec_alt] \\
 lift_tac 2
          cake_ag32_next
          ag32BootstrapTheory.config_def \\

 drule (cake_extract_writes |> GEN_ALL) \\
 disch_then (qspec_then `input` mp_tac) \\
 simp [] \\
 pairarg_tac \\ simp [] \\ strip_tac \\
 rpt conj_tac

 >- fs [relM_def, relM_var_def, WORD_def]

 >- (every_case_tac \\ metis_tac [is_prefix_extract_writes])

 >- (every_case_tac \\ metis_tac [is_prefix_extract_writes])

 \\ strip_tac \\ rfs [] \\ drule_strip after_R_1w_lift \\ drule_first \\
    every_case_tac \\ fs [cake_extract_writes]);

val _ = save_thm("cake_ag32_next_verilog",
 cake_ag32_next_verilog |> REWRITE_RULE [LET_THM] |> BETA_RULE);

val _ = export_theory ();
