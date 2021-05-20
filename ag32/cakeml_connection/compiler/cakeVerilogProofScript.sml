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

val cl_ok_def = Define `
 cl_ok cl <=>
  SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
  wfcl cl`;

val cake_ag32_next_verilog_lem = Q.prove(
 `!vstep fext ms cl input.
   vstep = verilog_sem fext computer ms ∧

   cl_ok cl ∧
   STRLEN input ≤ stdin_size ∧

   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) (cl, input) ms fext
   ⇒
   ?k1. !k. k1 ≤ k ==> ?fin.
    vstep k = INR fin /\
    let events = MAP get_ag32_io_event (fext k).io_events;
	stdout = extract_writes 1 events;
	stderr = extract_writes 2 events;
	events_spec = MAP get_output_io_event (cake_io_events cl (stdin_fs input));
	stdout_spec = extract_writes 1 events_spec;
	stderr_spec = extract_writes 2 events_spec
    in
      is_halted (code, data, config) fin ∧
      stdout ≼ stdout_spec ∧
      stderr ≼ stderr_spec ∧
      (exit_code_0 fin ⇒
       stdout = stdout_spec ∧
       stderr = stderr_spec)`,
 rewrite_tac [cl_ok_def] \\
 lift_tac cake_ag32_next
	  ag32BootstrapTheory.config_def \\
 lift_stdout_stderr_tac);

val cake_ag32_next_verilog_lem2 = Q.prove(
 `!vstep fext ms cl input.
   vstep = verilog_sem fext computer ms ∧

   cl_ok cl ∧
   STRLEN input ≤ stdin_size ∧

   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) (cl, input) ms fext
   ⇒
   ?stdout stderr. ?k1. !k. k1 ≤ k ==> ?fin.
    compiler_spec input cl stdout stderr /\
    vstep k = INR fin /\
    let outs = MAP get_ag32_io_event (fext k).io_events;
	outs_stdout = extract_writes 1 outs;
	outs_stderr = extract_writes 2 outs
    in
      is_halted (code, data, config) fin ∧
      outs_stdout ≼ stdout ∧
      outs_stderr ≼ stderr ∧
      (exit_code_0 fin ⇒
       outs_stdout = stdout ∧
       outs_stderr = stderr)`,
 rewrite_tac [compiler_spec_def] \\ rpt strip_tac \\
 `wfcl cl` by fs [cl_ok_def] \\
 drule_strip (cake_extract_writes |> GEN_ALL) \\
 pop_assum (qspec_then `input` assume_tac) \\
 IF_CASES_TAC >- metis_tac [cake_ag32_next_verilog_lem] \\
 fs [] \\ pairarg_tac \\ fs [] \\
 metis_tac [cake_ag32_next_verilog_lem]);

val _ = save_thm("cake_ag32_next_verilog",
 cake_ag32_next_verilog_lem2 |> REWRITE_RULE [LET_THM] |> BETA_RULE);

val _ = export_theory ();
