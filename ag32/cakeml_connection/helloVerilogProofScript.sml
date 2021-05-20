open hardwarePreamble;

open helloProofTheory;

open commonVerilogProofLib;

val _ = new_theory "helloVerilogProof";

val hello_spec_def = Define `
 wc_spec output <=> output = "Hello World!\n"`;

val hello_ag32_next_verilog_lem = Q.prove(
 `!vstep fext ms cl input.
   vstep = verilog_sem fext computer ms ∧

   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   wfcl cl ∧
   STRLEN input ≤ stdin_size ∧
   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) (cl, input) ms fext
   ⇒
   ?k1. !k. k1 ≤ k ==> ?fin.
    vstep k = INR fin /\
    let stdout = extract_writes 1 (MAP get_ag32_io_event (fext k).io_events);
        stdout_spec = extract_writes 1 (MAP get_output_io_event (hello_io_events cl (stdin_fs input)))
    in
      is_halted (code, data, config) fin ∧
      stdout ≼ stdout_spec ∧
      (exit_code_0 fin ⇒ stdout = stdout_spec)`,
 lift_tac hello_ag32_next
          helloCompileTheory.config_def \\
 lift_stdout_tac);

val hello_ag32_next_verilog = Q.store_thm("hello_ag32_next_verilog",
 `!vstep fext ms cl input.
   vstep = verilog_sem fext computer ms ∧

   SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
   wfcl cl ∧
   STRLEN input ≤ stdin_size ∧
   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) (cl, input) ms fext
   ⇒
   ?output. ?k1. !k. k1 ≤ k ==> ?fin.
    wc_spec output ∧
    vstep k = INR fin /\
    let stdout = extract_writes 1 (MAP get_ag32_io_event (fext k).io_events)
    in
      is_halted (code, data, config) fin ∧
      stdout ≼ output ∧
      (exit_code_0 fin ⇒ stdout = output)`,
 metis_tac [hello_ag32_next_verilog_lem, hello_spec_def, hello_extract_writes_stdout]);

val _ = export_theory ();
