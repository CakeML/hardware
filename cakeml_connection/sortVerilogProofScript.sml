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
 lift_tac sort_ag32_next
          sortCompileTheory.config_def \\
 lift_stdout_tac);

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
 metis_tac [sort_ag32_next_verilog_lem, sort_spec_def, sort_extract_writes_stdout]);

val _ = export_theory ();
