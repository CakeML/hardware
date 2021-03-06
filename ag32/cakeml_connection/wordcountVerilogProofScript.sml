open hardwarePreamble;

open wordcountProofTheory;

open commonVerilogProofLib;

val _ = new_theory "wordcountVerilogProof";

val wc_spec_def = Define`
  wc_spec input output <=>
      output = explode (
        (concat [toString (LENGTH (TOKENS isSpace input)); strlit " ";
                 toString (LENGTH (splitlines input)); strlit "\n"]))`;

val wordcount_ag32_next_verilog_lem = Q.prove(
 `!vstep fext ms input.
   vstep = verilog_sem fext computer ms ∧

   STRLEN input ≤ stdin_size ∧
   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) ([strlit "wordcount"], input) ms fext
   ⇒
   ?k1. !k. k1 ≤ k ==> ?fin.
    vstep k = INR fin ∧
    let stdout = extract_writes 1 (MAP get_ag32_io_event (fext k).io_events);
        stdout_spec = extract_writes 1 (MAP get_output_io_event (wordcount_io_events input))
    in
      is_halted (code, data, config) fin ∧
      stdout ≼ stdout_spec ∧
      (exit_code_0 fin ⇒ stdout = stdout_spec)`,
 lift_tac wordcount_ag32_next
          wordcountCompileTheory.config_def \\
 lift_stdout_tac);

val wordcount_ag32_next_verilog_lem2 = Q.prove(
 `!vstep fext ms input.
   vstep = verilog_sem fext computer ms ∧

   STRLEN input ≤ stdin_size ∧
   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) ([strlit "wordcount"], input) ms fext
   ⇒
   ?output. ?k1. !k. k1 ≤ k ==> ?fin.
    wc_spec input output /\
    vstep k = INR fin /\
    let stdout = extract_writes 1 (MAP get_ag32_io_event (fext k).io_events)
    in
      is_halted (code, data, config) fin ∧
      stdout ≼ output ∧
      (exit_code_0 fin ⇒ stdout = output)`,
 metis_tac [wordcount_ag32_next_verilog_lem, wc_spec_def, wordcount_extract_writes_stdout]);

val _ = save_thm("wordcount_ag32_next_verilog",
  wordcount_ag32_next_verilog_lem2 |> REWRITE_RULE [LET_THM] |> BETA_RULE);

val _ = export_theory ();
