open hardwarePreamble;

open wordcountProofTheory;

open commonVerilogProofLib;

val _ = new_theory "wordcountVerilogProof";

(* Temporary *)
val wc_spec_def = Define`
  wc_spec input output <=>
      output = explode (
        (concat [mlnum$toString (LENGTH (TOKENS isSpace input)); strlit " ";
                 mlnum$toString (LENGTH (splitlines input)); strlit "\n"]))`;

val wordcount_ag32_next_verilog = Q.prove(
 `!vstep fext ms input.
   vstep = verilog_sem fext computer ms ∧

   STRLEN input ≤ stdin_size ∧
   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) ([strlit "wordcount"], input) ms fext
   ⇒
   ?output. wc_spec input output ∧
   ?k1. !k. k1 ≤ k ==>
    ?fin. vstep k = INR fin /\
    let stdout = extract_writes 1 (MAP get_ag32_io_event (fext k).io_events)
    in
      is_halted fin (code, data, config) ∧
      stdout ≼ output ∧
      (exit_code_0 fin ⇒ stdout = output)`,
 rewrite_tac [wc_spec_def] \\
 lift_tac wordcount_ag32_next
          wordcountCompileTheory.config_def \\
 lift_stdout_tac wordcount_extract_writes_stdout);

val _ = save_thm("wordcount_ag32_next_verilog",
  wordcount_ag32_next_verilog |> REWRITE_RULE [LET_THM] |> BETA_RULE);

val _ = export_theory ();
