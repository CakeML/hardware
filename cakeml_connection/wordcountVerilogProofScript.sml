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

val ag32_verilog_init_def = Define `
 ag32_verilog_init (code, data, config') (cl, input) init fext fextv <=>
  lift_fext fextv fext /\
  (fext 0).mem = (init_memory code data (THE config'.ffi_names) (cl, input)) /\
  vars_has_type init (relMtypes ++ ag32types) /\
  INIT_verilog (fext 0) init`;

val wordcount_ag32_next_verilog = Q.prove(
 `!vstep fext fextv ms input output.
   vstep = mrun fextv computer ms ∧

   STRLEN input ≤ stdin_size ∧
   wc_spec input output ∧
   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) ([strlit "wordcount"], input) ms fext fextv
   ⇒
   ?k1. !k. k1 ≤ k ==>
    ?fin. vstep k = INR fin /\
    let stdout = extract_writes 1 (MAP get_ag32_io_event (fext k).io_events)
    in
      is_halted fin (code, data, config) ∧
      stdout ≼ output ∧
      (exit_code_0 fin (fextv k) ⇒ stdout = output)`,
 cheat);

val _ = save_thm("wordcount_ag32_next_verilog",
  wordcount_ag32_next_verilog |> REWRITE_RULE [LET_THM] |> BETA_RULE);

(*
 lift_tac wordcount_ag32_next
          wordcountCompileTheory.config_def \\
 lift_stdout_tac wordcount_extract_writes_stdout);
*)

val _ = export_theory ();
