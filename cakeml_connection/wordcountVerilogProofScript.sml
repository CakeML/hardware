open hardwarePreamble;

open wordcountProofTheory;

open commonVerilogProofLib;

val _ = new_theory "wordcountVerilogProof";

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
      (exit_code_0 fin (fextv k) ⇒ outs_stdout = outs_stdout_spec)`,
 lift_tac wordcount_ag32_next
          wordcount_extract_writes_stdout
          wordcountCompileTheory.config_def);

val _ = export_theory ();
