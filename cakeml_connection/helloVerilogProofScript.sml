open hardwarePreamble;

open helloProofTheory;

open commonVerilogProofLib;

val _ = new_theory "helloVerilogProof";

val hello_ag32_next_verilog = Q.store_thm("hello_ag32_next_verilog",
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
        outs_stdout_spec = "Hello World!\n"
    in
      ag32_is_halted fin hello_machine_config ∧
      outs_stdout ≼ outs_stdout_spec ∧
      (exit_code_0 fin (fextv k) ⇒ outs_stdout = outs_stdout_spec)`,
 lift_tac hello_ag32_next
          hello_extract_writes_stdout
          helloCompileTheory.config_def);

val _ = export_theory ();
