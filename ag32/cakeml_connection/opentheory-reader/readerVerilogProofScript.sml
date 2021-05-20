open wordsLib; (* <-- must be loaded first (this is fixed in the latest HOL) *)

open hardwarePreamble;

open readerProgProofTheory;
(* For compilation: open readerProgProofTheory readerCompileTheory; *)

open commonVerilogProofLib;

val _ = new_theory "readerVerilogProof";

val _ = Parse.hide "mem";
val mem = ``mem:'U->'U-> bool``;
val _ = temp_overload_on ("reader", ``\inp r. readLines inp init_state r``);

val reader_spec_def = Define `
 reader_spec mem input cl stdout stderr <=>
  let refs = SND (init_reader () init_refs) in
   case reader (lines_of (implode input)) refs of
     (Failure (Fail e), refs) => (stdout = "") /\ (stderr = explode e)
   | (Success (s, _), refs) =>
      (is_set_theory ^mem ==>
       (!asl c. MEM (Sequent asl c) s.thms ==> (thyof refs.the_context, asl) |= c)) /\
     refs.the_context extends init_ctxt /\
     (stdout = explode (msg_success s refs.the_context)) /\ (stderr = "")
   | _ => F`;

val reader_cl_ok_def = Define `
 reader_cl_ok cl <=>
  wfcl cl ∧
  SUM (MAP strlen cl) + LENGTH cl ≤ cline_size ∧
  (LENGTH cl = 1)`;

val reader_ag32_next_verilog_lem = Q.prove(
 `!vstep fext ms mem cl input.
   vstep = verilog_sem fext computer ms ∧

   reader_cl_ok cl ∧
   STRLEN input ≤ stdin_size ∧

   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) (cl, input) ms fext
   ⇒
   ?k1. !k. k1 ≤ k ==> ?fin.
    vstep k = INR fin /\
    let events = MAP get_ag32_io_event (fext k).io_events;
        stdout = extract_writes 1 events;
        stderr = extract_writes 2 events;
        events_spec = MAP get_output_io_event (reader_io_events cl (stdin_fs input));
        stdout_spec = extract_writes 1 events_spec;
        stderr_spec = extract_writes 2 events_spec
    in
      is_halted (code, data, config) fin ∧
      stdout ≼ stdout_spec ∧
      stderr ≼ stderr_spec ∧
      (exit_code_0 fin ⇒
       stdout = stdout_spec ∧
       stderr = stderr_spec)`,
 rewrite_tac [reader_cl_ok_def] \\
 lift_tac reader_ag32_next
          readerCompileTheory.config_def \\
 lift_stdout_stderr_tac);

val reader_ag32_next_verilog_lem2 = Q.prove(
 `!vstep fext ms mem cl input.
   vstep = verilog_sem fext computer ms ∧

   reader_cl_ok cl ∧
   STRLEN input ≤ stdin_size ∧

   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) (cl, input) ms fext
   ⇒
   ?stdout stderr. ?k1. !k. k1 ≤ k ==> ?fin.
    reader_spec ^mem input cl stdout stderr /\
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
 metis_tac [reader_ag32_next_verilog_lem, reader_spec_def, reader_cl_ok_def,
            reader_extract_writes]);

val _ = save_thm("reader_ag32_next_verilog",
 reader_ag32_next_verilog_lem2 |> REWRITE_RULE [LET_THM] |> BETA_RULE);

val _ = export_theory ();
