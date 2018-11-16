open wordsLib; (* Must be loaded before readerProgProofTheory? Why? *)

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

val reader_ag32_next_verilog = Q.prove(
 `!vstep fext ms mem cl input.
   vstep = verilog_sem fext computer ms ∧

   reader_cl_ok cl ∧
   STRLEN input ≤ stdin_size ∧

   is_lab_env fext_accessor_verilog vstep fext ∧
   ag32_verilog_init (code, data, config) (cl, input) ms fext
   ⇒
   ?stdout stderr k1. !k. k1 ≤ k ==> ?fin.
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
 rewrite_tac [reader_cl_ok_def, reader_spec_def] \\
 (* Hack for now, use lift_tac later *)
 rewrite_tac [verilog_sem_def] \\ rpt gen_tac \\
 SELECT_ELIM_TAC \\ conj_asm1_tac >- metis_tac[lift_fext_exists] \\
 pop_assum strip_assume_tac \\

 rewrite_tac [ag32_verilog_init_def] \\ rpt strip_tac \\ last_x_assum kall_tac \\
 drule_strip (vars_has_type_append |> SPEC_ALL |> EQ_IMP_RULE |> fst |> SPEC_ALL) \\
(*
 rewrite_tac [ag32_verilog_init_def] \\ rpt strip_tac \\
 `mrun x computer ms = mrun x' computer ms` by metis_tac [lift_fext_unique] \\
 last_x_assum kall_tac \\ FULL_SIMP_TAC bool_ss [] \\ pop_assum kall_tac \\
 drule_strip (vars_has_type_append |> SPEC_ALL |> EQ_IMP_RULE |> fst |> SPEC_ALL) \\
*)

 (* Instantiate output etc. *) (* <-- modified *)
 simp [] \\
 qmatch_goalsub_abbrev_tac `pair_CASE res _` \\
 qexists_tac `case res of
               (Success (s,v11),refs) => explode (msg_success s refs.the_context)
               | _ => ""` \\
 qexists_tac `case res of
               (Failure (Fail e), _) => explode e
               | _ => ""` \\

 drule_strip relM_backwards \\
 drule_strip INIT_backwards \\
 qmatch_asmsub_abbrev_tac `INIT _ _ s'` \\

 (* modified: *)
 drule_strip (reader_ag32_next |> GEN_ALL) \\

 disch_then (qspec_then `s'` mp_tac) \\
 impl_tac >- (qunabbrev_tac `s'` \\ simp [ag32_targetTheory.is_ag32_init_state_def]) \\

 strip_tac \\
 first_x_assum(qspec_then`k1`mp_tac) \\
 impl_tac >- simp[] \\ strip_tac \\

 drule_strip (SIMP_RULE (srw_ss()) [] INIT_REL_circuit_verilog) \\
 pop_assum(qspec_then`k1`strip_assume_tac) \\
 qexists_tac `m` \\ rpt strip_tac' \\

 fs [is_lab_env_def] \\
 drule_strip is_mem_verilog \\
 drule_strip is_interrupt_interface_verilog \\
 drule_strip (SIMP_RULE (srw_ss()) [] circuit_halt_compute_step_full_actual') \\
 fs [arithmeticTheory.LESS_EQ_EXISTS] \\
 qmatch_assum_rename_tac `k = m + m1` \\ rveq \\
 disch_then (qspecl_then [`m`, `m1`] mp_tac) \\ impl_tac
 >- (rpt conj_tac
    >- (fs [REL_def] \\
       CONV_TAC (RAND_CONV (REWRITE_CONV [readerCompileTheory.config_def] THENC EVAL)) \\
       EVAL_TAC)
    >- rfs [REL_def, get_mem_word_word_at_addr]
    \\ fs [halt_inv_def, REL_def]) \\
 strip_tac \\

 drule_strip computer_Next_relM_run \\ pop_assum (qspec_then `m1 + m` strip_assume_tac) \\
 fs [REL_def, is_halted_def, ag32_machine_configTheory.ag32_machine_config_def] \\

(* lift_tac 2
          cake_ag32_next
          ag32BootstrapTheory.config_def \\*)

 (* End of lift_tac *)
 drule_strip (reader_extract_writes |> GEN_ALL) \\
 pop_assum (qspecl_then [`mem`, `input`] mp_tac) \\
 simp [] \\
 qunabbrev_tac `res` \\
 TOP_CASE_TAC \\ strip_tac \\
 rpt conj_tac

 >- (every_case_tac \\ fs [relM_def, relM_var_def, WORD_def])

 >- (fs [relM_def, relM_var_def, WORD_def])

 >- (every_case_tac \\ metis_tac [is_prefix_extract_writes])

 >- (every_case_tac \\ metis_tac [is_prefix_extract_writes])

 \\ strip_tac \\ rfs [] \\ drule_strip after_R_1w_lift \\ drule_first \\
    every_case_tac \\ fs [reader_extract_writes]);

val _ = save_thm("reader_ag32_next_verilog",
 reader_ag32_next_verilog |> REWRITE_RULE [LET_THM] |> BETA_RULE);

val _ = export_theory ();
