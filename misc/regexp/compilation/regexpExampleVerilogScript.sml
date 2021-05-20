open hardwarePreamble;

open verilogTranslatorLib moduleTranslatorTheory;
open verilogTranslatorConfigLib verilogLiftLib;

open regexpExampleTheory;

val _ = new_theory "regexpExampleVerilog";

val _ = guess_lengths ();
val _ = prefer_num ();

(* Main process *)
val trans = hol2hardware_step_function regexp_def;
val prog_def = EvalS_get_prog (trans |> concl);
val regexpv_def = Define `regexpv = ^prog_def`;
val trans = REWRITE_RULE [GSYM regexpv_def] trans;

(* Ad-hoc lifting as we only have one process and no non-blocking writes *)
val regexp_step_relM = Q.store_thm("regexp_step_relM",
 `!n fext fextv init vs ps.
  (* Simulation step *)
  relM (circuit init fext n) vs /\ lift_fext fextv fext
  ==>
  ?vs'. mstep_commit (fextv n) [regexpv] vs = INR vs' /\
        relM (circuit init fext (SUC n)) vs'`,
 rewrite_tac [lift_fext_relS_fextv_fext] \\
 rw [mstep_commit_def, mstep_def, sum_foldM_def] \\
 first_x_assum (qspec_then `n` assume_tac) \\
 drule_strip relM_relS \\
 drule_strip (trans |> REWRITE_RULE [EvalS_def] |> GEN_ALL) \\

 drule vnwrites_nil_correct \\ impl_tac >- EVAL_TAC \\ strip_tac \\
 fs [sum_bind_def, sum_map_def, circuit_def] \\
 fs [relS_def, relM_def, relS_var_def, relM_var_def, mget_var_get_var]);

val regexp_step_relM_run = Q.store_thm("regexp_step_relM_run",
 `!n fextv fext init vs.
  relM init vs /\ lift_fext fextv fext
  ==>
  ?vs'. mrun fextv [regexpv] vs n = INR vs' /\
        relM (circuit init fext n) vs'`,
 rpt strip_tac \\ match_mp_tac mstep_commit_mrun \\ qexists_tac `[]` \\ rpt conj_tac
 >- simp [circuit_def]
 >- simp [vars_has_type_def]
 \\ rpt strip_tac \\ match_mp_tac regexp_step_relM \\ simp []);

(* circuit_correct_regexp *)

val INIT_verilog_def = Define `
 INIT_verilog env <=>
  (* Machine implementation registers *)
  WORD (0w:word4) (THE (ALOOKUP env "state")) /\
  WORD (0w:word4) (THE (ALOOKUP env "state_start")) /\

  WORD_ARRAY BOOL (hwfinal : word4 -> bool) (THE (ALOOKUP env "state_is_final")) /\
  (WORD_ARRAY (WORD_ARRAY WORD)) (hwtable : word4 -> word8 -> word4) (THE (ALOOKUP env "next_state_info"))`;

val relM_backwards = Q.store_thm("relM_backwards",
 `!vs. vars_has_type vs relMtypes ==> ?hol_s. relM hol_s vs`,
 simp [vars_has_type_def, relMtypes_def, relM_def, relM_var_def, mget_var_ALOOKUP] \\ rpt gen_tac \\

 relM_backwards_tac);

val INIT_backwards = Q.store_thm("INIT_backwards",
 `!hol_s init.
   relM hol_s init /\
   INIT_verilog init ==>
   INIT hol_s`,
 rw [INIT_verilog_def, relM_def, relM_var_def, mget_var_def] \\
 every_case_tac \\ fs [] \\ rveq \\
 simp [INIT_def] \\
 metis_tac [WORD_eq, WORD_ARRAY_BOOL_eq, WORD_ARRAY_WORD_ARRAY_WORD_eq]);

val circuit_correct_regexp_verilog = Q.store_thm("circuit_correct_regexp_verilog",
 `!n m init fext fextv.
  lift_fext fextv fext /\

  vars_has_type init relMtypes /\
  INIT_verilog init /\

  (fext n).new_package /\
  (∀p. p ≤ m ⇒ ¬(fext (n + p)).new_package)
  ==>
  ?vs'.
   mrun fextv [regexpv] init (SUC (n + m)) = INR vs' /\
   mget_var vs' "accept" = INR (VBool (regexp_lang foobar_regex (str_of_ext fext (n + 1) m)))`,
 rpt strip_tac \\
 drule_strip relM_backwards \\
 drule_strip INIT_backwards \\
 drule_strip regexp_step_relM_run \\
 first_x_assum (qspec_then `SUC (n + m)` strip_assume_tac) \\
 simp [] \\

 fs [relM_def, relM_var_def, BOOL_def] \\
 drule_strip circuit_correct_regexp \\
 fs []);

val _ = export_theory ();
