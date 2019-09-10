open hardwarePreamble;

open moduleTranslatorTheory;
open verilogTranslatorLib verilogLiftLib;
open verilogPrintLib;

open ledExampleTheory;

val _ = new_theory "ledExampleVerilog";

(*

 Step 1: Invoke translator

 *)

val blink_led_trans = hol2hardware_step_function blink_led_def;
val prog_def = blink_led_trans |> concl |> EvalS_get_prog;
val prog_def = Define `prog = ^prog_def`;
val blink_led_trans = REWRITE_RULE [GSYM prog_def] blink_led_trans;

(*

 Step 2: Massage output from translator to more readable form: A module consisting of a single process

 (For more complex programs we would merge multiple processes into one module in this step.)

 This step is currently very ugly and requires copy-and-pasting the following proofs... this can be automated.

 *)

Theorem prog_step_relM:
 !n init vs ps fextv fext.
 relM (circuit init n) vs /\ (* more than needed here: *) lift_fext fextv fext
 ==>
 ?vs'. mstep_commit (fextv n) [prog] vs = INR vs' /\
       relM (circuit init (SUC n)) vs'
Proof
 rw [lift_fext_relS_fextv_fext, mstep_commit_def, mstep_def, sum_foldM_def] \\
 first_x_assum (qspec_then `n` assume_tac) \\
 drule_strip relM_relS \\
 drule_strip (blink_led_trans |> REWRITE_RULE [EvalS_def] |> GEN_ALL) \\

 (* Ad-hoc hack instead of using main lifting thm, as we only have one process: *)
 drule vnwrites_nil_correct \\ impl_tac >- EVAL_TAC \\ strip_tac \\
 fs [sum_bind_def, sum_map_def, circuit_def,
     relS_def, relM_def, relS_var_def, relM_var_def, mget_var_get_var]
QED

Theorem prog_step_relM_run:
 !n fextv fext init vs.
 relM init vs /\ lift_fext fextv fext
 ==>
 ?vs'. mrun fextv [prog] vs n = INR vs' /\
       relM (circuit init n) vs'
Proof
 rpt strip_tac \\ match_mp_tac mstep_commit_mrun \\ qexists_tac `[]` \\ rpt conj_tac
 >- simp [circuit_def]
 >- simp [vars_has_type_def]
 \\ rpt strip_tac \\ match_mp_tac prog_step_relM \\ rpt (asm_exists_tac \\ simp [])
QED

(*

 Step 3: Lift correctness property to Verilog level

 Also here more automation possible needed...

 *)

(* More copy-paste boilerplate... can be generated automatically (everything done by "relM_backwards_tac") *)
Theorem relM_backwards:
 !vs. vars_has_type vs relMtypes ==> ?hol_s. relM hol_s vs
Proof
 simp [vars_has_type_def, relMtypes_def, relM_def, relM_var_def, mget_var_ALOOKUP] \\ rpt gen_tac \\
 relM_backwards_tac
QED

(* Actual lifting of correctness property: *)
Theorem circuit_correct_verilog:
 !fextv fext init.
 lift_fext fextv fext /\
 vars_has_type init relMtypes ==>
 ?n vs' count.
  mrun fextv [prog] init n = INR vs' /\
  mget_var vs' "count" = INR (w2ver count) /\ (42w:word8) <=+ count
Proof
 rpt strip_tac \\
 drule_strip relM_backwards \\
 qspec_then `hol_s` strip_assume_tac circuit_correct \\
 drule_strip prog_step_relM_run \\ first_x_assum (qspec_then `n` strip_assume_tac) \\
 
 asm_exists_tac \\ fs [relM_def, relM_var_def, WORD_def] \\ (* ugly instantiation: *) metis_tac []
QED

(*

 Step 4: Print Verilog code for synthesis...

 This does not print module boilerplate, only the code for the single process the module consist of

 *)

val prog_code = prog_def |> concl |> rhs |> vprog_print;

(*

Wrap in boilerplate etc.:

print "always_ff @ (posedge clk) begin\n";
print prog_code;
print "end\n";

*)

val _ = export_theory ();
