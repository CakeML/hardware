open hardwarePreamble;

open moduleTranslatorTheory;

open verilogTranslatorLib verilogLiftLib;
open circuitExampleTheory;

val _ = new_theory "circuitExampleVerilog";

val _ = prefer_num ();

(* TODO: Duplication *)
fun intro_cvars_for_prog prog =
  list_mk_comb (``intro_cvars``, [``cvars``, prog])
  |> computeLib.RESTR_EVAL_CONV (append (decls "n2ver") (decls "w2ver"))
  |> concl |> rhs;

val cvars_def = Define `cvars = ["count"]`;

val A_trans = hol2hardware_step_function A_def;
val Av_def = A_trans |> concl |> EvalS_get_prog;
val Av_def = Define `Av = ^Av_def`;
val A_trans = REWRITE_RULE [GSYM Av_def] A_trans;

val B_trans = hol2hardware_step_function B_def;
val Bv_def = B_trans |> concl |> EvalS_get_prog;
val Bv_def = Define `Bv = ^Bv_def`;
val B_trans = REWRITE_RULE [GSYM Bv_def] B_trans;

val ABv_def = Define `
 ABv = MAP (intro_cvars cvars) [Av; Bv]`;

val prg_to_trans = [A_trans, B_trans]
 |> map (fn t => (t |> concl |> rator |> rand |> strip_comb |> fst, (t |> concl |> rand, t |> GEN_ALL)));

fun mget_var_init_tac (g as (tms, tm)) = let
  val (mget_var_tm, pred_tm) = tm |> boolSyntax.dest_exists |> snd |> dest_conj
  val prg = pred_tm |> rator |> rand |> rand |> strip_comb |> fst
  val var = mget_var_tm |> lhs |> rand
  val res = lookup prg prg_to_trans
in
  (first_x_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [] o SPEC (fst res)) \\
  pop_assum (mp_tac o (CONV_RULE (LAND_CONV EVAL)) o SPEC var)) g
end;

val AB_mstep_commit = Q.store_thm("AB_mstep_commit",
 `!n fext fextv init vs ps.
  relM (AB fext init n) vs /\ lift_fext fextv fext
  ==>
  ?vs'. mstep_commit (fextv n) ABv vs = INR vs' /\
        relM (AB fext init (SUC n)) vs'`,
 rewrite_tac [lift_fext_relS_fextv_fext, ABv_def] \\ rpt strip_tac \\
 first_x_assum (qspec_then `n` assume_tac) \\
 qspecl_then [`cvars`, `fext n`, `[Av; Bv]`, `fextv n`, `vs`, `AB fext init n`, `K T`] mp_tac mstep_commit_lift_EvalSs \\ impl_tac
 >- (rpt conj_tac
  >- EVAL_TAC
  >- (rpt strip_tac >- (fs [] \\ metis_tac [A_trans, B_trans]) \\ fs [] \\ EVAL_TAC)
  >- EVAL_TAC
  >- simp []
  >- simp []
  >- (EVAL_TAC \\ rpt gen_tac \\ strip_tac \\ rveq \\ EVAL_TAC \\ rw [])) \\

 strip_tac \\ simp [] \\

 drule_strip relM_relS \\
 drule_strip (A_trans |> DISCH_ALL |> REWRITE_RULE [EvalS_def] |> GEN_ALL) \\
 drule_strip (B_trans |> DISCH_ALL |> REWRITE_RULE [EvalS_def] |> GEN_ALL) \\

 rw [relM_def, relM_var_def, AB_def] \\

 mget_var_init_tac \\ fs [relS_def, relS_var_def]);

val AB_mrun = Q.store_thm("AB_mrun",
 `!n fextv fext init vs.
  relM init vs /\ lift_fext fextv fext
  ==>
  ?vs'. mrun fextv ABv vs n = INR vs' /\ relM (AB fext init n) vs'`,
 rpt strip_tac \\ match_mp_tac mstep_commit_mrun \\ qexists_tac `[]` \\ rpt conj_tac
 >- simp [AB_def]
 >- simp [vars_has_type_def]
 \\ rpt strip_tac \\ match_mp_tac AB_mstep_commit \\ simp []);

(* Just a prettier name for the paper *)
val ABtypes_def = Define `
 ABtypes = relMtypes`;

val relM_backwards = Q.prove(
 `!vs. vars_has_type vs ABtypes ==> ?init. relM init vs`,
 simp [vars_has_type_def, ABtypes_def, relMtypes_def, relM_def, relM_var_def, mget_var_ALOOKUP] \\

 rpt gen_tac \\ relM_backwards_tac);

(* Lift pulse_spec to Verilog level *)

val pulse_spec_verilog_def = Define `
 pulse_spec_verilog fext <=>
  (!n. ?m. (fext (n + m)) "pulse" = INR (VBool T)) /\
  (!n. ?b. (fext n) "pulse" = INR (VBool b)) /\
  (!n var. var <> "pulse" ==> (fext n) var = INL UnknownVariable)`;

val pulse_spec_verilog_to_pulse_spec_def = Define `
 pulse_spec_verilog_to_pulse_spec fextv n = <| pulse := ((fextv n) "pulse" = INR (VBool T)) |>`;

val pulse_spec_verilog_backwards = Q.prove(
 `!fextv. pulse_spec_verilog fextv ==> ?fext. pulse_spec fext /\ lift_fext fextv fext`,
 rw [pulse_spec_verilog_def, pulse_spec_def, lift_fext_def] \\
 qexists_tac `pulse_spec_verilog_to_pulse_spec fextv` \\
 rw [pulse_spec_verilog_to_pulse_spec_def] \\
 Cases_on `fextv n "pulse"` >- metis_tac [sumTheory.ISR] \\
 Cases_on `y` \\ simp [] \\ ntac 2 (first_x_assum (qspec_then `n` strip_assume_tac)) \\ fs []);

val AB_spec_verilog = Q.store_thm("AB_spec_verilog",
 `!fext fextv Γ.
 pulse_spec_verilog fext /\ vars_has_type Γ ABtypes
 ==>
 ?n Γ'. mrun fext ABv Γ n = INR Γ' /\
      mget_var Γ' "done" = INR (VBool T)`,
 rpt strip_tac \\

 drule_strip relM_backwards \\
 drule_strip pulse_spec_verilog_backwards \\
 drule AB_spec \\ disch_then (qspec_then `init` strip_assume_tac) \\

 drule_strip AB_mrun \\ pop_assum (qspec_then `n` strip_assume_tac) \\
 asm_exists_tac \\ fs [relM_def, relM_var_def, BOOL_def]);

(*

pp example circuit:

open verilogPrintLib;

Av_def |> concl |> rhs |> intro_cvars_for_prog |> vprog_print |> print
Bv_def |> concl |> rhs |> intro_cvars_for_prog |> vprog_print |> print

R_trans |> vprog_print |> print

*)

(** Another example for the paper **)

val word_xor_1_2 = save_thm("word_xor_1_2",
 hol2hardware_exp (mk_var ("s", state_ty)) ``word_xor (1w:word8) 2w``);

val _ = export_theory ();
