open preamble;

open alistTheory;

open translatorLib moduleTranslatorTheory;
open ag32ConfigLib ag32MachineTheory ag32AddAcceleratorTheory ag32EqTheory;

open verilogPrintLib;

(*
(* Based on Magnus' code from mail *)
fun rename_vars tm = let
  val seen_names = ref ([]:term list)

  fun new_var v = let
    val v = if (type_of v = state_ty) then v else variant (!seen_names) v
    val _ = seen_names := (v :: (!seen_names))
  in v end

  fun change_name tm =
    let
      val (v,body) = dest_abs tm
    in ALPHA_CONV (new_var v) tm end

  fun walk_once c tm =
    if is_abs tm then (c THENC ABS_CONV (walk_once c)) tm else
    if is_comb tm then (RATOR_CONV (walk_once c) THENC
                                   RAND_CONV (walk_once c)) tm else
    ALL_CONV tm
in QCONV (walk_once change_name) tm end;
*)

val cvars_def = Define `
 cvars = ["PC"; "data_out";
          "command"; "data_addr"; "data_wdata"; "data_wstrb";
          "acc_arg"; "acc_arg_ready";
          "acc_res"; "acc_res_ready"]`;

fun intro_cvars_for_prog prog =
  list_mk_comb (``intro_cvars``, [``cvars``, prog])
  |> computeLib.RESTR_EVAL_CONV (append (decls "n2ver") (decls "w2ver"))
  |> concl |> rhs;

val cpu_step_def = cpu_Next_def
 |> REWRITE_RULE [cpu_Next_0w_def, cpu_Next_1w_def, cpu_Next_2w_def, cpu_Next_3w_def, cpu_Next_4w_def,
                  (* 0w: *) align_addr_def, decode_instruction_def, DecodeReg_imm_def, ALU_def, execute_instruction_def,
                  (* 1w: *) delay_write_Next_def];
(*
 |> CONV_RULE instruction_let_CONV
 |> PURE_REWRITE_RULE [ImplRun_def]
 |> CONV_RULE (DEPTH_CONV BETA_CONV)
 (* Cannot use usual priming, because ' is not valid in Verilog identifiers *)
 |> CONV_RULE (with_flag (priming, SOME "_") rename_vars); <-- might want to re-enable this
*)

(* Cpu *)
val trans = hol2hardware_step_function cpu_step_def;
val prog_def = EvalS_get_prog (trans |> concl);
val prog_def = Define `prog = ^prog_def`;
val trans = REWRITE_RULE [GSYM prog_def] trans;
val prog_comm = intro_cvars_for_prog (prog_def |> concl |> lhs);

(* Acc *)
val trans_acc = hol2hardware_step_function addacc_next_def;
val prog_acc_def = EvalS_get_prog (trans_acc |> concl);
val prog_acc_def = Define `prog_acc = ^prog_acc_def`;
val trans_acc = REWRITE_RULE [GSYM prog_acc_def] trans_acc;
val prog_acc_comm = intro_cvars_for_prog (prog_acc_def |> concl |> lhs);

(* Normalize for extraction *)
(* This can be simplified for now because only the processor has preconds *)
val trans = vars_has_type_cleanup trans;
val ag32types_def = trans |> hyp |> hd |> rand |> (fn tm => Define `ag32types = ^tm`);
val trans = trans |> DISCH_ALL |> PURE_REWRITE_RULE [GSYM ag32types_def] |> UNDISCH_ALL;

val prg_to_trans = [trans, trans_acc]
 |> map (fn t => (t |> concl |> rator |> rand |> strip_comb |> fst, (t |> concl |> rand, t |> GEN_ALL)));

(* Duplication from circuitExampleTrans... *)
fun mget_var_init_tac (g as (tms, tm)) = let
  val (mget_var_tm, pred_tm) = tm |> boolSyntax.dest_exists |> snd |> dest_conj
  val prg = pred_tm |> rator |> rand |> rand |> strip_comb |> fst
  val var = mget_var_tm |> lhs |> rand
  val res = lookup prg prg_to_trans
in
  (first_x_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [] o SPEC (fst res)) \\
  pop_assum (mp_tac o (CONV_RULE (LAND_CONV EVAL)) o SPEC var)) g
end;

val computer_Next_relM = Q.store_thm("computer_next_relM",
 `!n fext fextv init vs ps.
  (* Will MP_MATCH away this afterwards, because Eval thm for processor has preconds: *)
  vars_has_type vs ag32types ==>

  ps = [prog; prog_acc] /\
  (* Simulation step *)
  relM (circuit addacc_next init fext n) vs /\ relM_fextv fextv fext
  ==>
  ?vs'. mstep_commit (fextv n) (MAP (intro_cvars cvars) ps) vs = INR vs' /\
        relM (circuit addacc_next init fext (SUC n)) vs'`,
 rewrite_tac [relM_fextv_fext_relS_fextv_fext] \\ rpt strip_tac \\ first_x_assum (qspec_then `n` assume_tac) \\
 qspecl_then [`cvars`, `fext n`, `ps`, `fextv n`, `vs`, `circuit addacc_next init fext n`, `\vs. vars_has_type vs ag32types`] mp_tac mstep_commit_lift_EvalSs \\ impl_tac
 >- (simp [] \\ rpt conj_tac
    >- (gen_tac \\ strip_tac \\ rveq \\
        (conj_tac >- (metis_tac [DISCH_ALL trans, trans_acc])) \\ EVAL_TAC)
    >- EVAL_TAC
    \\ rw [valid_ps_for_module_def, cvars_def] \\ pop_assum mp_tac \\ EVAL_TAC \\ rw []) \\
 strip_tac \\ simp [] \\

 drule_strip relM_relS \\
 drule_strip (trans |> DISCH_ALL |> REWRITE_RULE [EvalS_def] |> GEN_ALL) \\
 drule_strip (trans_acc |> DISCH_ALL |> REWRITE_RULE [EvalS_def] |> GEN_ALL) \\

 rw [relM_def, relM_var_def, circuit_def] \\

 (* TODO: Somewhat of a hack currently to handle "data_in" not written to *)
 TRY (mget_var_init_tac \\ fs [relS_def, relS_var_def] \\ NO_TAC) \\

 drule_strip mstep_commit_intro_cvars_no_writes \\
 disch_then (qspec_then `"data_in"` mp_tac) \\ impl_tac >- EVAL_TAC \\

 qpat_x_assum `prun _ _ prog = _` assume_tac \\
 drule_strip prun_same_after \\ last_x_assum (qspec_then `"data_in"` mp_tac) \\
 impl_tac >- EVAL_TAC \\ disch_then (mp_tac o GSYM) \\ simp [get_var_mget_var] \\
 fs [relS_def, relS_var_def]);

val computer_Next_relM_run = Q.store_thm("computer_Next_relM_run",
 `!n fextv fext init vs.
  vars_has_type vs ag32types /\ relM init vs /\ relM_fextv fextv fext
  ==>
  ?vs'. mrun fextv (MAP (intro_cvars cvars) [prog; prog_acc]) vs n = INR vs' /\
        relM (circuit addacc_next init fext n) vs'`,
 rpt strip_tac \\ match_mp_tac mstep_commit_mrun \\ qexists_tac `ag32types` \\ rpt conj_tac
 >- simp [circuit_def]
 >- simp []
 (* TODO: Not sure why match_mp_tac doesn't work here... *)
 \\ rpt strip_tac \\ drule_strip (SIMP_RULE (srw_ss()) [] computer_Next_relM) \\ simp []);

val INIT_REL_circuit_verilog = Q.store_thm("INIT_REL_circuit_verilog",
  `!n c s init fext fextv vs.
   c = circuit addacc_next init fext /\
   is_mem c fext /\
   mem_no_errors fext /\

   vars_has_type vs ag32types /\
   relM init vs /\
   relM_fextv fextv fext /\

   INIT (fext 0) init s ==>
   ?m vs' cvs'.
    mrun fextv (MAP (intro_cvars cvars) [prog; prog_acc]) vs m = INR vs' /\
    relM cvs' vs' /\
    REL (fext m) cvs' (FUNPOW Next n s)`,
 simp [] \\ rpt strip_tac \\

 drule_strip (SIMP_RULE (srw_ss()) [] INIT_REL_circuit) \\
 disch_then (qspecl_then [`n`, `s`] mp_tac) \\
 impl_tac >- simp [is_acc_addacc] \\ strip_tac \\

 drule_strip computer_Next_relM_run \\ pop_assum (qspec_then `m` strip_assume_tac) \\ fs [] \\
 asm_exists_tac \\ simp [] \\ asm_exists_tac \\ simp []);

(** Pretty print to file **)

val input_vars = ["data_in"];
val output_vars = ["data_out", "command", "data_addr", "PC" (* for inst_addr *), "data_wdata", "data_wstrb", "interrupt_req"];
val external_vars = input_vars @ output_vars;

(* Fext vars *)

fun print_fext_var (var, ty) = let
  val var_type = predicate_for_type_ty ty
in
  print_var var var_type
end;

(* For filtering out modeling variables *)
fun is_fext_var (var, _) =
 var <> "mem";

(* Internal vars *)

local
  val s = mk_var ("t", state_ty)
  val data = INIT_def |> SPEC_ALL |> concl |> rhs |> strip_conj
in
val init_assoc =
 foldr (fn (spec, l) => if is_neg spec then let
                          val var = hol2hardware_exp s (dest_neg spec) |> concl |> Eval_get_prog |> dest_Var |> fromHOLstring
                          val v = exp_print ``Const (VBool F)``
                        in
                          (var, v) :: l
                        end else if is_eq spec andalso is_word_literal (rhs spec) then let
                          val (var, _, const) = hol2hardware_exp s spec |> concl |> Eval_get_prog |> dest_Cmp
                          val var = dest_Var var |> fromHOLstring
                        in
                          (var, exp_print const) :: l
                        end else
                          l) [] data
end;

fun print_interface_var (var, ty) = let
  val var_type = ty |> predicate_for_type_ty
  val init_val = assoc1 var init_assoc
  val var = print_var var var_type
in
  case init_val of
      SOME (_, v) => var ^ " = " ^ v
    | NONE => var
end;

fun is_internal_var (var, _) =
 not (exists (equal var) external_vars);

(* Internal let-induced vars *)

val internal_let_vars =
 ag32types_def
 |> concl |> rhs |> dest_list |> fst
 |> map (fn p =>
            let
              val (var, ty) = dest_pair p
              val var = fromHOLstring var
              val ty = newtype2vertype ty
            in
              "automatic " ^ ty ^ " " ^ var ^ ";\n"
            end)
 |> concat;

let
  val ss =
   "`timescale 1ns / 1ps\n" ^
   "\n" ^
   "module processor(\n" ^
   "  input clk,\n" ^
   (TypeBase.fields_of state_ty
    |> filter (fn (var, _) => mem var input_vars)
    |> map (fn p => "  input " ^ print_interface_var p ^ ",\n")
    |> String.concat) ^

   (TypeBase.fields_of state_ty
    |> filter (fn (var, _) => mem var output_vars)
    |> map (fn p => "  output " ^ print_interface_var p ^ ",\n")
    |> String.concat) ^

   (TypeBase.fields_of fext_ty
    |> filter is_fext_var
    |> map (fn var => "  input " ^ print_fext_var var)
    |> String.concatWith ",\n") ^
   ");\n\n" ^

   (TypeBase.fields_of state_ty
    |> filter is_internal_var
    |> map (fn p => print_interface_var p ^ ";\n")
    |> concat) ^

   "\nalways_ff @ (posedge clk) begin\n" ^
   (* All let variables are from processor currently, so can do this in a simple way currently *)
   internal_let_vars ^ "\n" ^
   vprog_print prog_comm ^
   "end\n" ^

   "\nalways_ff @ (posedge clk) begin\n" ^
   vprog_print prog_acc_comm ^
   "end\n" ^

   "\n" ^ "endmodule\n"
in
  writeFile "processor.sv" ss
end;
