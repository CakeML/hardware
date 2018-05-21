open preamble;

open alistTheory;

open translatorLib moduleTranslatorTheory;
open tinyConfigLib tinyImplTheory tinyMachineTheory;

open verilogPrintLib;

(* val _ = new_theory "tinyTranslate"; *)

val s = ``s:tinyImpl_state``;

val ImplRun_tm = ``ImplRun``;

fun instruction_let_CONV_help tm = let
  val (f, arg) = dest_comb tm
in
  if is_comb f then let
    val (ff, farg) = dest_comb f
  in
    if ff = ImplRun_tm then let
      val var = ``i:word32``
    in
      if free_in var tm then
        failwith "i free in tm?"
      else
        (* TODO: Other var here, or check for freshness *)
        SOME (ISPECL [mk_abs (var, subst [ farg |-> var ] tm), farg] LET_THM |> SYM |> BETA_RULE)
    end
    else
      NONE
  end
  else
    NONE
end;

fun instruction_let_CONV tm =
  if is_comb tm then
    case instruction_let_CONV_help tm of
        SOME th => th
      | NONE => COMB_CONV instruction_let_CONV tm
  else if is_var tm orelse is_const tm then
    raise UNCHANGED
  else (* must be abs *)
    ABS_CONV instruction_let_CONV tm;

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

val cvars_def = Define `
 cvars = ["mem_inst_addr"; "mem_inst_out";
          "mem_data_addr"; "mem_data_mask"; "mem_data_in"; "mem_data_out";
          "acc_arg"; "acc_arg_ready"; "acc_res"; "acc_res_ready"]`;

fun intro_cvars_for_prog prog =
  list_mk_comb (``intro_cvars``, [``cvars``, prog])
  |> computeLib.RESTR_EVAL_CONV (append (decls "n2ver") (decls "w2ver"))
  |> concl |> rhs;

val Next_full_def = Next_def
 |> CONV_RULE instruction_let_CONV
 |> PURE_REWRITE_RULE [ImplRun_def]
 |> CONV_RULE (DEPTH_CONV BETA_CONV)
 (* Cannot use usual priming, because ' is not valid in Verilog identifiers *)
 |> CONV_RULE (with_flag (priming, SOME "_") rename_vars);

(* Translates a step function to hardware ... *)
fun hol2hardware_step_function tm = let
  val (stm, funtm) = tm |> concl |> dest_forall
  val ret = hol2hardware_trace stm (rhs funtm)
in
  (* TODO: No error handling here if no match... *)
  REWRITE_RULE [GSYM tm] ret
end;

val trans = hol2hardware_step_function Next_full_def;
val prog_def = EvalS_get_prog (trans |> concl);
val prog_def = Define `prog = ^prog_def`;
val trans = REWRITE_RULE [GSYM prog_def] trans;
val prog_comm = intro_cvars_for_prog (prog_def |> concl |> lhs);

(* Acc *)
val trans_acc = hol2hardware_step_function acc_Next_def;
val prog_acc_def = EvalS_get_prog (trans_acc |> concl);
val prog_acc_def = Define `prog_acc = ^prog_acc_def`;
val trans_acc = REWRITE_RULE [GSYM prog_acc_def] trans_acc;
val prog_acc_comm = intro_cvars_for_prog (prog_acc_def |> concl |> lhs);

(* Mem *)
val trans_mem = hol2hardware_step_function mem_Next_def;
val prog_mem_def = EvalS_get_prog (trans_mem |> concl);
val prog_mem_def = Define `prog_mem = ^prog_mem_def`;
val trans_mem = REWRITE_RULE [GSYM prog_mem_def] trans_mem;

(* Normalize for extraction *)
(* This can be simplified for now because only the processor has preconds *)
val trans = trans |> DISCH_ALL |> CONV_RULE (DEPTH_CONV AND_IMP_INTRO_CONV);
val precond = trans |> concl |> dest_imp |> fst;
val envP_def = Define `envP env = ^precond`;

val trans = trans |> REWRITE_RULE [GSYM envP_def] |> GEN_ALL;

val [trans_acc, trans_mem] = [trans_acc, trans_mem] |> map (Q.DISCH `envP env`)
                                                    |> map GEN_ALL;

val var_to_prg =
  [``prog``, ``prog_acc``, ``prog_mem``]
  |> map (fn prg => mk_comb (``vwrites``, prg)
                    |> EVAL |> concl |> rhs
                    |> dest_list |> fst |> map (fn tm => (tm, prg)))
  |> flatten;

val prg_to_EvalS = [(``prog``, trans), (``prog_acc``, trans_acc), (``prog_mem``, trans_mem)];

val get_nbq_var_empty = Q.store_thm("get_nbq_var_empty",
 `!env var. get_nbq_var <|vars := env; nbq := []|> var = INL UnknownVariable`,
 rw [get_nbq_var_def]);

val mget_var_get_nbq_var_empty = Q.store_thm("mget_var_get_nbq_var_empty",
 `!s ps var. get_nbq_var s var = INL UnknownVariable ==>
  mget_var <|vars := s.nbq ++ s.vars; ps := ps|> var = mget_var <|vars := s.vars; ps := ps|> var`,
 rw [get_nbq_var_def, mget_var_def, ALOOKUP_APPEND] \\ pop_assum mp_tac \\ TOP_CASE_TAC \\ fs []);

val computer_Next_relM = Q.store_thm("computer_next_relM",
 `!s env ps m.
  (* Will MP_MATCH away this afterwards, because Eval thm for processor has preconds: *)
  envP env ==>

  ps = [prog; prog_acc; prog_mem] /\
  m = <| vars := env; ps := MAP (intro_cvars cvars) ps |> /\

  (* Simulation step *)
  relM s m
  ==>
  ?m'. mstep_commit m = INR m' /\ relM (computer_Next acc_Next s) m'`,
 rpt strip_tac \\ simp [mstep_commit_def] \\
 qspecl_then [`cvars`, `ps`, `<|vars := env; nbq := []|>`,
              `<|vars := env; nbq := []|>`, `s`, `envP`] mp_tac mstep_untainted_state \\
 rveq \\ impl_tac
 >- (rpt conj_tac
  >- rw []
  >- (rw [] \\ TRY (metis_tac [trans, trans_mem, trans_acc]) \\ EVAL_TAC \\
      ntac 2 (pop_assum mp_tac) \\ EVAL_TAC \\ simp [] \\ strip_tac \\ fs [])
  >- EVAL_TAC
  >- metis_tac [relM_relS]
  >- (rw [valid_ps_for_module_def] \\ ntac 2 (pop_assum mp_tac) \\ EVAL_TAC \\ rw []) (* <-- takes forever *)
  \\ rw [])
 \\ imp_res_tac relM_relS \\
    drule (REWRITE_RULE [EvalS_def] trans) \\ disch_then drule \\
    drule (REWRITE_RULE [EvalS_def] trans_acc) \\ disch_then drule \\
    drule (REWRITE_RULE [EvalS_def] trans_mem) \\ disch_then drule \\

    rpt strip_tac \\ fs [sum_map_def, nbq_commit_def, computer_Next_def] \\
    rw [relM_def, relM_var_def] \\
    qmatch_goalsub_abbrev_tac `mget_var _ var = _` \\

    TRY (pop_assum (fn th => let
                 val prg = th |> concl |> markerSyntax.dest_abbrev |> snd |> flip lookup var_to_prg
               in
                 pop_assum (mp_tac o SPEC prg) \\ assume_tac th
               end) \\
    simp [] \\ strip_tac \\ pop_assum (qspec_then `var` mp_tac) \\ impl_tac
    >- (EVAL_TAC \\ rw []) \\ unabbrev_all_tac \\ simp [cvars_def] \\
    fs [] \\ rveq \\
    simp [get_nbq_var_empty, mget_var_get_nbq_var_empty] \\
    fs [get_var_def, get_nbq_var_def, mget_var_def, ALOOKUP_APPEND, relS_def, relS_var_def] \\
    (* for non-blocking cases: *)
    TOP_CASE_TAC \\ fs [])

    \\ (* lastMemAddr case, nobody writes to this ... *)
       (* TODO: Check if lastMemAddr API makes sense in CakeML compiler, otherwise do something *)
       cheat);

(*
Clean version of thm:

computer_Next_relM |> SPEC_ALL |> REWRITE_RULE [envP_def] |> UNDISCH |> GEN_ALL;
*)

(*
hol2hardware_body s tm
val tm = hd (!tm_trace)

Next_full_body
|> dest_let |> snd |> dest_cond |> #3 |> dest_cond |> #2 |> TypeBase.dest_case |> #3 |> hd
|> snd |> dest_cond |> #2

|> dest_cond |> #3 |> dest_cond |> #2
|> hol2hardware_body s;

``s with R := (x =+ bit_field_insert 31 23 (((8 >< 0) (i:word32)):word9) (s.R x)) s.R``
|> hol2hardware_body s;

fun let_cutter tm n = let
  val (body_abs, arg) = dest_let tm
  val (body_v, body) = dest_abs body_abs
  val body_new = if n = 0
                 then ``^s with PC := 5w``
                 else let_cutter body (n - 1)
in
  mk_let (mk_abs(body_v, body_new), arg)
end;

*)

(*
fun remove_lets tm =
  if is_let tm then let
    val (f, arg) = dest_let tm
    val (x, f) = dest_abs f
  in remove_lets f end
  else
    tm;

val tm = Next_full_body
|> dest_let |> snd |> dest_cond |> #3 |> dest_cond |> #2 |> TypeBase.dest_case |> #3 |> hd
|> snd |> dest_cond |> #2
|> remove_lets
|> TypeBase.strip_case |> snd |> el 4 |> snd
|> dest_let |> snd |> dest_cond |> #2 |> remove_lets

|> dest_comb |> snd

|> hol2hardware_body s
*)

fun print_local_var tm = let
  val (_, [_, var, ty]) = strip_comb tm
in
  print_var var ty
end;

(* TODO: These are init manually, fine now but must be handled in verification later *)
val init_vars = [(* IO: *) "data_in", "data_out",
                 "PC", "mem_inst_addr", "lastMemAddr",
                 "do_delay_write", "state", "acc_state", "acc_arg_ready",
                 "mem_fun"];

fun print_state_var tm = let
  val (_, [_, _, var, ty, _]) = strip_comb tm
in
  (* TODO: Hack *)
  if mem (fromHOLstring var) init_vars then
    ""
  else
    print_var var ty
end;

fun print_all_vars hyps = let
  val local_vars = map print_local_var hyps
  val state_vars = map print_state_var (relS_def |> concl |> strip_forall |> snd |> rhs |> strip_conj)
in
  (concat state_vars) ^ (concat local_vars)
end;

let
  val header = "`timescale 1ns / 1ps\n" ^
               "\n" ^
               "module processor(input clk,\n" ^
	       "                 input logic[15:0] data_in,\n" ^
	       "                 output logic[15:0] data_out);\n" ^
               "logic nothing;\n\n"

  val footer = "endmodule\n"

  val mem_connection =
      "\n" ^
      "// Just so we do not have to reapply the manual packed/unpacked fix each time...\n" ^
      "Mem MEM(.clkA(clk), .weA(mem_data_mask), .addrA(mem_data_addr), .dinA(mem_data_in), .doutA(mem_data_out),\n" ^
      "        .clkB(clk), .addrB(mem_inst_addr), .doutB(mem_inst_out));\n"

  val ss = header ^
           "logic[31:0] PC = 0;\n" ^
           "logic[9:0] mem_inst_addr = 0;\n" ^
           "logic[31:0] lastMemAddr = 1024;\n" ^
           "logic[2:0] do_delay_write = 5;\n" ^
           "logic[1:0] state = 1;\n" ^
           "logic acc_arg_ready = 0;\n" ^
           "logic[1:0] acc_state = 0;\n" ^
           "\n";

  val ss = ss ^ print_all_vars (envP_def |> SPEC_ALL |> concl |> dest_eq |> snd |> strip_conj)
  val ss = ss ^ mem_connection

  val ss = ss ^ "\nalways_ff @ (posedge clk) begin\n"
  val ss = ss ^ vprog_print prog_comm
  val ss = ss ^ "end\n"

  val ss = ss ^ "\nalways_ff @ (posedge clk) begin\n"
  val ss = ss ^ vprog_print prog_acc_comm
  val ss = ss ^ "end\n"

  val ss = ss ^ "\n" ^ footer
in
  writeFile "processor.sv" ss
  (* print *)
end;

(* val _ = export_theory(); *)
