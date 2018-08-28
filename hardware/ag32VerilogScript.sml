open hardwarePreamble;

open alignmentTheory alistTheory;

open verilogTranslatorLib moduleTranslatorTheory;
open verilogTranslatorConfigLib ag32MachineTheory ag32AddAcceleratorTheory ag32EqTheory;

val _ = new_theory "ag32Verilog";

guess_lengths ();
prefer_num ();

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
                  (* 0w: *) align_addr_def, decode_instruction_def, DecodeReg_imm_def, ALU_def, shift_def, execute_instruction_def,
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

(* Could move this further up *)
val computer_def = Define `
 computer = MAP (intro_cvars cvars) [prog; prog_acc]`;

val computer_Next_relM_run = Q.store_thm("computer_Next_relM_run",
 `!n fextv fext init vs.
  vars_has_type vs ag32types /\ relM init vs /\ relM_fextv fextv fext
  ==>
  ?vs'. mrun fextv computer vs n = INR vs' /\
        relM (circuit addacc_next init fext n) vs'`,
 rpt strip_tac \\ match_mp_tac mstep_commit_mrun \\ qexists_tac `ag32types` \\ rpt conj_tac
 >- simp [circuit_def]
 >- simp []
 (* TODO: Not sure why match_mp_tac doesn't work here... *)
 \\ rpt strip_tac \\ drule_strip (SIMP_RULE (srw_ss()) [] computer_Next_relM) \\ simp [computer_def]);

(** Lift INIT_REL_circuit to Verilog level **)

(* TODO: Move *)

val mget_var_ALOOKUP = Q.store_thm("mget_var_ALOOKUP",
 `!s name v. mget_var s name = INR v <=> ALOOKUP s name = SOME v`,
 rw [mget_var_def] \\ CASE_TAC);

val ver2w_def = Define `
 ver2w v = sum_map v2w (ver2v v)`;

val ver2w_w2ver = Q.store_thm("ver2w_w2ver",
 `!v. ver2w (w2ver v) = INR v`,
 simp [ver2w_def, w2ver_def, ver2v_def, sum_mapM_VBool, sum_map_def]);

(* Similar to REL, but for initial state *)
val INIT_verilog_def = Define `
 INIT_verilog env <=>
  (* Machine implementation registers *)
  WORD (3w:word3) (THE (ALOOKUP env "state")) /\
  BOOL F (THE (ALOOKUP env "acc_arg_ready")) /\
  WORD (0w:word3) (THE (ALOOKUP env "command")) /\
  WORD (5w:word3) (THE (ALOOKUP env "do_delay_write")) /\
  BOOL F (THE (ALOOKUP env "do_interrupt")) /\
  BOOL F (THE (ALOOKUP env "interrupt_req"))`;

val INIT_fext_def = Define `
 INIT_fext fext <=>
 fext.io_events = [] /\
 fext.ready /\
 fext.interrupt_state = InterruptReady /\
 ~fext.interrupt_ack`;

val (var_has_type_tm, mk_var_has_type, dest_var_has_type, is_var_has_type) = syntax_fns3 "verilogType" "var_has_type";

fun var_has_type_to_old_CONV tm =
 if is_abs tm then
   ABS_CONV var_has_type_to_old_CONV tm
 else if is_var_has_type tm then let
   val (_, _, ty) = dest_var_has_type tm
 in
   if is_VBool_t ty then (* BOOL *)
     PURE_REWRITE_CONV [GSYM var_has_type_old_var_has_type_BOOL] tm
   else if is_VArray_t ty then let
     val is = dest_VArray_t ty
     val len = length is
   in
     if len = 1 then (* WORD, TODO: assumes numerals in index position *) let
       val dimindex_rw = is |> hd |> dest_numeral |> mk_numeric_type |> mk_dimindex |> EVAL |> SYM
     in
       PURE_REWRITE_CONV [dimindex_rw, GSYM var_has_type_old_var_has_type_WORD] tm
     end else if len = 2 then (* WORD_ARRAY, TODO: does not work if index same... *) let
       val dimword_rw = is |> hd |> dest_numeral |> Arbnumcore.log2 |> mk_numeric_type |> mk_dimword |> EVAL |> SYM
       val dimindex_rw = is |> tl |> hd |> dest_numeral |> mk_numeric_type |> mk_dimindex |> EVAL |> SYM
     in
       PURE_REWRITE_CONV [dimword_rw, dimindex_rw, GSYM var_has_type_old_var_has_type_WORD_ARRAY] tm
     end else
       ALL_CONV tm
   end else
     ALL_CONV tm
 end else if is_comb tm then
   COMB_CONV var_has_type_to_old_CONV tm
 else ALL_CONV tm;

val relM_backwards = Q.store_thm("relM_backwards",
 `!vs. vars_has_type vs relMtypes ==> ?hol_s. relM hol_s vs`,
 simp [vars_has_type_def, relMtypes_def, relM_def, relM_var_def, mget_var_ALOOKUP] \\ rpt gen_tac \\

 CONV_TAC var_has_type_to_old_CONV \\

 simp [var_has_type_old_def, var_has_value_def] \\

 disch_then (MAP_EVERY (REPEAT_TCL CHOOSE_THEN ASSUME_TAC) o CONJUNCTS) \\

 (fn g as (asl, _) => let
     val hol_s = foldr (fn (assm, acc) => let
                          val (lconj, rconj) = dest_conj assm
                          val name = lconj |> lhs |> rand |> fromHOLstring
                          val update = lookup name updates
                          val rep = rconj |> rator |> rand
                        in
                          mk_comb(mk_comb (update, (mk_K_1 (rep, type_of rep))), acc)
                        end)
                       ``ARB:state_circuit``
                       asl
  in
    EXISTS_TAC hol_s g
  end) \\

 simp []);

val INIT_backwards_mem_def = Define `
 INIT_backwards_mem (mem : word32 -> word32) (i : word32) = (7 >< 0) (mem (align 2 i) >>>~ (8w * (1 >< 0) i))`;

val align_addr_align = Q.prove(
 `!w. align_addr w = align 2 w`,
 rw [align_addr_def, align_def] \\ blastLib.BBLAST_TAC);

val word4lt = WORD_DECIDE ``!(w:word32). w <+ 4w <=> w = 0w \/ w = 1w \/ w = 2w \/ w = 3w``;

val align_align_2_4 = Q.prove(
 `!w (addr:word32).
   w <+ 4w ==> align 2 (align 2 addr + w) = align 2 addr`,
 rpt strip_tac \\ fs [word4lt] \\ rveq \\
 simp [align_def] \\ blastLib.BBLAST_TAC);

val align_align_2_4_add = Q.prove(
 `!w (addr:word32). w <+ 4w ==> (1 >< 0) (align 2 addr + w) = w`,
 rpt strip_tac \\ fs [word4lt] \\ rveq \\
 simp [align_def] \\ blastLib.BBLAST_TAC);

val align_align_2_4_add_0 = align_align_2_4_add |> Q.SPEC `0w` |> SIMP_RULE (srw_ss()) [];

val mem_eq_INIT_backwards_mem = Q.store_thm("mem_eq_INIT_backwards_mem",
 `!memw. ∃memb. mem_eq memw memb`,
 gen_tac \\ qexists_tac `INIT_backwards_mem memw` \\
 rw [mem_eq_def, word_at_addr_def, INIT_backwards_mem_def, align_addr_align, align_align_2_4, align_align, align_align_2_4_add, align_align_2_4_add_0] \\
 simp [align_def] \\ blastLib.BBLAST_PROVE_TAC);

val INIT_backwards = Q.store_thm("INIT_backwards",
 `!t fext env mem_start.
   relM t env /\ INIT_verilog env /\ INIT_fext fext ==>
   ?s mem.
    INIT fext t (s with <| PC := mem_start + 64w;
                           R := (0w =+ mem_start) s.R;
                           MEM := mem;
                           io_events := [] |>)`,
 rw [relM_def, INIT_def, INIT_verilog_def, INIT_fext_def] \\

 qexists_tac `<| R := t.R; CarryFlag := t.CarryFlag; OverflowFlag := t.OverflowFlag;
                 data_in := t.data_in; data_out := t.data_out |>` \\
 simp [INIT_R_def, combinTheory.UPDATE_APPLY] \\

 qspec_then `fext.mem` strip_assume_tac mem_eq_INIT_backwards_mem \\ asm_exists_tac \\

 rfs [relM_var_def, WORD_def, BOOL_def, mget_var_ALOOKUP, w2ver_bij]);

val fext_accessor_verilog_def = Define `
 fext_accessor_verilog =
  <| get_command := \s. OUTR (ver2w (THE (ALOOKUP (OUTR s) "command")));
     get_PC := \s. OUTR (ver2w (THE (ALOOKUP (OUTR s) "PC")));
     get_data_addr := \s. OUTR (ver2w (THE (ALOOKUP (OUTR s) "data_addr")));
     get_data_wdata := \s. OUTR (ver2w (THE (ALOOKUP (OUTR s) "data_wdata")));
     get_data_wstrb := \s. OUTR (ver2w (THE (ALOOKUP (OUTR s) "data_wstrb")));

     get_interrupt_req := \s. OUTR (ver2bool (THE (ALOOKUP (OUTR s) "interrupt_req"))) |>`;

(* To cong thm here also? *)
val is_interrupt_interface_verilog = Q.store_thm("is_interrupt_interface_verilog",
 `!vs init fext fextv.
   vars_has_type vs ag32types /\ relM init vs /\ relM_fextv fextv fext /\
   is_interrupt_interface fext_accessor_verilog (mrun fextv computer vs) fext ==>
   is_interrupt_interface fext_accessor_circuit (circuit addacc_next init fext) fext`,
 simp [is_interrupt_interface_def, fext_accessor_circuit_def, fext_accessor_verilog_def] \\ rpt strip_tac \\

 drule_strip computer_Next_relM_run \\ pop_assum (qspec_then `n` strip_assume_tac) \\

 first_x_assum (qspec_then `n` assume_tac) \\
 TOP_CASE_TAC \\ fs [] \\
 rfs [relM_def, relM_var_def, mget_var_ALOOKUP, BOOL_def, ver2bool_def]);

val is_mem_cong = Q.store_thm("is_mem_cong",
 `!accessors1 step1 accessors2 step2 fext.
   (!n. accessors1.get_command (step1 n) = accessors2.get_command (step2 n) /\
        accessors1.get_PC (step1 n) = accessors2.get_PC (step2 n) /\
        accessors1.get_data_addr (step1 n) = accessors2.get_data_addr (step2 n) /\
        accessors1.get_data_wdata (step1 n) = accessors2.get_data_wdata (step2 n) /\
        accessors1.get_data_wstrb (step1 n) = accessors2.get_data_wstrb (step2 n)) ==>
   (is_mem accessors1 step1 fext <=> is_mem accessors2 step2 fext)`,
 rw [is_mem_def, fext_accessor_circuit_def, fext_accessor_verilog_def]);

val is_mem_cong' = is_mem_cong
 |> SPEC_ALL
 |> MATCH_MP (simpLib.SIMP_PROVE (srw_ss()) [] ``!a b c. (a ==> (b <=> c)) ==> (b ==> a ==> c)``)
 |> GEN_ALL;

val is_mem_verilog = Q.store_thm("is_mem_verilog",
 `!vs init fext fextv.
   vars_has_type vs ag32types /\ relM init vs /\ relM_fextv fextv fext /\
   is_mem fext_accessor_verilog (mrun fextv computer vs) fext ==>
   is_mem fext_accessor_circuit (circuit addacc_next init fext) fext`,
 rpt strip_tac \\ pop_assum (fn th => match_mp_tac (MATCH_MP is_mem_cong' th)) \\ gen_tac \\

 simp [fext_accessor_circuit_def, fext_accessor_verilog_def] \\

 drule_strip computer_Next_relM_run \\
 pop_assum (qspec_then `n` strip_assume_tac) \\
 qpat_x_assum `relM init vs` kall_tac \\ (* just for cleanup *)

 fs [relM_def, relM_var_def, mget_var_ALOOKUP, WORD_def, ver2w_w2ver]);

val INIT_REL_circuit_verilog = Q.store_thm("INIT_REL_circuit_verilog",
  `!n init mem_start fext fextv vstep.
   vstep = mrun fextv computer init /\

   relM_fextv fextv fext /\
   is_mem fext_accessor_verilog vstep fext /\
   is_interrupt_interface fext_accessor_verilog vstep fext /\
   is_mem_start_interface fext mem_start /\

   mem_no_errors fext /\

   vars_has_type init (relMtypes ++ ag32types) /\
   INIT_verilog init /\
   INIT_fext (fext 0) /\

   (!s.
    mem_eq (fext 0).mem s.MEM /\
    s.io_events = [] /\
    s.R 0w = mem_start /\
    s.PC = mem_start + 64w ==>
    (FUNPOW Next n s).io_events = [] (* <-- just an example property *))
   ==>
   ?m vs'.
    vstep m = INR vs' /\
    (fext m).io_events = []
    (*LIST_REL mem_eq (fext m).io_events s'.io_events*)`,
 simp [vars_has_type_append] \\ rpt strip_tac \\

 drule_strip relM_backwards \\
 drule_strip INIT_backwards \\
 pop_assum (qspec_then `mem_start` strip_assume_tac) \\

 drule_strip is_interrupt_interface_verilog \\
 qspecl_then [`hol_s`, `fext`] assume_tac is_acc_addacc \\
 drule_strip is_mem_verilog \\

 drule_strip (SIMP_RULE (srw_ss()) [] INIT_REL_circuit) \\ simp [combinTheory.UPDATE_APPLY] \\
 disch_then (qspec_then `n` strip_assume_tac) \\

 (* Step to REL-valid state *)
 drule_strip (SIMP_RULE (srw_ss()) [circuit_0] circuit_0_next) \\
 impl_tac >- fs [INIT_def] \\ strip_tac \\

 drule_strip computer_Next_relM_run \\ pop_assum (qspec_then `m'` strip_assume_tac) \\
 asm_exists_tac \\

 qmatch_asmsub_abbrev_tac `INIT _ _ s'` \\
 first_x_assum (qspec_then `s'` mp_tac) \\
 qunabbrev_tac `s'` \\ simp [combinTheory.UPDATE_APPLY] \\

 fs [REL_def, INIT_def] \\ metis_tac [LIST_REL_NIL]);

val _ = export_theory ();
