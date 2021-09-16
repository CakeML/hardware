open hardwarePreamble;

open alignmentTheory alistTheory;
open ag32Machine2Theory (*ag32EqTheory*);

open translatorLib verilogPrintLib;

val _ = new_theory "ag32Verilog";

val _ = guess_lengths ();
val _ = prefer_num ();

val module_def = ag32_def;
val abstract_fields = ["mem", "io_events", "interrupt_state"];
val outputs = ["PC"];
val comms = ["PC", "data_out",
             "command", "data_addr", "data_wdata", "data_wstrb",
             "acc_arg", "acc_arg_ready",
             "acc_res", "acc_res_ready",
             "interrupt_req"];

val trans_thm = module2hardware module_def
                                abstract_fields
                                outputs
                                comms;

val verilogstr =
 definition"ag32_v_def"
 |> REWRITE_RULE [definition"ag32_v_seqs_def", definition"ag32_v_combs_def"]
 |> concl
 |> rhs
 |> verilog_print "processor";

print verilogstr

(*Definition INIT_fext_def:
 INIT_fext fext <=>
 fext.io_events = [] /\
 fext.ready /\
 fext.interrupt_state = InterruptReady /\
 ~fext.interrupt_ack
End*)

(** OLD **)

(*
(* Similar to REL, but for initial state *)
val INIT_verilog_vars_def = Define `
 INIT_verilog_vars env <=>
  (* Machine implementation registers *)
  WORD (0w:word32) (THE (ALOOKUP env "PC")) /\
  WORD (3w:word3) (THE (ALOOKUP env "state")) /\
  BOOL F (THE (ALOOKUP env "acc_arg_ready")) /\
  WORD (0w:word3) (THE (ALOOKUP env "command")) /\
  WORD (5w:word3) (THE (ALOOKUP env "do_delay_write")) /\
  BOOL F (THE (ALOOKUP env "do_interrupt")) /\
  BOOL F (THE (ALOOKUP env "interrupt_req")) /\

  WORD_ARRAY WORD (\(i:word6). (0w:word32)) (THE (ALOOKUP env "R"))`;

val INIT_verilog_def = Define `
 INIT_verilog fext env <=> INIT_verilog_vars env /\ INIT_fext fext`;

val relM_backwards = Q.store_thm("relM_backwards",
 `!vs. vars_has_type vs relMtypes ==> ?hol_s. relM hol_s vs`,
 simp [vars_has_type_def, relMtypes_def, relM_def, relM_var_def, mget_var_ALOOKUP] \\ rpt gen_tac \\

 relM_backwards_tac);

val align_addr_align = Q.store_thm("align_addr_align",
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

val INIT_backwards = Q.store_thm("INIT_backwards",
 `!t fext env mem.
   relM t env /\ INIT_verilog fext env /\ fext.mem = mem ==>
   ?s.
    INIT fext t (s with <| PC := 0w;
                           R := K 0w;
                           MEM := mem;
                           io_events := [] |>)`,
 rw [relM_def, INIT_def, INIT_verilog_def, INIT_verilog_vars_def, INIT_fext_def] \\

 qexists_tac `<| PC := t.PC; R := t.R; CarryFlag := t.CarryFlag; OverflowFlag := t.OverflowFlag;
                 data_in := t.data_in; data_out := t.data_out |>` \\

 rfs [relM_var_def, WORD_def, WORD_ARRAY_def, BOOL_def, mget_var_ALOOKUP, w2ver_bij] \\

 Cases_on `v` \\ rfs [] \\ match_mp_tac EQ_EXT \\ gen_tac \\
 first_x_assum (qspec_then `x` mp_tac) \\
 simp [w2ver_bij]);

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
   vars_has_type vs ag32types /\ relM init vs /\ lift_fext fextv fext /\
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
   vars_has_type vs ag32types /\ relM init vs /\ lift_fext fextv fext /\
   is_mem fext_accessor_verilog (mrun fextv computer vs) fext ==>
   is_mem fext_accessor_circuit (circuit addacc_next init fext) fext`,
 rpt strip_tac \\ pop_assum (fn th => match_mp_tac (MATCH_MP is_mem_cong' th)) \\ gen_tac \\

 simp [fext_accessor_circuit_def, fext_accessor_verilog_def] \\

 drule_strip computer_Next_relM_run \\
 pop_assum (qspec_then `n` strip_assume_tac) \\
 qpat_x_assum `relM init vs` kall_tac \\ (* just for cleanup *)

 fs [relM_def, relM_var_def, mget_var_ALOOKUP, WORD_def, ver2w_w2ver]);

val is_lab_env_verilog_circuit = Q.store_thm("is_lab_env_verilog_circuit",
 `!fext fextv vs init.
   vars_has_type vs ag32types /\
   relM init vs /\
   lift_fext fextv fext /\
   is_lab_env fext_accessor_verilog (mrun fextv computer vs) fext ==>
   is_lab_env fext_accessor_circuit (circuit addacc_next init fext) fext`,
 rw [is_lab_env_def] \\ metis_tac [is_interrupt_interface_verilog, is_mem_verilog]);

val INIT_REL_circuit_verilog = Q.store_thm("INIT_REL_circuit_verilog",
  `!n init fext fextv vstep s hol_s.
   vstep = mrun fextv computer init /\

   lift_fext fextv fext /\
   is_lab_env fext_accessor_verilog vstep fext /\

   vars_has_type init (relMtypes ++ ag32types) /\
   INIT_verilog (fext 0) init /\

   relM hol_s init /\
   INIT (fext 0) hol_s s
   ==>
   ?m vs'.
    vstep m = INR vs' /\
    relM (circuit addacc_next hol_s fext m) vs' /\
    REL (fext m) (circuit addacc_next hol_s fext m) (FUNPOW Next n s)`,
 (* todo: append not needed here? *)
 simp [INIT_verilog_def, vars_has_type_append] \\ rpt strip_tac \\

 drule_strip is_lab_env_verilog_circuit \\
 qspecl_then [`hol_s`, `fext`] assume_tac is_acc_addacc \\

 drule_strip (SIMP_RULE (srw_ss()) [] INIT_REL_circuit) \\ simp [combinTheory.UPDATE_APPLY] \\
 pop_assum (qspec_then `n` strip_assume_tac) \\

 (* Step to REL-valid state *)
 drule_strip (SIMP_RULE (srw_ss()) [circuit_0] circuit_0_next) \\
 impl_tac >- fs [INIT_def] \\ strip_tac \\

 drule_strip computer_Next_relM_run \\ pop_assum (qspec_then `m` strip_assume_tac) \\

 asm_exists_tac \\ simp [] \\ asm_exists_tac \\ simp []);
*)

val _ = export_theory ();
