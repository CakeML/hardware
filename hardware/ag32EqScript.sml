open hardwarePreamble;

open arithmeticTheory combinTheory;

open dep_rewrite blastLib;

open ag32Theory ag32MachineTheory wordsExtraTheory;

open bitstringSyntax fcpSyntax listSyntax wordsSyntax;

val _ = new_theory "ag32Eq";

guess_lengths ();
prefer_num ();

(* Memory behavior-selection functions *)

local
  val is_mem_def = ``is_mem fext_accessor_circuit step fext``
  |> SIMP_CONV (srw_ss()) [fext_accessor_circuit_def, is_mem_def]
  |> GEN_ALL;
  fun rw_mem conjn n = el conjn o CONJUNCTS o Q.SPEC n o PURE_REWRITE_RULE [is_mem_def]
in
val is_mem_do_nothing = rw_mem 1
val is_mem_inst_read = rw_mem 2
val is_mem_data_read = rw_mem 3
val is_mem_data_write = rw_mem 4
val is_mem_data_flush = rw_mem 5
end

val mem_no_errors_def = Define `
 mem_no_errors fext = !n. (fext n).error = 0w`;

(** Correspondence relation **)

val REL_def = Define `
 REL fext (t:state_circuit) (s:ag32_state) <=>
  (* Memory state *)
  (t.i = word_at_addr fext.mem (align_addr s.PC)) /\
  (fext.mem = s.MEM) /\
  fext.ready /\

  (* Interrupt state *)
  (fext.io_events = s.io_events) /\
  (fext.interrupt_state = InterruptReady) /\
  ~fext.interrupt_ack /\

  (* Needs to be in the state = 0 invariant because we need to know which instruction to run *)
  (t.state = 0w) /\

  (* Machine state *)
  (t.PC = s.PC) /\
  (t.R = s.R) /\
  (t.CarryFlag = s.CarryFlag) /\
  (t.OverflowFlag = s.OverflowFlag) /\
  (t.data_in = s.data_in) /\
  (t.data_out = s.data_out) /\

  (* Machine implementation state *)
  ~t.acc_arg_ready /\
  (t.command = 0w) /\
  (t.do_delay_write = 5w) /\
  ~t.do_interrupt /\
  ~t.interrupt_req`;

val INIT_R_def = Define `
 INIT_R (t:state_circuit) (s:ag32_state) =
  !i. i <> 0w ==> t.R i = s.R i`;

(* Similar to REL, but for initial state *)
val INIT_def = Define `
 INIT fext (t:state_circuit) (s:ag32_state) <=>
  (* Memory state *)
  (fext.mem = s.MEM) /\
  fext.ready /\

  (* Interrupt state, in practice both should be empty initially *)
  (fext.io_events = s.io_events) /\
  (fext.interrupt_state = InterruptReady) /\
  ~fext.interrupt_ack /\

  (t.state = 3w) /\

  (* Machine state, not including PC nor register zero *)
  (INIT_R t s) /\
  (t.CarryFlag = s.CarryFlag) /\
  (t.OverflowFlag = s.OverflowFlag) /\
  (t.data_in = s.data_in) /\
  (t.data_out = s.data_out) /\

  (* Machine implementation state *)
  ~t.acc_arg_ready /\
  (t.command = 0w) /\
  (t.do_delay_write = 5w) /\
  ~t.do_interrupt /\
  ~t.interrupt_req`;

val INIT_ISA_def = Define `
 INIT_ISA (s:ag32_state) mem_start <=>
  s.PC = mem_start + 64w /\
  s.R 0w = mem_start`;

(* Variant of state_circuit_component_equality with only cpu-relevant fields *)
val cpu_eq_def = Define `
 cpu_eq s1 s2 ⇔
  s1.state = s2.state ∧
  s1.PC = s2.PC ∧
  s1.R = s2.R ∧
  (s1.CarryFlag ⇔ s2.CarryFlag) ∧
  (s1.OverflowFlag ⇔ s2.OverflowFlag) ∧
  s1.i = s2.i ∧
  (*s1.instruction = s2.instruction ∧*)
  (*s1.ALU_res = s2.ALU_res ∧*)
  s1.delay_write = s2.delay_write ∧
  s1.do_delay_write = s2.do_delay_write ∧
  s1.data_out = s2.data_out ∧
  s1.data_in = s2.data_in ∧
  s1.acc_arg = s2.acc_arg ∧
  (s1.acc_arg_ready ⇔ s2.acc_arg_ready) ∧
  s1.mem_start = s2.mem_start ∧
  (s1.interrupt_req ⇔ s2.interrupt_req) ∧
  (s1.do_interrupt ⇔ s2.do_interrupt) ∧
  s1.command = s2.command ∧
  s1.data_addr = s2.data_addr ∧
  s1.data_wdata = s2.data_wdata ∧
  s1.data_wstrb = s2.data_wstrb`;

(** Correspondence proof **)

fun v2w_word_bit_list_cleanup tm =
  if is_var tm orelse is_const tm then
    raise UNCHANGED
  else if is_v2w tm andalso (is_list (rand tm)) then let
    val (arg, worddim) = dest_v2w tm
    val (arg, _) = dest_list arg
    val len = length arg
  in
    if len = 1 then
      raise UNCHANGED
    else let
      (* TODO: Fails on lists of non-dest_word_bit calls *)
      val (hindex, var) = arg |> hd |> dest_word_bit
      val (lindex, _) = arg |> last |> dest_word_bit
    in
      mk_eq (tm, mk_word_extract (hindex, lindex, var, mk_int_numeric_type len)) |> BBLAST_PROVE
    end
  end else if is_comb tm then
    COMB_CONV v2w_word_bit_list_cleanup tm
  else (* must be abs *)
    ABS_CONV v2w_word_bit_list_cleanup tm;

val LT2_cases = Q.store_thm("LT2_cases",
 `!n. n < 2 <=> n = 0 \/ n = 1`,
 DECIDE_TAC);

val LT4_cases = Q.store_thm("LT4_cases",
 `!n. n < 4 <=> n = 0 \/ n = 1 \/ n = 2 \/ n = 3`,
 DECIDE_TAC);

val LT16_cases = Q.store_thm("LT16_cases",
 `!n. n < 16 <=> n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/
                 n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15`,
 gen_tac \\ ntac 8 (Cases_on `n` >- fs [ADD1] \\ Cases_on `n'` >- fs [ADD1]) \\ fs [ADD1]);

val funcT2num_num2funcT = Q.prove(
 `!(w:word4). funcT2num (num2funcT (w2n w)) = (w2n w)`,
 Cases_on `w` \\ fs [ag32Theory.funcT2num_num2funcT]);

val shiftT2num_num2shiftT = Q.prove(
 `!(w:word2). shiftT2num (num2shiftT (w2n w)) = w2n w`,
 Cases_on `w` \\ fs [] \\ `n < 5` by DECIDE_TAC \\ fs [ag32Theory.shiftT2num_num2shiftT]);

val ri2bits_DecodeReg_imm = Q.store_thm("ri2bits_DecodeReg_imm",
 `!w1 w2. ri2bits (DecodeReg_imm (w1, w2)) = w1 @@ w2`,
 rw [ri2bits_def, ag32Theory.DecodeReg_imm_def] \\ FULL_BBLAST_TAC);

val ALU_correct_carry_lem = Q.prove(
 `!(w:33 word). word_bit 32 w <=> n2w (dimword(:32)) <=+ w`,
 simp [] \\ BBLAST_PROVE_TAC);

val ALU_correct_v2w_carry32_lem = Q.prove(
 `!b. v2w [b] = if b then (1w:word32) else 0w`,
 Cases \\ EVAL_TAC);

val ALU_correct_v2w_carry33_lem = Q.prove(
 `!b. v2w [b] = if b then (1w:33 word) else 0w`,
 Cases \\ EVAL_TAC);

val ALU_correct = Q.store_thm("ALU_correct",
 `!(func:word4) a b s t.
   t.CarryFlag = s.CarryFlag /\ t.OverflowFlag = s.OverflowFlag ==>
   ALU (func, a, b) t =
   let vt' = ag32$ALU (num2funcT (w2n func), a, b) s in
   t with <| OverflowFlag := (SND vt').OverflowFlag;
             CarryFlag := (SND vt').CarryFlag;
             ALU_res := FST vt' |>`,
 rpt strip_tac \\ simp [ALU_def, ag32Theory.ALU_def] \\
 Cases_on `func` \\ pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [LT16_cases]) \\ rveq \\
 simp [state_circuit_component_equality]

 >- (* Add *)
 (rpt conj_tac
  >- (Cases_on `a` \\ Cases_on `b` \\ fs [ALU_correct_carry_lem, w2n_w2w, WORD_LS, word_add_def])
  >- (simp [integer_wordTheory.overflow] \\ BBLAST_TAC)
  \\ BBLAST_TAC)

 >- (* AddWithCarry *)
 (rpt conj_tac
  >- (IF_CASES_TAC \\ simp [ALU_correct_v2w_carry33_lem] \\
     Cases_on `a` \\ Cases_on `b` \\ fs [ALU_correct_carry_lem, w2n_w2w, WORD_LS, word_add_def])
  \\ BBLAST_TAC)

 >- (* Sub *)
 (`a + -1w * b = a - b` by WORD_DECIDE_TAC \\ pop_assum (fn th => rewrite_tac [th]) \\
 rewrite_tac [integer_wordTheory.sub_overflow] \\ (* overkill: *) BBLAST_TAC)

 \\ (* Mul *)
 simp [word_mul_def, w2n_w2w] \\ BBLAST_TAC);

val dimindex_MOD_dimword = Q.store_thm("dimindex_MOD_dimword",
 `dimindex (:'a) MOD dimword (:'a) = dimindex (:'a)`,
simp [MOD_LESS, dimindex_lt_dimword]);

val MOD_MOD_lt = Q.store_thm("MOD_MOD_lt",
 `!x n m. n < m /\ 0 <> n ==> (x MOD n) MOD m = x MOD n`,
 metis_tac [LESS_MOD, MOD_LESS, LESS_TRANS, NOT_ZERO_LT_ZERO]);

val word_ror_intro_mod = Q.store_thm("word_ror_intro_mod",
 `!(w:'a word) sh. w #>>~ sh = w #>>~ word_mod sh (n2w (dimindex(:'a)))`,
 simp [word_ror_bv_def, word_ror_def, word_mod_def,
       dimindex_MOD_dimword, MOD_MOD_lt, dimindex_lt_dimword]);

val word_ror_impl = Q.store_thm("word_ror_impl",
 `!(w:word32) sh. sh <+ 32w ==> w #>>~ sh = (w >>>~ sh || w <<~ (32w - sh))`,
 BBLAST_TAC);

val shift_correct = Q.store_thm("shift_correct",
 `!shiftOp w a b s.
   shift shiftOp w a b s = s with R := (w =+ ag32$shift (num2shiftT (w2n shiftOp), a, b)) s.R`,
 Cases \\ rpt gen_tac \\ fs [LT4_cases] \\ rveq \\
 simp [shift_def, ag32Theory.shift_def] \\

 (* Rotation case *)
 simp [state_circuit_component_equality] \\ f_equals_tac \\
 once_rewrite_tac [word_ror_intro_mod] \\ simp [] \\
 DEP_REWRITE_TAC [word_ror_impl] \\
 simp [] \\

 simp [word_mod_def, WORD_LO, MOD_MOD_lt]);

(* Common for all post-conditions for state = 0w *)
val state_0w_fext_post_def = Define `
 state_0w_fext_post fext n =
 ((fext (n + 1)).mem = (fext n).mem /\
  (fext (n + 1)).ready = (fext n).ready)`;

val DecodeReg_imm_Reg = Q.store_thm("DecodeReg_imm_Reg",
 `!flag v1 v2.
   ag32$DecodeReg_imm (flag, v1) = Reg v2 ==> flag = 0w /\ v1 = v2`,
 rw [ag32Theory.DecodeReg_imm_def]);

val DecodeReg_imm_Imm = Q.store_thm("DecodeReg_imm_Imm",
 `!flag v1 v2.
   ag32$DecodeReg_imm (flag, v1) = Imm v2 ==> flag = 1w /\ v1 = v2`,
 rw [ag32Theory.DecodeReg_imm_def] \\ Cases_on `flag` \\ fs []);

(* Can be optimized ... *)
val no_mem_error_tac = reverse IF_CASES_TAC >- rfs [mem_no_errors_def] \\ pop_assum kall_tac;

val no_interrupt_req = Q.store_thm("no_interrupt_req",
 `!n c fext.
  is_interrupt_interface fext_accessor_circuit c fext /\
  (fext n).interrupt_state = InterruptReady /\
  ~(c n).interrupt_req ==>
  (fext (SUC n)).interrupt_state = InterruptReady /\
  (fext (SUC n)).io_events = (fext n).io_events /\
  ~(fext (SUC n)).interrupt_ack`,
 rewrite_tac [is_interrupt_interface_def] \\ rpt strip_tac' \\
 first_x_assum (qspec_then `n` mp_tac) \\ simp [fext_accessor_circuit_def]);

val circuit_read_wait = Q.store_thm("circuit_read_wait",
 `!m facc init fext n.
   is_interrupt_interface fext_accessor_circuit (circuit facc init fext) fext /\
   mem_no_errors fext /\
   (* from previous inst. of is_mem: *)
   (!p. p < m ==> (fext (SUC (n + p))).mem = (fext n).mem /\ ~(fext (SUC (n + p))).ready) /\

   (fext n).ready /\
   (fext n).interrupt_state = InterruptReady /\

   (circuit facc init fext n).state = 1w /\

   (circuit facc init fext n).command <> 0w /\
   ~(circuit facc init fext n).interrupt_req
   ==>
   cpu_eq (circuit facc init fext (SUC (m + n)))
          ((circuit facc init fext n) with command := 0w) /\
   (fext (SUC (m + n))).io_events = (fext n).io_events /\
   (fext (SUC (m + n))).interrupt_state = InterruptReady /\
   ~(fext (SUC (m + n))).interrupt_ack`,
 rpt gen_tac \\ strip_tac \\ Induct_on `m`
 >- (strip_tac \\ drule_strip no_interrupt_req \\
    simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
    simp [cpu_Next_1w_def, delay_write_Next_def, cpu_eq_def]) \\
 strip_tac \\ qpat_x_assum `_ ==> _` mp_tac \\ impl_tac >- simp [] \\ strip_tac \\
 once_rewrite_tac [circuit_def] \\
 simp [cpu_Next_def] \\ no_mem_error_tac \\
 qpat_x_assum `cpu_eq _ _` (strip_assume_tac o REWRITE_RULE [cpu_eq_def]) \\
 rfs [ADD1, cpu_Next_1w_def] \\
 drule_strip no_interrupt_req \\
 first_x_assum (qspec_then `m` assume_tac) \\ fs [ADD1] \\
 simp [cpu_eq_def]);

val circuit_acc_wait_help = Q.store_thm("circuit_acc_wait_help",
 `!l k n facc init fext.
   is_mem fext_accessor_circuit (circuit facc init fext) fext /\
   is_interrupt_interface fext_accessor_circuit (circuit facc init fext) fext /\
   mem_no_errors fext /\

   (circuit facc init fext n).state = 2w /\
   (circuit facc init fext n).acc_arg_ready /\
   ~(circuit facc init fext n).interrupt_req /\

   (fext n).ready /\
   (fext n).interrupt_state = InterruptReady /\
   (circuit facc init fext n).command = 0w /\
   l < k /\

   (* from previous inst. of is_acc, somewhat ugly: *)
   (k <> 0 ==> ~(circuit facc init fext (SUC n)).acc_res_ready) /\
   (!l. l < k /\ (!m. m <> 0 /\ m <= l ==> ~(circuit facc init fext (n + m)).acc_arg_ready) ==>
        ~(circuit facc init fext (SUC (n + l))).acc_res_ready)
   ==>
   (!m. m <= l ==> cpu_eq (circuit facc init fext (SUC (n + m)))
                          ((circuit facc init fext n) with acc_arg_ready := F) /\
                   ~(circuit facc init fext (SUC (n + m))).acc_res_ready /\
                   (fext (SUC (n + m))).ready /\
                   (fext (SUC (n + m))).mem = (fext n).mem /\
                   (fext (SUC (n + m))).io_events = (fext n).io_events /\
                   (fext (SUC (n + m))).interrupt_state = InterruptReady /\
                   ~(fext (SUC (n + m))).interrupt_ack)`,
 (* TODO: This is a mess... but works for now *)
 rpt gen_tac \\ strip_tac \\ Induct_on `l`
 >- (drule_strip no_interrupt_req \\
     simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\ simp [cpu_Next_2w_def, cpu_eq_def] \\
     last_x_assum (assume_tac o is_mem_do_nothing `n`) \\
     fs []) \\
 rpt strip_tac' \\ reverse (Cases_on `m = SUC l`) >- (`m <= l` by DECIDE_TAC \\ fs []) \\
 rveq \\

 last_assum (qspec_then `SUC l` mp_tac) \\ impl_tac >- (rw [] \\ Cases_on `m` >- fs [] \\ fs [GSYM ADD_SUC] \\
 first_x_assum (qspec_then `n'` mp_tac) \\ simp [cpu_eq_def]) \\ simp [] \\ disch_then kall_tac \\

 first_x_assum (qspec_then `l` mp_tac) \\ impl_tac >- (rw [] \\ Cases_on `m` \\ fs [] \\
 first_x_assum (qspec_then `n'` mp_tac) \\ simp [cpu_eq_def, GSYM ADD_SUC]) \\
 strip_tac \\ fs [] \\ first_x_assum (qspec_then `l` mp_tac) \\ simp [] \\ strip_tac \\
 simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\ fs [cpu_Next_2w_def, cpu_eq_def, GSYM ADD_SUC] \\
 last_x_assum (assume_tac o is_mem_do_nothing `SUC (l + n)`) \\
 rfs [] \\ drule_strip no_interrupt_req \\ simp []);

val circuit_acc_wait = Q.store_thm("circuit_acc_wait",
 `!k n facc init fext.
   is_mem fext_accessor_circuit (circuit facc init fext) fext /\
   is_interrupt_interface fext_accessor_circuit (circuit facc init fext) fext /\
   mem_no_errors fext /\

   (circuit facc init fext n).state = 2w /\
   (circuit facc init fext n).acc_arg_ready /\
   ~(circuit facc init fext n).interrupt_req /\

   (fext n).ready /\
   (fext n).interrupt_state = InterruptReady /\
   (circuit facc init fext n).command = 0w /\

   (* from previous inst. of is_acc, somewhat ugly: *)
   (k <> 0 ==> ~(circuit facc init fext (SUC n)).acc_res_ready) /\
   (!l. l < k /\ (!m. m <> 0 /\ m <= l ==> ~(circuit facc init fext (n + m)).acc_arg_ready) ==>
        ~(circuit facc init fext (SUC (n + l))).acc_res_ready)
   ==>
   !m. m <= k ==> cpu_eq (circuit facc init fext (SUC (n + m)))
                         ((circuit facc init fext n) with acc_arg_ready := F) /\
                  (fext (SUC (n + m))).ready /\
                  (fext (SUC (n + m))).mem = (fext n).mem /\
                  (fext (SUC (n + m))).io_events = (fext n).io_events /\
                  (fext (SUC (n + m))).interrupt_state = InterruptReady /\
                  ~(fext (SUC (n + m))).interrupt_ack`,
 (* TODO: As the above proof, this is also a mess. *)
 rpt strip_tac' \\ Cases_on `m`
 >- (* duplication: *)
 (drule_strip no_interrupt_req \\
 simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\ simp [cpu_Next_2w_def, cpu_eq_def] \\
 last_x_assum (assume_tac o is_mem_do_nothing `n`) \\
 fs []) \\

 `n' < k` by DECIDE_TAC \\ drule_strip circuit_acc_wait_help \\ disch_then (qspec_then `n'` mp_tac) \\ simp [] \\ strip_tac \\

 qpat_x_assum `cpu_eq _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [cpu_eq_def]) \\

 simp [circuit_def] \\ simp [GSYM ADD_SUC] \\ simp [cpu_Next_def] \\ no_mem_error_tac \\ simp [cpu_Next_2w_def, cpu_eq_def] \\
 last_x_assum (assume_tac o is_mem_do_nothing `SUC (n + n')`) \\
 rfs [] \\ drule_strip no_interrupt_req \\ simp []);

val circuit_interrupt_wait = Q.store_thm("circuit_interrupt_wait",
 `!m n facc init fext.
   is_mem fext_accessor_circuit (circuit facc init fext) fext /\
   mem_no_errors fext /\

   (circuit facc init fext n).state = 4w /\
   (circuit facc init fext n).command = 0w /\

   (fext n).ready /\
   ~(fext n).interrupt_ack /\

   (!l. l < m ==> ~(fext (SUC (n + l))).interrupt_ack)
   ==>
   cpu_eq (circuit facc init fext (SUC (n + m)))
          (circuit facc init fext n) /\
   (fext (SUC (n + m))).ready /\
   (fext (SUC (n + m))).mem = (fext n).mem`,
 Induct \\ rpt strip_tac' >-
 (last_x_assum (assume_tac o is_mem_do_nothing `n`) \\ simp [] \\ pop_assum kall_tac \\
 simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_4w_def, cpu_eq_def]) \\

 simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 drule_last \\ impl_tac >- simp [] \\ fs [ADD_SUC] \\
 disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [cpu_eq_def]) \\
 last_x_assum (mp_tac o is_mem_do_nothing `n + SUC m`) \\
 simp [ADD_SUC] \\ disch_then kall_tac \\
 simp [cpu_Next_4w_def, cpu_eq_def]);

val circuit_mem_start_ready_wait = Q.store_thm("circuit_mem_start_ready_wait",
 `!m facc init fext.
   is_mem fext_accessor_circuit (circuit facc init fext) fext /\
   is_interrupt_interface fext_accessor_circuit (circuit facc init fext) fext /\
   mem_no_errors fext /\

   (circuit facc init fext 0).state = 3w /\
   (circuit facc init fext 0).command = 0w /\
   ~(circuit facc init fext 0).interrupt_req /\

   (fext 0).ready /\
   (fext 0).interrupt_state = InterruptReady /\
   ~(fext 0).interrupt_ack /\

   (!l. l < m ==> ~(fext l).mem_start_ready)
   ==>
   cpu_eq (circuit facc init fext m)
          (circuit facc init fext 0) /\
   (fext m).ready /\
   (fext m).mem = (fext 0).mem /\
   (fext m).io_events = (fext 0).io_events /\
   (fext m).interrupt_state = InterruptReady /\
   ~(fext m).interrupt_ack`,
 Induct \\ rpt strip_tac' >- simp [cpu_eq_def] \\
 drule_last \\ impl_tac >- simp [] \\
 disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [cpu_eq_def]) \\
 last_x_assum (mp_tac o is_mem_do_nothing `m`) \\ simp [] \\ disch_then kall_tac \\
 rfs [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 drule_strip no_interrupt_req \\
 simp [cpu_Next_3w_def, cpu_eq_def]);

(* Impl variant of ri2word... *)
val EncodeReg_imm_def = Define `
 (EncodeReg_imm (Imm v) (s:state_circuit) = sw2sw v) /\
 (EncodeReg_imm (Reg r) s = s.R r)`;

val EncodeReg_imm_DecodeReg_imm = Q.store_thm("EncodeReg_imm_DecodeReg_imm",
 `!flag v s. EncodeReg_imm (DecodeReg_imm (v2w [flag], v)) s = DecodeReg_imm (flag, v) s`,
 rw [ag32Theory.DecodeReg_imm_def, DecodeReg_imm_def, EncodeReg_imm_def, v2w_single_0w]);

val ri2word_DecodeReg_imm = Q.store_thm("ri2word_DecodeReg_imm",
 `!s t i arg.
   t.R = s.R ==>
   ri2word (DecodeReg_imm (v2w [word_bit i t.i], arg)) s =
   DecodeReg_imm (word_bit i t.i, arg) t`,
 rw [ri2word_def, ag32Theory.DecodeReg_imm_def, DecodeReg_imm_def, v2w_single_0w] \\ fs []);

val DecodeReg_imm_cleanup_instruction = Q.store_thm("DecodeReg_imm_cleanup_instruction",
 `!flag v i s. DecodeReg_imm (flag, v) (s with instruction := i) = DecodeReg_imm (flag, v) s`,
 rw [DecodeReg_imm_def]);

val ALU_cleanup_instruction = Q.store_thm("ALU_cleanup_instruction",
 `!func a b s i. ALU (func, a, b) (s with instruction := i) = (ALU (func, a, b) s) with instruction := i`,
 rpt gen_tac \\ simp [ALU_def] \\ Cases_on `func` \\
 rpt (IF_CASES_TAC >- simp [state_circuit_component_equality]) \\
 last_x_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [LT16_cases]) \\ fs []);

(* This is not pretty, ad-hoc collection of variables we need to know are the same afterwards *)
val ALU_state_eq_after = Q.store_thm("ALU_state_eq_after",
 `!func a b res s s'.
   ag32$ALU (func, a, b) s = (res, s') ==>
   s'.PC = s.PC /\ s'.MEM = s.MEM /\ s'.PC = s.PC /\ s'.R = s.R /\ s'.data_in = s.data_in /\
   s'.data_out = s.data_out /\ s'.io_events = s.io_events`,
 rw [ag32Theory.ALU_def] \\ Cases_on `func` \\ fs [] \\ rw []);

(* "Variable slice", TODO: Move... *)
val word_ver_var_slice_def = Define `
 word_ver_var_slice idx len w = (w2n idx + (len - 1) >< w2n idx) w`;

val circuit_next = Q.store_thm("circuit_next",
 `!f init fext facc (c : num -> state_circuit).
   c = circuit facc init fext /\
   is_mem fext_accessor_circuit c fext /\
   is_acc f c /\
   is_interrupt_interface fext_accessor_circuit c fext /\
   mem_no_errors fext ==>
   !n. case (c n).state of
         0w =>
           !s.
            (c n).R = s.R /\ (c n).PC = s.PC /\ (c n).CarryFlag = s.CarryFlag /\ (c n).OverflowFlag = s.OverflowFlag /\

            (word_at_addr (fext n).mem (align_addr (c n).PC) = (c n).i) /\ (c n).command = 0w /\ (fext n).ready /\

            ~(c n).interrupt_req /\ (fext n).interrupt_state = InterruptReady
            ==>
            state_0w_fext_post fext n /\
            ((fext (n + 1)).io_events = (fext n).io_events /\
             (fext (n + 1)).interrupt_state = InterruptReady /\
             ~(fext (n + 1)).interrupt_ack) /\
            (case Decode (c n).i of
               Accelerator (w, a) =>
               cpu_eq (c (n + 1)) (c n with <| delay_write := w;
                                               acc_arg := EncodeReg_imm a (c n);
                                               acc_arg_ready := T;
                                               PC := (c n).PC + 4w;
                                               state := 2w |>)
             | In w =>
               cpu_eq (c (n + 1)) (c n with <| R := (w =+ w2w (c n).data_in) (c n).R;
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 1w |>)
             | Interrupt =>
               cpu_eq (c (n + 1)) (c n with <| data_addr := (c n).mem_start;
                                               do_interrupt := T;
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 4w |>)
             | Jump (func, w, a) =>
               let (res, s') = ag32$ALU (func, s.PC, ri2word a s) s in
               cpu_eq (c (n + 1)) (c n with <| R := (w =+ s.PC + 4w) (c n).R;
                                               CarryFlag := s'.CarryFlag;
                                               OverflowFlag := s'.OverflowFlag;
                                               PC := res;
                                               state := 1w;
                                               command := 1w |>)
             | JumpIfNotZero (func, w, a, b) =>
               let (res, s') = ag32$ALU (func, ri2word a s, ri2word b s) s in
               cpu_eq (c (n + 1)) (c n with <| CarryFlag := s'.CarryFlag;
                                               OverflowFlag := s'.OverflowFlag;
                                               PC := if res <> 0w then s.PC + ri2word w s else s.PC + 4w;
                                               state := 1w;
                                               command := 1w |>)
             | JumpIfZero (func, w, a, b) =>
               let (res, s') = ag32$ALU (func, ri2word a s, ri2word b s) s in
               cpu_eq (c (n + 1)) (c n with <| CarryFlag := s'.CarryFlag;
                                               OverflowFlag := s'.OverflowFlag;
                                               PC := if res = 0w then s.PC + ri2word w s else s.PC + 4w;
                                               state := 1w;
                                               command := 1w |>)
             | LoadConstant (w, negate, a) =>
               cpu_eq (c (n + 1)) (c n with <| R := (w =+ if negate then -w2w a else w2w a) (c n).R;
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 1w |>)
             | LoadMEM (w, a) =>
               cpu_eq (c (n + 1)) (c n with <| delay_write := w;
                                               do_delay_write := 4w;
                                               data_addr := EncodeReg_imm a (c n);
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 2w |>)
             | LoadMEMByte (w, a) =>
               let addr = (EncodeReg_imm a (c n)) in
               cpu_eq (c (n + 1)) (c n with <| delay_write := w;
                                               do_delay_write := (1 >< 0) addr;
                                               data_addr := addr;
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 2w |>)
             | Normal (func, w, a, b) =>
               let (res, s') = ag32$ALU (func, ri2word a s, ri2word b s) s in
               cpu_eq (c (n + 1)) (c n with <| R := (w =+ res) (c n).R;
                                               CarryFlag := s'.CarryFlag;
                                               OverflowFlag := s'.OverflowFlag;
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 1w |>)
             | LoadUpperConstant (w, a) =>
               cpu_eq (c (n + 1)) (c n with <| R := (w =+ bit_field_insert 31 23 a ((c n).R w)) (c n).R;
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 1w |>)
             | Out (func, w, a, b) =>
               let (res, s') = ag32$ALU (func, ri2word a s, ri2word b s) s in
               cpu_eq (c (n + 1)) (c n with <| R := (w =+ res) (c n).R;
                                               CarryFlag := s'.CarryFlag;
                                               OverflowFlag := s'.OverflowFlag;
                                               data_out := (9 >< 0) res;
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 1w |>)
             | ReservedInstr =>
               cpu_eq (c (n + 1)) (c n)
             | Shift (shiftOp, w, a, b) =>
               let shift_res = ag32$shift (shiftOp, ri2word a s, ri2word b s) in
               cpu_eq (c (n + 1)) (c n with <| R := (w =+ shift_res) (c n).R;
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 1w |>)
             | StoreMEM (a, b) =>
               cpu_eq (c (n + 1)) (c n with <| data_addr := ri2word b s;
                                               data_wdata := ri2word a s;
                                               data_wstrb := 15w;
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 3w |>)
             | StoreMEMByte (a, b) =>
               cpu_eq (c (n + 1)) (c n with <| data_addr := ri2word b s;
                                               data_wstrb := 1w <<~ w2w ((1 >< 0) (ri2word b s));
                                               data_wdata := (case (1 >< 0) (ri2word b s) of
                                                                  0w => bit_field_insert 7 0 ((7 >< 0) (ri2word a s)) (c n).data_wdata
                                                                | 1w => bit_field_insert 15 8 ((7 >< 0) (ri2word a s)) (c n).data_wdata
                                                                | 2w => bit_field_insert 23 16 ((7 >< 0) (ri2word a s)) (c n).data_wdata
                                                                | 3w => bit_field_insert 31 24 ((7 >< 0) (ri2word a s)) (c n).data_wdata
                                                                | v => ARB (* <-- just to silence warning *));
                                               PC := (c n).PC + 4w;
                                               state := 1w;
                                               command := 3w |>))
       | 1w =>
         (case (c n).command of
            1w => (c n).do_delay_write = 5w /\ ~(c n).do_interrupt /\ (fext n).ready /\
                  ~(c n).interrupt_req /\ (fext n).interrupt_state = InterruptReady ==>
                  ?m. cpu_eq (c (n + m)) (c n with <| command := 0w;
                                                      state := 0w;
                                                      i := word_at_addr (fext n).mem (align_addr (c n).PC) |>) /\
                      (fext (n + m)).ready /\
                      (fext (n + m)).mem = (fext n).mem /\
                      (fext (n + m)).interrupt_state = InterruptReady /\
                      (fext (n + m)).io_events = (fext n).io_events /\
                      ~(fext (n + m)).interrupt_ack
          | 2w => (c n).do_delay_write <+ 5w /\ ~(c n).do_interrupt /\ (fext n).ready /\
                  ~(c n).interrupt_req /\ (fext n).interrupt_state = InterruptReady ==>
                  ?m. cpu_eq
                       (c (n + m))
                       (c n with <| command := 0w;
                                    state := 0w;
                                    i := word_at_addr (fext n).mem (align_addr (c n).PC);
                                    do_delay_write := 5w;
                                    R := if (c n).do_delay_write = 4w then
                                          ((c n).delay_write =+ (word_at_addr (fext (n + m)).mem (align_addr (c n).data_addr))) (c n).R
                                         else
                                          ((c n).delay_write =+ w2w ((word_ver_var_slice ((8w:word6) * w2w (c n).do_delay_write) 8
                                                                                         (word_at_addr (fext (n + m)).mem (align_addr (c n).data_addr))):word8))
                                          (c n).R |>) /\
                      (fext (n + m)).ready /\
                      (fext (n + m)).mem = (fext n).mem /\
                      (fext (n + m)).interrupt_state = InterruptReady /\
                      (fext (n + m)).io_events = (fext n).io_events /\
                      ~(fext (n + m)).interrupt_ack
          | 3w => (c n).do_delay_write = 5w /\ ~(c n).do_interrupt /\ (fext n).ready /\
                  ~(c n).interrupt_req /\ (fext n).interrupt_state = InterruptReady ==>
                  (let newmem = mem_update (fext n).mem (align_addr (c n).data_addr) (c n).data_wdata (c n).data_wstrb in
                  ?m. cpu_eq
                       (c (n + m))
                       (c n with <| command := 0w;
                                    state := 0w;
                                    i := word_at_addr newmem (align_addr (c n).PC) |>) /\
                      (fext (n + m)).ready /\
                      (fext (n + m)).mem = newmem /\
                      (fext (n + m)).interrupt_state = InterruptReady /\
                      (fext (n + m)).io_events = (fext n).io_events /\
                      ~(fext (n + m)).interrupt_ack)
          | 4w => (c n).do_delay_write = 5w /\ (c n).do_interrupt /\ (fext n).ready /\
                  ~(c n).interrupt_req /\ (fext n).interrupt_state = InterruptReady ==>
                  ?m. cpu_eq (c (n + m)) (c n with <| command := 0w;
                                                      state := 4w;
                                                      interrupt_req := T;
                                                      do_interrupt := F;
                                                      i := word_at_addr (fext n).mem (align_addr (c n).PC) |>) /\
                      (fext (n + m)).ready /\
                      (fext (n + m)).mem = (fext n).mem /\
                      (fext (n + m)).interrupt_state = InterruptReady /\
                      (fext (n + m)).io_events = (fext n).io_events /\
                      ~(fext (n + m)).interrupt_ack
          | _ => T)
       | 2w => (c n).acc_arg_ready /\ (c n).command = 0w /\ (fext n).ready /\
               ~(c n).interrupt_req /\ (fext n).interrupt_state = InterruptReady ==>
               ?m. cpu_eq
                    (c (n + m))
                    (c n with <| command := 1w;
                                 state := 1w;
                                 acc_arg_ready := F;
                                 R := ((c n).delay_write =+ f (c n).acc_arg) (c n).R |>) /\
                    (fext (n + m)).ready /\
                    (fext (n + m)).mem = (fext n).mem /\
                    (fext (n + m)).interrupt_state = InterruptReady /\
                    (fext (n + m)).io_events = (fext n).io_events /\
                    ~(fext (n + m)).interrupt_ack
       | 4w => (c n).command = 0w /\ (fext n).ready /\
               (c n).interrupt_req /\ ~(fext n).interrupt_ack /\ (fext n).interrupt_state = InterruptReady ==>
               ?m. cpu_eq
                    (c (n + m))
                    (c n with <| state := 0w;
                                 interrupt_req := F |>) /\
                    (fext (n + m)).ready /\
                    (fext (n + m)).mem = (fext n).mem /\
                    (fext (n + m)).interrupt_state = InterruptReady /\
                    (fext (n + m)).io_events = (fext n).io_events ++ [(fext n).mem] /\
                    ~(fext (n + m)).interrupt_ack
       | _ => T`,
 rpt strip_tac \\ rveq \\ TOP_CASE_TAC \\ simp [] \\

 IF_CASES_TAC >-

 (* state = 0w *)
 (rveq \\ rpt strip_tac' \\ conj_tac

 >- (* memory part *)
 (last_x_assum (assume_tac o is_mem_do_nothing `n`) \\
 simp [state_0w_fext_post_def, GSYM ADD1])

 \\ conj_tac
 >- (* interrupt part *)
 (drule_strip no_interrupt_req \\ fs [ADD1])

 \\ simp [Decode_def, boolify32_def] \\ CONV_TAC v2w_word_bit_list_cleanup

 \\ IF_CASES_TAC >-
 (* LoadUpperConstant *)
 (fs [GSYM ADD1] \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 `(23 >< 9) (circuit facc init fext n).i = 0w` by FULL_BBLAST_TAC \\
 simp [cpu_Next_0w_def, decode_instruction_def, ALU_cleanup_instruction, DecodeReg_imm_cleanup_instruction] \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\ simp [execute_instruction_def] \\
 simp [cpu_eq_def])

 \\ IF_CASES_TAC >-
 (* LoadConstant *)
 (fs [GSYM ADD1] \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, ALU_cleanup_instruction, DecodeReg_imm_cleanup_instruction] \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\ simp [execute_instruction_def] \\

 IF_CASES_TAC \\ simp [cpu_eq_def] \\ IF_CASES_TAC \\ FULL_BBLAST_TAC)

 \\ IF_CASES_TAC >-
 (* ReservedInstr *)
 (simp [GSYM ADD1, circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def] \\
 IF_CASES_TAC >- fs [] \\
 IF_CASES_TAC >- FULL_BBLAST_TAC \\
 simp [ALU_cleanup_instruction, DecodeReg_imm_cleanup_instruction] \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\ simp [execute_instruction_def] \\
 simp [cpu_eq_def])

 \\ IF_CASES_TAC >-
 (* JumpIfZero *)
 (fs [GSYM ADD1] \\ pairarg_tac \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, DecodeReg_imm_cleanup_instruction, ALU_cleanup_instruction] \\

 drule_strip ri2word_DecodeReg_imm \\ fs [] \\ pop_assum kall_tac \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\

 simp [execute_instruction_def] \\
 rw [cpu_eq_def])

 \\ IF_CASES_TAC >-
 (* JumpIfNotZero *)
 (fs [GSYM ADD1] \\ pairarg_tac \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, DecodeReg_imm_cleanup_instruction, ALU_cleanup_instruction] \\

 drule_strip ri2word_DecodeReg_imm \\ fs [] \\ pop_assum kall_tac \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\

 simp [execute_instruction_def] \\
 rw [cpu_eq_def])

 \\ IF_CASES_TAC >-
 (* Interrupt *)
 (fs [GSYM ADD1] \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, DecodeReg_imm_cleanup_instruction, ALU_cleanup_instruction] \\

 drule_strip ri2word_DecodeReg_imm \\ fs [] \\ pop_assum kall_tac \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\

 simp [execute_instruction_def] \\
 rw [cpu_eq_def, ag32Theory.ALU_def])

 (* Ugly case split, because do not want to split top case *)
 \\ Cases_on `DecodeReg_imm (v2w [word_bit 31 (circuit facc init fext n).i], (30 >< 25) (circuit facc init fext n).i)` \\ fs [] >-
 (* ReservedInstr *)
 (* TODO: Very similar to other ReservedInstr case *)
 (drule_strip DecodeReg_imm_Imm \\ fs [v2w_single_1w] \\

 simp [GSYM ADD1, circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def] \\
 simp [ALU_cleanup_instruction, DecodeReg_imm_cleanup_instruction] \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\ simp [execute_instruction_def] \\
 simp [cpu_eq_def])

 \\ drule_strip DecodeReg_imm_Reg \\ fs [v2w_single_0w]
 \\ IF_CASES_TAC >-
 (* Normal *)
 (fs [GSYM ADD1] \\ pairarg_tac \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, DecodeReg_imm_cleanup_instruction, ALU_cleanup_instruction] \\

 drule_strip ri2word_DecodeReg_imm \\ fs [] \\ pop_assum kall_tac \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\

 simp [execute_instruction_def] \\
 simp [cpu_eq_def])

 \\ IF_CASES_TAC >-
 (* Shift *)
 (fs [GSYM ADD1] \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, DecodeReg_imm_cleanup_instruction, ALU_cleanup_instruction] \\

 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\
 simp [execute_instruction_def, ri2word_DecodeReg_imm] \\

 simp [shift_correct] \\ simp [cpu_eq_def] \\ f_equals_tac \\ BBLAST_TAC)

 \\ IF_CASES_TAC >-
 (* StoreMEM *)
 (fs [GSYM ADD1] \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, DecodeReg_imm_cleanup_instruction, ALU_cleanup_instruction] \\

 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\
 simp [execute_instruction_def, ri2word_DecodeReg_imm] \\
 simp [cpu_eq_def])

 \\ IF_CASES_TAC >-
 (* StoreMEMByte *)
 (fs [GSYM ADD1] \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, DecodeReg_imm_cleanup_instruction, ALU_cleanup_instruction] \\

 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\
 simp [execute_instruction_def, ri2word_DecodeReg_imm] \\
 (* Ugly case split: *)
 Cases_on `(1 >< 0) (DecodeReg_imm (word_bit 16 (circuit facc init fext n).i, (15 >< 10) (circuit facc init fext n).i) (circuit facc init fext n))` \\
 fs [LT4_cases] \\ rveq \\ simp [cpu_eq_def])

 \\ IF_CASES_TAC >-
 (* LoadMEM *)
 (fs [GSYM ADD1] \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, ALU_cleanup_instruction, DecodeReg_imm_cleanup_instruction] \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\
 simp [execute_instruction_def] \\
 simp [cpu_eq_def, EncodeReg_imm_DecodeReg_imm] \\
 simp [align_addr_def, DecodeReg_imm_def])

 \\ IF_CASES_TAC >-
 (* LoadMEMByte *)
 (fs [GSYM ADD1] \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, ALU_cleanup_instruction, DecodeReg_imm_cleanup_instruction] \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\
 simp [execute_instruction_def] \\
 simp [cpu_eq_def, EncodeReg_imm_DecodeReg_imm] \\
 simp [align_addr_def, DecodeReg_imm_def] \\ simp [word_extract_def, w2w_w2w, WORD_BITS_COMP_THM])

 \\ IF_CASES_TAC >-
 (* Out *)
 (fs [GSYM ADD1] \\ pairarg_tac \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, DecodeReg_imm_cleanup_instruction, ALU_cleanup_instruction] \\

 drule_strip ri2word_DecodeReg_imm \\ fs [] \\ pop_assum kall_tac \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\

 simp [execute_instruction_def] \\
 simp [cpu_eq_def])

 \\ IF_CASES_TAC >-
 (* In *)
 (simp [GSYM ADD1] \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, ALU_cleanup_instruction, DecodeReg_imm_cleanup_instruction] \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\ simp [execute_instruction_def] \\
 simp [cpu_eq_def])

 \\ IF_CASES_TAC >-
 (* Accelerator *)
 (simp [GSYM ADD1] \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, ALU_cleanup_instruction, DecodeReg_imm_cleanup_instruction] \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\ simp [execute_instruction_def] \\
 simp [cpu_eq_def] \\
 simp [EncodeReg_imm_DecodeReg_imm, DecodeReg_imm_def])

 \\ IF_CASES_TAC >-
 (* Jump *)
 (fs [GSYM ADD1] \\ pairarg_tac \\ simp [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def, DecodeReg_imm_cleanup_instruction, ALU_cleanup_instruction] \\

 drule_strip ri2word_DecodeReg_imm \\ fs [] \\ pop_assum kall_tac \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\

 simp [execute_instruction_def] \\
 simp [cpu_eq_def])

 \\ simp [] \\
 (* ReservedInstr *)
 simp [GSYM ADD1, circuit_def, cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_0w_def, decode_instruction_def] \\

 IF_CASES_TAC >- FULL_BBLAST_TAC \\

 simp [ALU_cleanup_instruction, DecodeReg_imm_cleanup_instruction] \\
 drule_strip ALU_correct \\ pop_assum (fn th => rewrite_tac [th]) \\
 simp [ag32Theory.ALU_def] \\ simp [execute_instruction_def] \\
 simp [cpu_eq_def])

 \\ IF_CASES_TAC >-

 (* state = 1w *)
 (rveq

 \\ IF_CASES_TAC >-
 (* command = 1w *)
 (rpt strip_tac \\ last_assum (mp_tac o is_mem_inst_read `n`) \\
 simp [] \\ strip_tac \\
 drule_strip circuit_read_wait \\ simp [] \\ strip_tac \\
 qexists_tac `m + 2` \\ once_rewrite_tac [DECIDE ``m + 2 + n = SUC (SUC (m + n))``] \\

 once_rewrite_tac [circuit_def] \\ simp [cpu_Next_def] \\ no_mem_error_tac \\
 qpat_x_assum `cpu_eq _ _` (strip_assume_tac o REWRITE_RULE [cpu_eq_def]) \\
 last_assum (mp_tac o is_mem_do_nothing `SUC (m + n)`) \\
 impl_tac >- simp [] \\ strip_tac \\
 simp [cpu_Next_1w_def, delay_write_Next_def] \\
 rfs [cpu_eq_def] \\ drule_strip no_interrupt_req \\ simp [])

 \\ IF_CASES_TAC >-
 (* command = 2w *)
 (rpt strip_tac \\ last_assum (mp_tac o is_mem_data_read `n`) \\
 simp [] \\ strip_tac \\
 drule_strip circuit_read_wait \\ simp [] \\ strip_tac \\
 qexists_tac `m + 2` \\ once_rewrite_tac [DECIDE ``m + 2 + n = SUC (SUC (m + n))``] \\

 once_rewrite_tac [circuit_def] \\ simp [cpu_Next_def] \\ no_mem_error_tac \\
 qpat_x_assum `cpu_eq _ _` (strip_assume_tac o REWRITE_RULE [cpu_eq_def]) \\
 last_assum (mp_tac o is_mem_do_nothing `SUC (m + n)`) \\
 impl_tac >- simp [] \\ strip_tac \\
 rfs [cpu_Next_1w_def, delay_write_Next_def] \\
 drule_strip no_interrupt_req \\

 fs [WORD_DECIDE ``!(w:word3). w <+ 5w <=> (w = 0w \/ w = 1w \/ w = 2w \/ w = 3w \/ w = 4w)``] \\
 simp [cpu_eq_def] \\
 simp [word_ver_var_slice_def] \\ f_equals_tac \\ simp [word_extract_def, w2w_w2w, WORD_BITS_COMP_THM])

 \\ IF_CASES_TAC >-
 (* command = 3w *)
 (rpt strip_tac \\ last_assum (mp_tac o is_mem_data_write `n`) \\

  (* Copied from command = 1w for now: *)
  (simp [] \\ strip_tac \\
  drule_strip circuit_read_wait \\ simp [] \\ strip_tac \\
  qexists_tac `m + 2` \\ once_rewrite_tac [DECIDE ``m + 2 + n = SUC (SUC (m + n))``] \\

  once_rewrite_tac [circuit_def] \\ simp [cpu_Next_def] \\ no_mem_error_tac \\
  qpat_x_assum `cpu_eq _ _` (strip_assume_tac o REWRITE_RULE [cpu_eq_def]) \\
  last_assum (mp_tac o is_mem_do_nothing `SUC (m + n)`) \\
  impl_tac >- simp [] \\ strip_tac \\
  simp [cpu_Next_1w_def, delay_write_Next_def] \\
  rfs [cpu_eq_def] \\ drule_strip no_interrupt_req \\ simp []))

 (* command = 4w *)
 \\ rpt strip_tac \\ last_assum (mp_tac o is_mem_data_flush `n`) \\

  (* Copied from command = 1w for now: *)
  (simp [] \\ strip_tac \\
  drule_strip circuit_read_wait \\ simp [] \\ strip_tac \\
  qexists_tac `m + 2` \\ once_rewrite_tac [DECIDE ``m + 2 + n = SUC (SUC (m + n))``] \\

  once_rewrite_tac [circuit_def] \\ simp [cpu_Next_def] \\ no_mem_error_tac \\
  qpat_x_assum `cpu_eq _ _` (strip_assume_tac o REWRITE_RULE [cpu_eq_def]) \\
  last_assum (mp_tac o is_mem_do_nothing `SUC (m + n)`) \\
  impl_tac >- simp [] \\ strip_tac \\
  simp [cpu_Next_1w_def, delay_write_Next_def] \\
  rfs [cpu_eq_def] \\ drule_strip no_interrupt_req \\ simp []))

 \\ IF_CASES_TAC >-

 (* state = 2w *)
 (rpt strip_tac \\ rveq \\
 fs [is_acc_def] \\ drule_last \\
 drule_strip circuit_acc_wait \\ strip_tac \\
 qpat_x_assum `_ ==> _` mp_tac \\ impl_tac
 >- (rpt strip_tac' \\ first_x_assum (qspec_then `m` mp_tac) \\ impl_tac >- rw [] \\ simp [cpu_eq_def]) \\
 first_x_assum (qspec_then `k` mp_tac) \\ impl_tac >- rw [] \\ simp [] \\ rpt strip_tac \\

 qexists_tac `SUC (SUC k)` \\ once_rewrite_tac [DECIDE ``SUC (SUC k) + n = SUC (SUC (k + n))``] \\
 once_rewrite_tac [circuit_def] \\ simp [cpu_Next_def] \\ no_mem_error_tac \\
 last_assum (assume_tac o is_mem_do_nothing `SUC (k + n)`) \\
 rfs [cpu_Next_2w_def, cpu_eq_def] \\ drule_strip no_interrupt_req \\ simp [])

 (* state = 4w *)
 \\ rpt strip_tac \\ rveq \\

 qpat_assum `is_interrupt_interface _ _ _`
            (strip_assume_tac o SIMP_RULE (srw_ss()) [is_interrupt_interface_def, fext_accessor_circuit_def]) \\
 pop_assum (qspec_then `n` assume_tac) \\ rfs [] \\
 drule_strip circuit_interrupt_wait \\
 qpat_x_assum `cpu_eq _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [cpu_eq_def]) \\
 qexists_tac `SUC (SUC m)` \\ rfs [GSYM ADD_SUC] \\
 last_assum (mp_tac o is_mem_do_nothing `SUC (m + n)`) \\ simp [] \\ disch_then kall_tac \\
 once_rewrite_tac [circuit_def] \\
 simp [cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_4w_def, cpu_eq_def] \\

 fs [is_interrupt_interface_def] \\ last_x_assum (qspec_then `SUC (m + n)` mp_tac) \\ simp []);

val circuit_0 = Q.store_thm("circuit_0",
 `!facc init fext.
   circuit facc init fext 0 = init`,
 simp [circuit_def]);

val circuit_0_next = Q.store_thm("circuit_0_next",
 `!init fext facc c mem_start.
   c = circuit facc init fext /\
   is_mem fext_accessor_circuit c fext /\
   is_mem_start_interface fext mem_start /\
   is_interrupt_interface fext_accessor_circuit c fext /\
   mem_no_errors fext /\

   (c 0).state = 3w /\
   (c 0).command = 0w /\
   ~(c 0).interrupt_req /\
   (fext 0).ready /\
   (fext 0).interrupt_state = InterruptReady /\
   ~(fext 0).interrupt_ack ==>
   ?m. cpu_eq (c m)
              (c 0 with <| command := 1w;
                           state := 1w;
                           R := (0w =+ mem_start) (c 0).R;
                           mem_start := mem_start;
                           PC := mem_start + 64w |>) /\
       (fext m).ready /\
       (fext m).mem = (fext 0).mem /\
       (fext m).interrupt_state = InterruptReady /\
       (fext m).io_events = (fext 0).io_events /\
       ~(fext m).interrupt_ack`,
 rewrite_tac [is_mem_start_interface_def] \\ rpt strip_tac \\ rveq \\
 drule_strip circuit_mem_start_ready_wait \\
 qpat_x_assum `cpu_eq _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [cpu_eq_def]) \\
 fs [circuit_0] \\

 qexists_tac `SUC n` \\
 last_assum (mp_tac o is_mem_do_nothing `n`) \\ simp [] \\ disch_then kall_tac \\

 rfs [circuit_def, cpu_Next_def] \\ no_mem_error_tac \\ drule_strip no_interrupt_req \\
 simp [cpu_Next_3w_def, cpu_eq_def]);

val addr_add = Q.prove(
 `!(w:word32).
   (31 >< 2) w @@ (0w:word2) + 1w = (31 >< 2) w @@ (1w:word2) /\
   (31 >< 2) w @@ (0w:word2) + 2w = (31 >< 2) w @@ (2w:word2) /\
   (31 >< 2) w @@ (0w:word2) + 3w = (31 >< 2) w @@ (3w:word2)`,
 BBLAST_TAC);

val addr_concat = Q.prove(
 `!(w1:word30) (w2:word2) (w3:word30) (w4:word2).
   (w1 @@ w2 = w3 @@ w4) <=> (w1 = w3 /\ w2 = w4)`,
 BBLAST_TAC);

val addr_split = Q.prove(
 `!(w1:word32).
   w1 = (31 >< 2) w1 @@ (1 >< 0) w1`,
 BBLAST_TAC);

val REL_circuit_SUC = Q.store_thm("REL_circuit_SUC",
 `!n c init fext facc s.
   c = circuit facc init fext /\
   is_mem fext_accessor_circuit c fext /\
   is_acc accelerator_f c /\
   is_interrupt_interface fext_accessor_circuit c fext /\
   mem_no_errors fext /\
   REL (fext n) (c n) s ==>
   ?m. m <> 0 /\ REL (fext (n + m)) (c (n + m)) (Next s)`,
 rpt strip_tac \\
 pop_assum (STRIP_ASSUME_TAC o REWRITE_RULE [REL_def]) \\

 simp [Next_def, GSYM word_at_addr_def, GSYM align_addr_def] \\

 qpat_x_assum `t.i = _` (fn th => GSYM th |> ASSUME_TAC) \\
 `(word_at_addr s.MEM (align_addr s.PC)) = (circuit facc init fext n).i` by metis_tac [] \\

 simp [] \\ rveq \\
 drule_strip (SIMP_RULE (srw_ss()) [] circuit_next) \\
 qpat_abbrev_tac `c = circuit _ _ _` \\

 Cases_on `Decode (c n).i`

 >- (* Accelerator *)
 (PairCases_on `p` \\ simp [Run_def, dfn'Accelerator_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\

 qunabbrev_tac `c` \\
 drule_strip (SIMP_RULE (srw_ss()) [] circuit_next) \\
 qpat_abbrev_tac `c = circuit _ _ _` \\
 first_x_assum (qspec_then `m + (n + 1)` mp_tac) \\
 simp [cpu_eq_def] \\ strip_tac \\

 qexists_tac `m + m' + 1` \\ fs [REL_def] \\
 f_equals_tac \\ Cases_on `p1` \\ simp [EncodeReg_imm_def, ri2word_def])

 >- (* In *)
 (simp [Run_def, dfn'In_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\
 qexists_tac `m + 1` \\ fs [REL_def])

 >- (* Interrupt *)
 (simp [Run_def, dfn'Interrupt_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\

 (* hacky: additional waiting needed for this instruction: *)
 qunabbrev_tac `c` \\
 drule_strip (SIMP_RULE (srw_ss()) [] circuit_next) \\
 qpat_abbrev_tac `c = circuit _ _ _` \\

 first_x_assum (qspec_then `m + (n + 1)` mp_tac) \\
 simp [cpu_eq_def] \\ strip_tac \\

 qexists_tac `m + m' + 1` \\ fs [REL_def])

 >- (* Jump *)
 (PairCases_on `p` \\ simp [Run_def, dfn'Jump_def] \\
 pairarg_tac \\

 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\

 drule_strip ALU_state_eq_after \\
 qexists_tac `m + 1` \\ fs [REL_def])

 >- (* JumpIfNotZero *)
 (PairCases_on `p` \\ simp [Run_def, dfn'JumpIfNotZero_def, incPC_def] \\
 (* pairarg_tac do not match ALU here ... *)
 qpat_abbrev_tac `alu = ag32$ALU _ _` \\
 Cases_on `alu` \\ pop_assum (assume_tac o SYM o ONCE_REWRITE_RULE [markerTheory.Abbrev_def]) \\

 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\

 drule_strip ALU_state_eq_after \\
 qexists_tac `m + 1` \\ IF_CASES_TAC \\ fs [REL_def] \\ simp [ri2word_def])

 >- (* JumpIfZero *)
 (PairCases_on `p` \\ simp [Run_def, dfn'JumpIfZero_def, incPC_def] \\
 (* pairarg_tac do not match ALU here ... *)
 qpat_abbrev_tac `alu = ag32$ALU _ _` \\
 Cases_on `alu` \\ pop_assum (assume_tac o SYM o ONCE_REWRITE_RULE [markerTheory.Abbrev_def]) \\

 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\

 drule_strip ALU_state_eq_after \\
 qexists_tac `m + 1` \\ IF_CASES_TAC \\ fs [REL_def] \\ simp [ri2word_def])

 >- (* LoadConstant *)
 (PairCases_on `p` \\ simp [Run_def, dfn'LoadConstant_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\
 qexists_tac `m + 1` \\ fs [REL_def])

 >- (* LoadMEM *)
 (PairCases_on `p` \\ simp [Run_def, dfn'LoadMEM_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\
 qexists_tac `m + 1` \\ fs [REL_def, word_at_addr_def] \\
 Cases_on `p1` \\ fs [align_addr_def, EncodeReg_imm_def, ri2word_def])

 >- (* LoadMEMByte *)
 (PairCases_on `p` \\ simp [Run_def, dfn'LoadMEMByte_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\
 fs [BBLAST_PROVE ``!(w:word32). (1 >< 0) w <₊ (5w:word3)``, BBLAST_PROVE ``!(w:word32). (1 >< 0) w <> (4w:word3)``] \\
 qexists_tac `m + 1` \\ fs [REL_def] \\

 f_equals_tac \\

 simp [word_ver_var_slice_def] \\
 (* Ugly and inefficient: *)
 `(1 >< 0) (EncodeReg_imm p1 (c n)) <=+ (3w:word3)` by BBLAST_TAC \\
 Cases_on `p1` \\ rfs [word_at_addr_def, align_addr_def, EncodeReg_imm_def, ri2word_def] \\
 fs [WORD_DECIDE ``!(w:word3). w <=+ 3w <=> (w = 0w \/ w = 1w \/ w = 2w \/ w = 3w)``] \\

 rpt (DEP_ONCE_REWRITE_TAC [word_extract_concat_right] \\ (conj_tac >- simp [])) \\
 DEP_REWRITE_TAC [word_extract_concat_left] \\ simp [word_extract_id] \\
 f_equals_tac \\ pop_assum mp_tac \\ BBLAST_TAC)

 >- (* LoadUpperConstant *)
 (PairCases_on `p` \\ simp [Run_def, dfn'LoadUpperConstant_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\
 qexists_tac `m + 1` \\ fs [REL_def])

 >- (* Normal *)
 (PairCases_on `p` \\ simp [Run_def, dfn'Normal_def, norm_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\
 (* Följer inte generella mönstret: *)
 pairarg_tac \\ simp [] \\ rpt strip_tac \\
 qexists_tac `m + 1` \\ drule_strip ALU_state_eq_after \\
 drule_strip ALU_state_eq_after \\
 fs [REL_def])

 >- (* Out *)
 (PairCases_on `p` \\ simp [Run_def, dfn'Out_def, norm_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\
 (* Följer inte generella mönstret: *)
 pairarg_tac \\ simp [] \\ rpt strip_tac \\
 qexists_tac `m + 1` \\
 drule_strip ALU_state_eq_after \\
 fs [REL_def] \\ (* lazy: *) BBLAST_TAC)

 >- (* ReservedInstr *)
 (simp [Run_def, dfn'ReservedInstr_def] \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\
 qexists_tac `1` \\ fs [REL_def])

 >- (* Shift *)
 (PairCases_on `p` \\ simp [Run_def, dfn'Shift_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\
 qexists_tac `m + 1` \\ fs [REL_def])

 >- (* StoreMEM *)
 (PairCases_on `p` \\ simp [Run_def, dfn'StoreMEM_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\
 qexists_tac `m + 1` \\ fs [REL_def] \\

 rw [mem_update_def] \\ fs [word_at_addr_def, align_addr_def, APPLY_UPDATE_THM] \\
 simp [addr_add, addr_concat])

 \\ (* StoreMEMByte *)
 PairCases_on `p` \\ simp [Run_def, dfn'StoreMEMByte_def, incPC_def] \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\
 reverse IF_CASES_TAC >- fs [] \\ disch_then drule_strip \\
 simp [state_0w_fext_post_def, cpu_eq_def] \\ rpt strip_tac \\
 qexists_tac `m + 1` \\ fs [REL_def] \\

 fs [word_at_addr_def, align_addr_def] \\
 qspec_then `ri2word p1 s` assume_tac addr_split \\
 pop_assum (fn th => CONV_TAC ((RHS_CONV o ONCE_REWRITE_CONV) [th])) \\

 Cases_on `(1 >< 0) (ri2word p1 s)` \\ fs [LT4_cases] \\ rveq \\

 simp [mem_update_def, addr_add, addr_concat] \\
 match_mp_tac EQ_EXT \\ rw [APPLY_UPDATE_THM] \\
 BBLAST_PROVE_TAC);

val REL_circuit = Q.store_thm("REL_circuit",
 `!m n ni c s facc init fext.
   c = circuit facc init fext /\
   is_mem fext_accessor_circuit c fext /\
   is_acc accelerator_f c /\
   is_interrupt_interface fext_accessor_circuit c fext /\
   mem_no_errors fext /\
   REL (fext ni) (c ni) (FUNPOW Next n s) ==>
   ?mi. (mi = 0 <=> m = 0) /\ REL (fext (ni + mi)) (c (ni + mi)) (FUNPOW Next (n + m) s)`,
 simp [] \\ Induct \\ rpt strip_tac
 >- (qexists_tac `0` \\ fs [circuit_def]) \\
 drule_first \\
 drule_strip (SIMP_RULE (srw_ss()) [] REL_circuit_SUC) \\
 qexists_tac `mi + m'` \\
 once_rewrite_tac [DECIDE ``SUC m + n = SUC (m + n)``] \\ rewrite_tac [FUNPOW_SUC] \\
 fs []);

(* Strange FUNPOW in conclusion because that's the form we need in main thm *)
val INIT_circuit = Q.store_thm("INIT_circuit",
 `!c s facc init fext mem_start.
   c = circuit facc init fext /\
   is_mem fext_accessor_circuit c fext /\
   is_acc accelerator_f c /\
   is_interrupt_interface fext_accessor_circuit c fext /\
   is_mem_start_interface fext mem_start /\
   mem_no_errors fext /\

   INIT (fext 0) init s /\
   INIT_ISA s mem_start ==>
   ?m. REL (fext m) (c m) (FUNPOW Next 0 s)`,
 simp [INIT_def, INIT_ISA_def] \\ rpt strip_tac \\
 drule_strip (SIMP_RULE (srw_ss()) [] circuit_0_next) \\
 impl_tac >- simp [circuit_def] \\ strip_tac \\ fs [circuit_0, cpu_eq_def] \\

 drule_strip (SIMP_RULE (srw_ss()) [] circuit_next) \\
 pop_assum (qspec_then `m` mp_tac) \\ fs [] \\ strip_tac \\

 qexists_tac `m' + m` \\ fs [cpu_eq_def, REL_def, INIT_R_def] \\
 match_mp_tac EQ_EXT \\ gen_tac \\ Cases_on `x = 0w` \\ simp [UPDATE_def]);

val INIT_REL_circuit_lem = Q.prove(
 `!n c s facc init fext mem_start.
   c = circuit facc init fext /\

   INIT (fext 0) init s /\
   INIT_ISA s mem_start /\

   is_mem fext_accessor_circuit c fext /\
   is_interrupt_interface fext_accessor_circuit c fext /\
   is_mem_start_interface fext mem_start /\
   mem_no_errors fext /\
   is_acc accelerator_f c ==>
   ?m. REL (fext m) (c m) (FUNPOW Next n s)`,
 simp [] \\ rpt strip_tac \\
 drule_strip (SIMP_RULE (bool_ss) [] INIT_circuit) \\
 drule_strip (SIMP_RULE (srw_ss()) [] REL_circuit) \\
 pop_assum (qspec_then `n` strip_assume_tac) \\
 qexists_tac `m + mi` \\ fs []);

val INIT_REL_circuit = save_thm("INIT_REL_circuit",
 SIMP_RULE (srw_ss()) [] INIT_REL_circuit_lem);

val _ = export_theory ();
