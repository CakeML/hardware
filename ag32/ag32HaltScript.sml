open hardwarePreamble;

open ag32MachineTheory ag32EqTheory;

open ag32StepLib;

val _ = new_theory "ag32Halt";

val _ = guess_lengths ();
val _ = prefer_num ();

(* This file is thrown together and should not depend on ag32EqTheory *)

val Encode_Jump_decode_instruction = Q.store_thm("Encode_Jump_decode_instruction",
 `!s. s.i = Encode (Jump (fAdd,0w,Imm 0w)) ==> decode_instruction s = s with instruction := 9w`,
 rw [ag32Theory.Encode_def, ag32Theory.enc_def, ag32Theory.ri2bits_def] \\
 rw [decode_instruction_def]);

val circuit_halt_compute_step = Q.store_thm("circuit_halt_compute_step",
`!n c init fext facc.
 c = circuit facc init fext /\
 is_mem fext_accessor_circuit c fext /\
 is_interrupt_interface fext_accessor_circuit c fext /\
 (c n).state = 0w /\
 (c n).i = word_at_addr (fext n).mem ((c n).PC) /\
 (c n).command = 0w /\
 ~(c n).interrupt_req /\
 (fext n).ready /\
 (fext n).interrupt_state = InterruptReady /\
 (word_at_addr (fext n).mem (c n).PC = Encode (Jump (fAdd, 0w, Imm 0w)))
 ==>
 ?carryflag overflowflag.
 (fext (n + 1)).mem = (fext n).mem ∧
 (fext (n + 1)).ready = (fext n).ready ∧
 (fext (n + 1)).interrupt_state = InterruptReady /\
 (fext (n + 1)).io_events = (fext n).io_events ∧
 cpu_eq (c (n + 1))
        (c n with
           <|state := 1w; R := (0w =+ (c n).PC + 4w) (c n).R;
             CarryFlag := carryflag; OverflowFlag := overflowflag;
             command := 1w|>)`,
 rpt strip_tac \\ rveq \\

 (* mem *)
 last_assum (assume_tac o is_mem_do_nothing `n`) \\
 fs [arithmeticTheory.ADD1] \\
 pop_assum kall_tac \\

 (* interrupt *)
 drule_strip no_interrupt_req \\ fs [arithmeticTheory.ADD1] \\

 simp [GSYM arithmeticTheory.ADD1, circuit_def, cpu_Next_def] \\
 no_mem_error_tac \\
 simp [cpu_Next_0w_def, Encode_Jump_decode_instruction, DecodeReg_imm_def] \\

 fs [ag32Theory.Encode_def, ag32Theory.enc_def, ag32Theory.ri2bits_def] \\
 simp [ALU_def, execute_instruction_def] \\

 rw [cpu_eq_def] \\ blastLib.BBLAST_TAC);

val circuit_halt_compute_step2_SUC = Q.store_thm("circuit_halt_compute_step2_SUC",
`!n c init fext facc.
 c = circuit facc init fext /\
 mem_no_errors fext /\
 (c n).state = 1w /\
 (c n).command = 0w /\
 (c n).do_delay_write = 5w /\
 ~(c n).do_interrupt /\
 ~(c n).interrupt_req /\
 (fext n).ready /\
 (fext n).interrupt_state = InterruptReady ==>
 cpu_eq (c (SUC n)) ((c n) with <| state := 0w; i := (fext n).inst_rdata |>)`,
 rw [circuit_def] \\ simp [cpu_Next_def] \\ no_mem_error_tac \\
 simp [cpu_Next_1w_def, delay_write_Next_def, cpu_eq_def]);

val circuit_halt_compute_step2 = Q.store_thm("circuit_halt_compute_step2",
`!n c init fext facc s.
 c = circuit facc init fext /\
 is_mem fext_accessor_circuit c fext /\
 is_interrupt_interface fext_accessor_circuit c fext /\
 (c n).state = 1w /\
 (c n).command = 1w /\
 (c n).do_delay_write = 5w /\
 ~(c n).do_interrupt /\
 ~(c n).interrupt_req /\
 (fext n).ready /\
 (fext n).interrupt_state = InterruptReady
 ==>
 ?m. (fext (n + m)).mem = (fext n).mem ∧
     (fext (n + m)).ready = (fext n).ready ∧
     (fext (n + m)).interrupt_state = InterruptReady /\
     (!l. l <= m ==> (fext (n + l)).io_events = (fext n).io_events /\
                     (c (n + l)).R = (c n).R /\
                     (c (n + l)).PC = (c n).PC) /\
     cpu_eq (c (n + m))
            (c n with
               <|command := 0w;
                 state := 0w;
                 i := word_at_addr (fext n).mem (align_addr (c n).PC) |>)`,
 (* copied from circuit_next more or less, should make more modular thms instead... *)
 rpt strip_tac' \\ last_assum (mp_tac o is_mem_inst_read `n`) \\
 simp [] \\ strip_tac \\
 drule_strip is_mem_mem_no_errors \\
 drule_strip circuit_read_wait \\ simp [] \\ strip_tac \\
 qpat_x_assum `cpu_eq _ _` (strip_assume_tac o REWRITE_RULE [cpu_eq_def]) \\ rfs [] \\

 qexists_tac `m + 2` \\ once_rewrite_tac [DECIDE ``m + 2 + n = SUC (SUC (m + n))``] \\

 drule_strip (SIMP_RULE (srw_ss()) [] circuit_halt_compute_step2_SUC) \\
 pop_assum (strip_assume_tac o REWRITE_RULE [cpu_eq_def]) \\ rfs [] \\

 last_assum (mp_tac o is_mem_do_nothing `SUC (m + n)`) \\
 impl_tac >- simp [] \\ strip_tac \\
 drule_strip no_interrupt_req \\ simp [cpu_eq_def] \\

 rpt strip_tac' \\ `l <= SUC m \/ l = m + 2` by decide_tac \\
 fs [arithmeticTheory.ADD1] \\ first_x_assum (qspec_then `SUC m` mp_tac) \\ 
 simp [arithmeticTheory.ADD1]);

val halt_inv_def = Define `
 halt_inv c fext n <=>
  (c n).i = word_at_addr (fext n).mem (align_addr (c n).PC) /\
  (c n).state = 0w /\
  (c n).command = 0w /\
  ~(c n).interrupt_req /\
  (fext n).ready /\
  (fext n).interrupt_state = InterruptReady /\
  (c n).do_delay_write = 5w ∧
  ¬(c n).do_interrupt`;

val byte_aligned_align_addr = Q.store_thm("byte_aligned_align_addr",
 `!(w:word32). byte_aligned w ==> align_addr w = w`,
 rw [alignmentTheory.byte_aligned_def, alignmentTheory.aligned_def,
     alignmentTheory.align_def, align_addr_def] \\
 blastLib.FULL_BBLAST_TAC);

val circuit_halt_compute_step_full = Q.store_thm("circuit_halt_compute_step_full",
 `!n c init fext facc s.
   c = circuit facc init fext /\
   is_mem fext_accessor_circuit c fext /\
   is_interrupt_interface fext_accessor_circuit c fext /\
   halt_inv c fext n /\
   byte_aligned (c n).PC /\
   word_at_addr (fext n).mem (c n).PC = Encode (Jump (fAdd,0w,Imm 0w))
   ==>
   ?m. halt_inv c fext (SUC (n + m)) /\
       (fext (SUC (n + m))).mem = (fext n).mem /\
       (fext (SUC (n + m))).ready = (fext n).ready /\
       (c (SUC (n + m))).PC = (c n).PC /\
       (!l. l <= SUC m ==> (fext (n + l)).io_events = (fext n).io_events /\
                           (c (n + l)).R 1w = (c n).R 1w /\
                           (c (n + l)).PC = (c n).PC)`,
 rpt strip_tac \\
 qpat_x_assum `halt_inv _ _ _` (STRIP_ASSUME_TAC o REWRITE_RULE [halt_inv_def]) \\

 rveq \\
 drule_strip (SIMP_RULE (srw_ss()) [] circuit_halt_compute_step2) \\
 disch_then (qspec_then `n + 1` mp_tac) \\

 drule_strip (SIMP_RULE (srw_ss()) [] circuit_halt_compute_step) \\

 qpat_abbrev_tac `c = circuit _ _ _` \\

 simp [byte_aligned_align_addr] \\
 disch_then (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss()) [cpu_eq_def]) \\

 simp [] \\
 strip_tac \\

 qexists_tac `m` \\ fs [halt_inv_def, cpu_eq_def, arithmeticTheory.ADD1,
                        combinTheory.APPLY_UPDATE_THM] \\
 rpt strip_tac' \\ `l = 0 \/ (0 < l /\ l <= m) \/ l = m + 1` by decide_tac \\ fs []
 >- (first_x_assum (qspec_then `l - 1` mp_tac) \\ simp [combinTheory.APPLY_UPDATE_THM])
 >- simp [combinTheory.APPLY_UPDATE_THM]);

val circuit_halt_compute_step_full_actual = Q.store_thm("circuit_halt_compute_step_full_actual",
 `!n m c init fext facc s.
   c = circuit facc init fext /\
   is_mem fext_accessor_circuit c fext /\
   is_interrupt_interface fext_accessor_circuit c fext /\
   byte_aligned (c n).PC /\
   word_at_addr (fext n).mem (c n).PC = Encode (Jump (fAdd,0w,Imm 0w)) /\
   halt_inv c fext n
   ==>
   ?l. m <= l /\
       halt_inv c fext (n + l) /\
       (fext (n + l)).mem = (fext n).mem ∧
       (c (n + l)).PC = (c n).PC ∧
       (!k. k <= l ==> (fext (n + k)).io_events = (fext n).io_events /\
                       (c (n + k)).R 1w = (c n).R 1w /\
                       (c (n + k)).PC = (c n).PC)`,
 rpt strip_tac \\ rveq \\ Induct_on `m` \\ rpt strip_tac >- (qexists_tac `0` \\ rw []) \\

 pop_assum strip_assume_tac \\
 drule_strip (SIMP_RULE (srw_ss()) [] circuit_halt_compute_step_full) \\
 impl_tac >- simp [] \\ strip_tac \\

 qexists_tac `l + m' + 1` \\ fs [arithmeticTheory.ADD1] \\
 rpt strip_tac' \\ 
 last_assum (qspec_then `l` mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
 fs [] \\

 Cases_on `k ≤ l`
 >- metis_tac []
 \\ fs []
 \\ `l ≤ k` by decide_tac
 \\ ntac 2 (first_x_assum (qspec_then `k - l` mp_tac))
 \\ simp []);

val circuit_halt_compute_step_full_actual' = Q.store_thm("circuit_halt_compute_step_full_actual'",
 `!n m c init fext facc s.
   c = circuit facc init fext /\
   is_mem fext_accessor_circuit c fext /\
   is_interrupt_interface fext_accessor_circuit c fext /\
   byte_aligned (c n).PC /\
   word_at_addr (fext n).mem (c n).PC = Encode (Jump (fAdd,0w,Imm 0w)) /\
   halt_inv c fext n
   ==>
   (c (n + m)).PC = (c n).PC /\
   (fext (n + m)).io_events = (fext n).io_events /\
   (c (n + m)).R 1w = (c n).R 1w`,
 metis_tac [circuit_halt_compute_step_full_actual]);

val _ = export_theory ();

