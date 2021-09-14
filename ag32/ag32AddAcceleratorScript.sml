open hardwarePreamble;

open arithmeticTheory;

open translatorTheory ag32Theory ag32MachineTheory;

val _ = new_theory "ag32AddAccelerator";

(*val _ = guess_lengths ();
val _ = prefer_num ();

(** Machine definition -- example accelerator that just does integer addition inefficiently **)

Definition addacc_next_def:
 addacc_next (fext:ext) (s:state_circuit) (s':state_circuit) =
  if s'.acc_arg_ready then
    s' with <| acc_state := 0w; acc_res_ready := F |>
  else
   case s'.acc_state of
      0w => s' with acc_state := 1w
(*  | 1w => s' with acc_state := 2w *)
    | 1w => s' with <| acc_res_ready := T;
                       acc_res := w2w ((31 >< 16) s'.acc_arg + (15 >< 0) s'.acc_arg) |>
    | _ => s'
End

Definition ag32_def:
 ag32 = ag32_facc addacc_next
End

Theorem ag32_trans:
 ag32 = mk_module (procs [cpu_Next; addacc_next]) (procs []) ag32_init
Proof
 simp [ag32_def, ag32_facc_def]
QED

(** Is accelerator **)

Triviality execute_instruction_const:
 (execute_instruction wV aV bV PC_next fext s).acc_state = s.acc_state
Proof
 rw [execute_instruction_def, shift_def] \\ WORD_DECIDE_TAC
QED

Triviality decode_instruction_const:
 (decode_instruction s).acc_state = s.acc_state ∧
 (decode_instruction s).acc_arg_ready = s.acc_arg_ready
Proof
 rw [decode_instruction_def]
QED

Triviality lt_16:
 ∀n. n < 16 ⇔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15
Proof
 ntac 8 (Cases_on ‘n’ >- simp [] \\ Cases_on ‘n'’ >- simp []) \\ simp []
QED

Triviality ALU_const:
 ∀args s. (ALU args s).acc_state = s.acc_state ∧
          (ALU args s).acc_arg_ready = s.acc_arg_ready
Proof
 PairCases \\ gen_tac \\ Cases_on ‘args0’ \\ fs [] \\
 pop_assum (strip_assume_tac o REWRITE_RULE [lt_16]) \\
 simp [ALU_def]
QED

Theorem cpu_Next_const:
 (cpu_Next fext s s').acc_state = s'.acc_state
Proof
 rw [cpu_Next_def,
     cpu_Next_0w_def, execute_instruction_const, decode_instruction_const, ALU_const,
     cpu_Next_1w_def, delay_write_Next_def,
     cpu_Next_2w_def, cpu_Next_3w_def, cpu_Next_4w_def]
QED

Triviality addacc_next_next:
  !fext fbits n.
   let c = ag32 fext fbits in
   if (c n).acc_arg_ready then
    (c (SUC n)).acc_state = 0w /\
    ~(c (SUC n)).acc_res_ready
   else
    case (c n).acc_state of
      0w =>
       (c (SUC n)).acc_state = 1w /\
       (c (SUC n)).acc_res_ready = (c n).acc_res_ready
    | 1w =>
       (c (SUC n)).acc_state = (c n).acc_state /\
       (c (SUC n)).acc_res_ready /\
       (c (SUC n)).acc_res = accelerator_f (c n).acc_arg
    | _ => T
Proof
 rw [ag32_def, ag32_facc_def, mk_module_def, mk_circuit_def, procs_def,
     addacc_next_def, cpu_Next_const] \\ gvs []

           , ,  accelerator_f_def]
QED

val addacc_next_next = addacc_next_next |> SIMP_RULE bool_ss [LET_THM];

Theorem is_acc_addacc:
 !fext fbits. is_acc accelerator_f (ag32 fext fbits)
Proof
 rpt strip_tac \\ simp [is_acc_def] \\ qexists_tac `2` \\ gen_tac \\ strip_tac \\
 qspecl_then [`init`, `fext`] assume_tac addacc_next_next \\

 first_assum (qspec_then `n + 2` mp_tac) \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\

 simp [ADD1] \\ rpt strip_tac' \\ rpt conj_tac \\ rpt strip_tac'

 >- (fs [DECIDE ``!l. l < 2 <=> l = 0 \/ l = 1``] \\ rveq \\ first_x_assum (qspec_then `1` mp_tac) \\
    simp [] \\ strip_tac \\ fs [])

 \\ first_assum (qspec_then `0` assume_tac) \\ first_x_assum (qspec_then `1` assume_tac) \\ fs [] \\ rfs []
QED*)

val _ = export_theory ();
