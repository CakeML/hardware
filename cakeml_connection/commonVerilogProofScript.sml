open hardwarePreamble;

open verilogTheory verilogTranslatorTheory moduleTranslatorTheory;
open ag32MachineTheory ag32EqTheory ag32VerilogTheory;

open ag32_machine_configTheory;

open verilogTranslatorLib;

val _ = new_theory "commonVerilogProof";

val _ = guess_lengths ();
val _ = prefer_num ();

val exit_code_0_def = Define `
 exit_code_0 vs fextv <=>
  erun fextv <| vars := vs |> (ArrayIndex (Var "R") [Const (w2ver (1w:word6))]) = INR (w2ver (0w:word32))`;

(* Should be replaced by event-based definition? *)
val is_halted_def = Define `
 is_halted fin (_, _, config') <=>
 let num_ffis = LENGTH (THE config'.ffi_names) in
  (mget_var fin "PC") = INR (n2ver (ffi_jumps_offset + (num_ffis + 1) * ffi_offset))`;

val after_R_1w_lift = Q.store_thm("after_R_1w_lift",
 `!env (hol_s:state_circuit) (s:ag32_state) fext fextv n.
   lift_fext fextv fext /\ relM hol_s env /\ hol_s.R 1w = s.R 1w /\ exit_code_0 env (fextv n) ==>
   s.R 1w = 0w`,
 rw [exit_code_0_def] \\
 assume_tac (hol2hardware_exp ``s:state_circuit`` ``(s:state_circuit).R 1w`` |> GEN_ALL) \\
 fs [Eval_def] \\

 drule_strip relM_relS \\
 fs [lift_fext_relS_fextv_fext] \\
 last_x_assum (qspec_then `n` assume_tac) \\
 first_x_assum (qspecl_then [`hol_s`, `fext n`, `env`, `fextv n`, `<| vars := env |>`] mp_tac) \\

 impl_tac >- (fs [relS_def, relS_var_def, get_var_def] \\ metis_tac []) \\
 strip_tac \\ fs [WORD_def] \\ rveq \\ fs [w2ver_bij] \\ metis_tac []);

val after_R_lift = Q.store_thm("after_R_lift",
 `!env (hol_s:state_circuit) (s:ag32_state) fext fextv n.
   lift_fext fextv fext /\ relM hol_s env /\ hol_s.R = s.R /\ exit_code_0 env (fextv n) ==>
   s.R 1w = 0w`,
 metis_tac [after_R_1w_lift]);

(* Move *)
val get_mem_word_word_at_addr = Q.store_thm("get_mem_word_word_at_addr",
 `!mem addr. get_mem_word mem addr = word_at_addr mem addr`,
 rw [word_at_addr_def, ag32_memoryTheory.get_mem_word_def]);

val is_prefix_extract_writes = Q.store_thm("is_prefix_extract_writes",
 `!l1 l2 fd. l1 ≼ l2 ==> extract_writes fd l1 ≼ extract_writes fd l2`,
 Induct >- rw [ag32_basis_ffiProofTheory.extract_writes_def] \\

 rw [] \\ every_case_tac \\ fs [] \\
 rveq \\ first_x_assum drule \\ disch_then (qspec_then `fd` assume_tac) \\
 fs [ag32_basis_ffiProofTheory.extract_writes_def] \\ rw []);

val _ = export_theory ();
