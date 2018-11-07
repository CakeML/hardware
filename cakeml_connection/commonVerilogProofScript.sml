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
val ag32_is_halted_def = Define `
 ag32_is_halted fin conf <=>
 (mget_var fin "PC") = INR (w2ver conf.halt_pc)`;

val after_R_lift = Q.store_thm("after_R_lift",
 `!env (hol_s:state_circuit) (s:ag32_state) fext fextv n.
   lift_fext fextv fext /\ relM hol_s env /\ hol_s.R = s.R /\ exit_code_0 env (fextv n) ==>
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

(* Unnecessary *)
val ag32_verilog_types_def = Define `
 ag32_verilog_types = relMtypes ++ ag32types`;

val _ = export_theory ();
