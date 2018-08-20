open preamble;

open arithmeticTheory;

open ag32Theory ag32MachineTheory;

val _ = new_theory "ag32AddAccelerator";

guess_lengths ();
prefer_num ();

(* Accelerator that just does integer addition inefficiently *)

val addacc_next_def = Define `
 addacc_next s =
  if s.acc_arg_ready then
    s with <| acc_state := 0w; acc_res_ready := F |>
  else
   case s.acc_state of
      0w => s with acc_state := 1w
(*  | 1w => s with acc_state := 2w *)
    | 1w => s with <| acc_res_ready := T;
                      acc_res := w2w ((31 >< 16) s.acc_arg + (15 >< 0) s.acc_arg) |>
    | _ => s`;

val addacc_next_next = Q.prove(
 `!init fext n.
   let c = circuit addacc_next init fext in
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
    | _ => T`,
 rw [circuit_def, addacc_next_def, accelerator_f_def])
 |> SIMP_RULE bool_ss [LET_THM];

val is_acc_addacc = Q.store_thm("is_acc_addacc",
 `!init fext.
   is_acc accelerator_f (circuit addacc_next init fext)`,
 rpt strip_tac \\ simp [is_acc_def] \\ qexists_tac `2` \\ gen_tac \\ strip_tac \\
 qspecl_then [`init`, `fext`] assume_tac addacc_next_next \\

 first_assum (qspec_then `n + 2` mp_tac) \\
 first_assum (qspec_then `n + 1` mp_tac) \\
 first_x_assum (qspec_then `n` mp_tac) \\

 simp [ADD1] \\ rpt strip_tac' \\ rpt conj_tac \\ rpt strip_tac'

 >- (fs [DECIDE ``!l. l < 2 <=> l = 0 \/ l = 1``] \\ rveq \\ first_x_assum (qspec_then `1` mp_tac) \\
    simp [] \\ strip_tac \\ fs [])

 \\ first_assum (qspec_then `0` assume_tac) \\ first_x_assum (qspec_then `1` assume_tac) \\ fs [] \\ rfs []);

val _ = export_theory ();
