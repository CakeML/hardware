open hardwarePreamble;

open newTranslatorTheory newTranslatorCoreLib;

val _ = new_theory "FSMCircuits";

val _ = prefer_num ();

(** FSM example from the Internet **)
(* https://personal.utdallas.edu/~zhoud/EE%203120/Verilog%20HDL%20(2).pdf *)

(* Moore variant *)

Datatype:
 moore_state = <| (* communication vars: *)     state : word4;
                  (* non-communication vars: *) out_seq : bool; next_state : word4 |>
End

Datatype:
 moore_ext_state = <| in_seq : bool |>
End

(*
parameter S0 = 4'b0001, S1 = 4'b0010, S2 = 4'b0100, S3 = 4'b1000;

S0 = 1
S1 = 2
S2 = 4
S3 = 8
*)

Definition moore_comb1_def:
 moore_comb1 fext s s' =
  case s.state of
    1w => if fext.in_seq then (s' with next_state := 2w) else (s' with next_state := 1w)
  | 2w => if ~fext.in_seq then (s' with next_state := 4w) else (s' with next_state := 2w)
  | 4w => if fext.in_seq then (s' with next_state := 8w) else (s' with next_state := 1w)
  | 8w => if fext.in_seq then (s' with next_state := 2w) else (s' with next_state := 4w)
  | _ => s' with next_state := 1w (* X assignment here would be better... but follow original strictly here! *)
End

Theorem moore_comb1_alt:
 moore_comb1 fext s s' =
  s' with next_state :=
   case s.state of
     1w => if fext.in_seq then 2w else 1w
   | 2w => if fext.in_seq then 2w else 4w
   | 4w => if fext.in_seq then 8w else 1w
   | 8w => if fext.in_seq then 2w else 4w
   | _ => 1w
Proof
 rw [moore_comb1_def] \\ fs []
QED

Definition moore_comb2_def:
 moore_comb2 (fext:moore_ext_state) s s' =
  case s.state of
    1w => s' with out_seq := F
  | 2w => s' with out_seq := F
  | 4w => s' with out_seq := F
  | 8w => s' with out_seq := T
  | _ => s' with out_seq := F (* should be X assignment here... *)
End

Theorem moore_comb2_alt:
 moore_comb2 fext s s' = s' with out_seq := (s.state = 8w)
Proof
 rw [moore_comb2_def]
QED

Definition moore_comb_def:
 moore_comb = procs [moore_comb1; moore_comb2]
End

Theorem moore_comb_const:
 (moore_comb fext s s').state = s'.state
Proof
 simp [moore_comb_def, procs_def, moore_comb2_alt, moore_comb1_alt]
QED

Definition moore_seq_def:
 moore_seq (fext:moore_ext_state) (s:moore_state) s' = s' with state := s'.next_state
End

val init_tm = add_x_inits “<| state := 1w |>”;

Definition moore_init_def:
 moore_init fbits = ^init_tm
End

Definition moore_def:
 moore = mk_module moore_seq moore_comb moore_init
End

Theorem moore_alt:
 moore = mk_module_extra moore_seq moore_comb moore_init
Proof
 simp [moore_def] \\ dep_rewrite.DEP_REWRITE_TAC [mk_module_mk_module_extra] \\
 simp [moore_comb_def, procs_def, moore_comb1_alt, moore_comb2_alt]
QED

Definition in_seq_previously_def:
 in_seq_previously fext n shift = if n < shift then F else (fext (n - shift)).in_seq
End

Theorem in_seq_previously_SUC:
 (in_seq_previously fext (SUC n) 1 = (fext n).in_seq) ∧
 (in_seq_previously fext (SUC n) 2 = in_seq_previously fext n 1) ∧
 (in_seq_previously fext (SUC n) 3 = in_seq_previously fext n 2) ∧
 (in_seq_previously fext (SUC n) 4 = in_seq_previously fext n 3)
Proof
 simp [in_seq_previously_def, arithmeticTheory.ADD1] \\ rw [EQ_IMP_THM]
QED

Definition moore_inv_def:
 moore_inv fext n s ⇔
  (* s0 *) (s.state = 1w ⇔ ~in_seq_previously fext n 2 ∧ ~in_seq_previously fext n 1) ∧
  (* s1 *) (s.state = 2w ⇔ ((~in_seq_previously fext n 3 ∧ ~in_seq_previously fext n 2) ∨
                            in_seq_previously fext n 2) ∧
                           in_seq_previously fext n 1) ∧
  (* s2 *) (s.state = 4w ⇔ in_seq_previously fext n 2 ∧ ~in_seq_previously fext n 1) ∧
  (* s3 *) (s.state = 8w ⇔ in_seq_previously fext n 3 ∧
                           ~in_seq_previously fext n 2 ∧
                           in_seq_previously fext n 1) ∧

 (s.out_seq ⇔ s.state = 8w)
End

Theorem moore_inv_moore:
 ∀fext fbits n. moore_inv fext n (moore fext fbits n)
Proof
 ntac 2 gen_tac \\ Induct >- (EVAL_TAC \\ rw [] \\ fs []) \\
 fs [moore_inv_def, moore_alt, in_seq_previously_SUC] \\
 fs [mk_module_extra_def, mk_circuit_extra_def, moore_comb_const] \\ rw [] \\
 fs [moore_seq_def, moore_comb_def, procs_def, moore_comb2_alt, moore_comb1_alt] \\
 rw [] \\ gs []
QED

(* definition of correct output, should detect 101 *)
Definition moore_spec_def:
 moore_spec fext n ⇔
  in_seq_previously fext n 3 ∧ ~(in_seq_previously fext n 2) ∧ in_seq_previously fext n 1
End

Theorem moore_correct:
 ∀fext fbits n. (moore fext fbits n).out_seq ⇔ moore_spec fext n
Proof
 rpt gen_tac \\ qspecl_then [‘fext’, ‘fbits’, ‘n’] assume_tac moore_inv_moore \\
 fs [moore_inv_def, moore_spec_def]
QED

(* Same but Mealy-style instead, from same source *)

Datatype:
 mealy_state = <| (* communication vars: *)     state : word2; in_seq_reg : bool;
                  (* non-communication vars: *) out_seq : bool; next_state : word2 |>
End

(*
parameter S0 = 2'b00, S1 = 2'b01, S2 = 2'b10;

S0 = 0
S1 = 1
S2 = 2
*)

Definition mealy_comb_def:
 mealy_comb (fext:moore_ext_state) s s' =
  case s.state of
    0w => if ~s.in_seq_reg then (s' with <| next_state := 0w; out_seq := F |>)
          else (s' with <| next_state := 1w; out_seq := F |>)
  | 1w => if ~s.in_seq_reg then (s' with <| next_state := 2w; out_seq := F |>)
          else (s' with <| next_state := 1w; out_seq := F |>)
  | 2w => if ~s.in_seq_reg then (s' with <| next_state := 0w; out_seq := F |>)
          else (s' with <| next_state := 1w; out_seq := T |>)
  | _ => s' with <| next_state := 0w; out_seq := F |> (* X assignment here would be better... *)
End

Theorem mealy_comb_const:
 (mealy_comb fext s s').state = s'.state ∧
 (mealy_comb fext s s').in_seq_reg = s'.in_seq_reg
Proof
 rw [mealy_comb_def]
QED

Definition mealy_seq1_def:
 mealy_seq1 fext (s:mealy_state) s' = s' with in_seq_reg := fext.in_seq
End

Definition mealy_seq2_def:
 mealy_seq2 (fext:moore_ext_state) (s:mealy_state) s' = s' with state := s'.next_state
End

Definition mealy_seq_def:
 mealy_seq = procs [mealy_seq1; mealy_seq2]
End

val init_tm = add_x_inits “<| state := 0w; in_seq_reg := F |>”;

Definition mealy_init_def:
 mealy_init fbits = ^init_tm
End

Definition mealy_def:
 mealy = mk_module mealy_seq mealy_comb mealy_init
End

Theorem mealy_alt:
 mealy = mk_module_extra mealy_seq mealy_comb mealy_init
Proof
 simp [mealy_def] \\ dep_rewrite.DEP_REWRITE_TAC [mk_module_mk_module_extra] \\
 rw [mealy_comb_def] \\ gs []
QED

Definition mealy_inv_def:
 mealy_inv fext n s ⇔
  (s.in_seq_reg = in_seq_previously fext n 1) ∧

  (* s0 *) (s.state = 0w ⇔ ~in_seq_previously fext n 3 ∧ ~in_seq_previously fext n 2) ∧
  (* s1 *) (s.state = 1w ⇔ in_seq_previously fext n 2) ∧
  (* s2 *) (s.state = 2w ⇔ in_seq_previously fext n 3 ∧ ~in_seq_previously fext n 2) ∧
  (* unreachable: *) (s.state ≠ 3w) ∧

  (s.out_seq ⇔ s.state = 2w ∧ in_seq_previously fext n 1)
End

Theorem mealy_inv_mealy:
 ∀fext fbits n. mealy_inv fext n (mealy fext fbits n)
Proof
 ntac 2 gen_tac \\ Induct >- EVAL_TAC \\
 fs [mealy_inv_def, in_seq_previously_SUC] \\ rpt conj_tac \\
 fs [mealy_alt, mk_module_extra_def, mk_circuit_extra_def, mealy_comb_const, mealy_seq_def, mealy_init_def] \\
 simp [procs_def, mealy_seq1_def, mealy_seq2_def] \\ simp [mealy_comb_def] \\
 rw [] \\ gs []
QED

Theorem mealy_correct:
 ∀fext fbits n. (mealy fext fbits n).out_seq ⇔ moore_spec fext n
Proof
 rpt gen_tac \\ qspecl_then [‘fext’, ‘fbits’, ‘n’] assume_tac mealy_inv_mealy \\
 fs [mealy_inv_def, moore_spec_def] \\ simp [GSYM CONJ_ASSOC]
QED

val _ = export_theory ();
