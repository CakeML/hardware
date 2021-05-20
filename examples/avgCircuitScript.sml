open hardwarePreamble;

open newTranslatorTheory newTranslatorCoreLib;

open blastLib;

val _ = new_theory "avgCircuit";

(* A simple moving average filter *)

val _ = prefer_num ();

Datatype:
 avg_state = <| h0 : word8; h1 : word8; h2 : word8; h3 : word8; avg : word8 |>
End

Datatype:
 avg_ext_state = <| signal : word8 |>
End

Definition soft_div_by_4_def:
 soft_div_by_4 s' = let
  s' = s' with avg := (0 :+ word_bit 2 s'.avg) s'.avg;
  s' = s' with avg := (1 :+ word_bit 3 s'.avg) s'.avg;
  s' = s' with avg := (2 :+ word_bit 4 s'.avg) s'.avg;
  s' = s' with avg := (3 :+ word_bit 5 s'.avg) s'.avg;
  s' = s' with avg := (4 :+ word_bit 6 s'.avg) s'.avg;
  s' = s' with avg := (5 :+ word_bit 7 s'.avg) s'.avg;
  s' = s' with avg := (6 :+ F) s'.avg;
  s' = s' with avg := (7 :+ F) s'.avg in
 s'
End

Theorem soft_div_by_4_correct:
 ∀s. soft_div_by_4 s = s with avg := s.avg // 4w
Proof
 rw [soft_div_by_4_def, theorem"avg_state_component_equality"] \\ BBLAST_TAC
QED

Definition avg_comb_def:
 avg_comb (fext:avg_ext_state) (s:avg_state) (s':avg_state) = let
  s' = s' with avg := s.h0 + s.h1 + s.h2 + s.h3 in
  soft_div_by_4 s'
End

Theorem avg_comb_trans = REWRITE_RULE [soft_div_by_4_def] avg_comb_def;

Theorem avg_comb_alt:
 avg_comb fext s s' = let 
  s' = s' with avg := s.h0 + s.h1 + s.h2 + s.h3 in
  s' with avg := s'.avg // 4w
Proof
 rw [avg_comb_def, soft_div_by_4_correct]
QED

Theorem avg_comb_const:
 (avg_comb fext s s').h0 = s'.h0 ∧
 (avg_comb fext s s').h1 = s'.h1 ∧
 (avg_comb fext s s').h2 = s'.h2 ∧
 (avg_comb fext s s').h3 = s'.h3
Proof
 simp [avg_comb_alt]
QED

Definition avg_ff_def:
 avg_ff (fext:avg_ext_state) (s:avg_state) (s':avg_state) = let
  s' = s' with h0 := fext.signal;
  s' = s' with h1 := s.h0;
  s' = s' with h2 := s.h1 in
  s' with h3 := s.h2
End

val init_tm = add_x_inits “<| h0 := 0w; h1 := 0w; h2 := 0w; h3 := 0w |>”;

Definition avg_init_def:
 avg_init fbits = ^init_tm
End

Definition avg_def:
 avg = mk_module (procs [avg_ff]) (procs [avg_comb]) avg_init
End

Theorem avg_alt:
 avg = mk_module avg_ff avg_comb avg_init
Proof
 simp [avg_def, procs_sing]
QED

Definition signal_previously_def:
 signal_previously fext n shift = if n < shift then 0w else (fext (n - shift)).signal
End

Definition avg_spec_def:
 avg_spec fext n =
  ((signal_previously fext n 1) +
   (signal_previously fext n 2) +
   (signal_previously fext n 3) +
   (signal_previously fext n 4)) // 4w
End

Definition avg_inv_def:
 avg_inv fext n s ⇔
  s.h0 = signal_previously fext n 1 ∧
  s.h1 = signal_previously fext n 2 ∧
  s.h2 = signal_previously fext n 3 ∧
  s.h3 = signal_previously fext n 4 ∧
  s.avg = avg_spec fext n
End

Theorem avg_inv_avg:
 ∀fext fbits n. avg_inv fext n (avg fext fbits n)
Proof
 ntac 2 gen_tac \\ Induct >- EVAL_TAC \\
 fs [avg_inv_def, avg_spec_def, avg_alt, mk_module_def, mk_circuit_def, avg_comb_const] \\
 ntac 4 (conj_asm1_tac >-
         (rw [avg_ff_def, signal_previously_def, arithmeticTheory.ADD1] \\ fs [])) \\
 simp [avg_comb_alt]
QED

Theorem avg_correct:
 ∀fext fbits n. (avg fext fbits n).avg = avg_spec fext n
Proof
 metis_tac [avg_inv_avg, avg_inv_def]
QED

val _ = export_theory ();
