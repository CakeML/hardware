open hardwarePreamble;

val _ = new_theory "avgExample";

(* Moving avg filter with history size = 2^2 = 4 *)

Datatype:
 state = <| h0 : word8; h1 : word8; h2 : word8; h3 : word8; sum : word8; avg : word8 |>
End

Datatype:
 ext_state = <| signal : word8; enabled : bool |>
End

Definition soft_div_by_4_def:
 soft_div_by_4 s = let
  s = s with sum := (0 :+ word_bit 2 s.sum) s.sum;
  s = s with sum := (1 :+ word_bit 3 s.sum) s.sum;
  s = s with sum := (2 :+ word_bit 4 s.sum) s.sum;
  s = s with sum := (3 :+ word_bit 5 s.sum) s.sum;
  s = s with sum := (4 :+ word_bit 6 s.sum) s.sum;
  s = s with sum := (5 :+ word_bit 7 s.sum) s.sum;
  s = s with sum := (6 :+ F) s.sum;
  s = s with sum := (7 :+ F) s.sum in
 s
End

Theorem soft_div_by_4_correct:
 ∀s. soft_div_by_4 s = s with sum := s.sum // 4w
Proof
 rw [soft_div_by_4_def, theorem"state_component_equality"] \\ blastLib.BBLAST_TAC
QED

Definition avg_step_def:
 avg_step (fext:ext_state) (s:state) =
  let s = s with h3 := s.h2;
      s = s with h2 := s.h1;
      s = s with h1 := s.h0;
      s = s with h0 := fext.signal;
      s = s with sum := s.h0 + s.h1 + s.h2 + s.h3;
      s = soft_div_by_4 s in
   if fext.enabled then (s with avg := s.sum) else (s with avg := fext.signal)
End

(* avg_step_def |> REWRITE_RULE [soft_div_by_4_def] *)

Definition avg_def:
 (avg fext s 0 = s) /\
 (avg fext s (SUC n) = avg_step (fext n) (avg fext s n))
End

Definition signal_previously_def:
 signal_previously fext (n:num) shift = if n < shift then 0w else (fext (n - shift)).signal
End

Definition avg_signal_def:
 avg_signal fext n =
  ((signal_previously fext n 1) +
   (signal_previously fext n 2) +
   (signal_previously fext n 3) +
   (signal_previously fext n 4)) // 4w
End

Definition avg_spec_def:
 avg_spec fext n =
  if n = 0 then
   0w
  else if (fext (n - 1)).enabled then
   avg_signal fext n
  else
   (fext (n - 1)).signal
End

Definition avg_inv_def:
 avg_inv fext n s ⇔
  s.h0 = signal_previously fext n 1 ∧
  s.h1 = signal_previously fext n 2 ∧
  s.h2 = signal_previously fext n 3 ∧
  s.h3 = signal_previously fext n 4 ∧
  s.sum = avg_signal fext n ∧
  s.avg = avg_spec fext n
End

Theorem avg_inv_avg:
 ∀n fext s.
 avg_inv fext n s ⇒ avg_inv fext (SUC n) (avg_step (fext n) s)
Proof
 rw [avg_inv_def, avg_spec_def, avg_signal_def, avg_step_def, soft_div_by_4_correct] \\
 rw [signal_previously_def, arithmeticTheory.ADD1] \\ fs []
QED

Definition avg_init_def:
 avg_init = <| h0 := 0w; h1 := 0w; h2 := 0w; h3 := 0w; sum := 0w; avg := 0w |>
End

Theorem avg_inv_avg:
 ∀n fext.
 avg_inv fext n (avg fext avg_init n)
Proof
 Induct >- (gen_tac \\ EVAL_TAC) \\ rw [avg_def, avg_inv_avg]
QED

Theorem avg_correct:
 ∀n fext.
 (avg fext avg_init n).avg = avg_spec fext n
Proof
 metis_tac [avg_inv_avg, avg_inv_def]
QED

val _ = export_theory ();
