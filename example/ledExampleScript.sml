open hardwarePreamble;

val _ = new_theory "ledExample";

val _ = Datatype `state = <| count : word8 |>`;
(* No model of the external world needed in this example: *)
val _ = Datatype `ext_state = <| dummy : bool |>`;

val blink_led_def = Define `
 blink_led (s:state) = s with count := s.count + 1w`;

val circuit_def = Define `
 (circuit init 0 = init) /\
 (circuit init (SUC n) = let s' = circuit init n in <| count := (blink_led s').count |>)`;

(* Just to have a (correctness) property to lift: Prove that we eventually reach 42 *)
Theorem circuit_count:
 !n init. (circuit init n).count = init.count + n2w n
Proof
 Induct \\ rw [circuit_def, blink_led_def, n2w_SUC]
QED

Theorem circuit_correct:
 !init. ?n. 42w <=+ (circuit init n).count
Proof
 rpt gen_tac \\ simp [circuit_count] \\ Cases_on `init.count <=+ 42w`
 >- (qexists_tac `42` \\ wordsLib.WORD_DECIDE_TAC)
 \\ qexists_tac `0` \\ wordsLib.WORD_DECIDE_TAC
QED

val _ = export_theory ();
