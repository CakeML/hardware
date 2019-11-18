open hardwarePreamble;

val _ = new_theory "circuitExample";

prefer_num ();

val _ = Datatype `state = <| a3 : word3; b3 : word3; c3 : word3; r3 : word3;
                             a5 : word5; b5 : word5; c5 : word5; r5 : word5;
                             r1 : bool |>`;
val _ = Datatype `ext_state = <| pulse : bool |>`;

(*
val ex1_def = Define `
 A s =
  if fext.pulse then
   s with count := s.count + 1w
  else
   s`;
*)

(* add with 2 *)

val ex1_def = Define `
 ex1 s = s with r3 := s.a3 + s.b3`;

(* w2w *)

val ex2_def = Define `
 ex2 s = s with r5 := w2w (s.a3 + s.b3)`;

val ex3_def = Define `
 ex3 s = s with r5 := w2w s.a3 + w2w s.b3`;

val ex4_def = Define `
 ex4 s = s with r5 := w2w s.a3 + s.b5`;

(* sw2sw *)

val ex5_def = Define `
 ex5 s = s with r5 := sw2sw (s.a3 + s.b3)`;

val ex6_def = Define `
 ex6 s = s with r5 := sw2sw s.a3 + sw2sw s.b3`;

val ex7_def = Define `
 ex7 s = s with r5 := sw2sw s.a3 + s.b5`;

(* add with 3 *)

val ex8_def = Define `
 ex8 s = s with r3 := s.a3 + s.b3 + s.c3`;

val ex9_def = Define `
 ex9 s = s with r5 := w2w (s.a3 + s.b3 + s.c3)`;

val ex10_def = Define `
 ex10 s = s with r5 := w2w (s.a3 + s.b3) + w2w s.c3`;

(* minus *)

val ex11_def = Define `
 ex11 s = s with r3 := s.a3 - s.b3`;

val ex12_def = Define `
 ex12 s = s with r5 := w2w (s.a3 - s.b3)`;

val ex13_def = Define `
 ex13 s = s with r5 := sw2sw (s.a3 - s.b3)`;

(* constants *)

val ex14_def = Define `
 ex14 s = s with r5 := w2w (s.a3 + (3w + s.c3) + s.b3 + 4w)`;

(* logical operators *)

val ex15_def = Define `
 ex15 s = s with r5 := word_and s.a5 (w2w s.b3)`;

val ex16_def = Define `
 ex16 s = s with r1 := (s.a5 = w2w s.b3)`;

val ex17_def = Define `
 ex17 s = s with r1 := (s.a5 <> w2w s.b3)`;

(* shift operators *)

val ex18_def = Define `
 ex18 s = s with r5 := s.a5 >>>~ w2w s.b3`;

val ex19_def = Define `
 ex19 s = s with r5 := w2w (s.a3 >>>~ w2w s.b3)`;

val ex20_def = Define `
 ex20 s = s with r5 := s.a5 >>~ w2w s.b3`;

val ex21_def = Define `
 ex21 s = s with r5 := w2w (s.a3 >>~ w2w s.b3)`;

val ex22_def = Define `
 ex22 s = s with r5 := sw2sw (s.a3 >>~ w2w s.b3) + s.c5`;

val _ = export_theory ();
