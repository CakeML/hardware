(* Verilog testcases (TCs) *)

open preamble;

open verilogTheory;

open bitstringLib;

val _ = new_theory "verilogTCs";

Q.prove(
 `erun <| vars := [("foo", VBool T)] |> (ArrayIndex "foo" [Const (n2ver 5)]) = INL TypeError`,
 EVAL_TAC);

(* bl = build *)
val bl_varray_def = Define `
 bl_varray xs = VArray (MAP n2ver xs)`;

val bl_earray_def = Define `
 bl_earray xs = MAP (Const o n2ver) xs`;

Q.prove(
 `erun <| vars := [("foo", bl_varray [5])] |> (ArrayIndex "foo" (bl_earray [0])) = INR (n2ver 5)`,
 EVAL_TAC);

Q.prove(
 `erun <| vars := [("foo", VArray [bl_varray [5; 50];
                                   bl_varray [0; 1]])] |> (ArrayIndex "foo" (bl_earray [1; 1])) =
                  INR (n2ver 5)`,
 EVAL_TAC);

Q.prove(
 `erun <| vars := [("foo", VArray [bl_varray [5; 50];
                                   bl_varray [0; 1]])] |> (ArrayIndex "foo" (bl_earray [0; 0])) =
                  INR (n2ver 1)`,
 EVAL_TAC);

val _ = export_theory ();
