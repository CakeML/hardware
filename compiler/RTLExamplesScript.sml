open hardwarePreamble;

open verilogTypeTheory RTLTheory;

val _ = new_theory "RTLExamples";

(*Definition prg_def:
 prg = Module
  [("in1", VBool_t); ("in2", VBool_t); ("inarr", VArray_t 5)]
  [(VBool_t, "a", SOME $ VBool F); (VArray_t 5, "arr", SOME $ n2VArray 5 0)]
  [BlockingAssign (Indexing "arr" 0 (Const $ n2VArray 5 2)) (SOME $ InputVar "in2")]
End

Definition add_prg_def:
 add_prg = Module
  [("in1", VArray_t 5); ("in2", VArray_t 5)]
  [(VArray_t 5, "in1inv", NONE); (VArray_t 5, "fullres", NONE); (VBool_t, "res", NONE)]
  [Seq (BlockingAssign (Indexing "fullres" 0 (Const (VArray [F])))
        (SOME $ BBOp (ArrayIndex (Var "fullres") 0 (Const (VArray [F])))
                     And
                     (ArrayIndex (Var "fullres") 0 (Const (VArray [T])))))
   (Seq (BlockingAssign (NoIndexing "fullres") (SOME $ Arith (Var "in1inv") Plus (InputVar "in2")))
        (BlockingAssign (NoIndexing "res") (SOME $ Equal T (ArrayIndex (Var "fullres") 0 (Const (VArray [T;T]))) (Const (VBool F)))))]
End*)

  (*[BlockingAssign (NoIndexing "a") (SOME $ BBOp (InputVar "in1") And (InputVar "in2"))]*)
      (*(BlockingAssign (NoIndexing "b") (SOME (BBOp (Var "in1") Or (Var "in2"))))*)
(*       (IfElse (Var "inv")
        (Seq (BlockingAssign (NoIndexing "a") (SOME (BUOp Not (Var "a"))))
         (BlockingAssign (NoIndexing "b") (SOME (BUOp Not (Var "b")))))
        Skip))*)

(*
EVAL ``compile_p1 [] [prg]``
*)

(*
val prg_assn_def = Define `
 prg_assn var b = BlockingAssign (Var var) (BBOp (Const (VBool b)) And (Const (VBool F)))`;

val prg_nassn_def = Define `
 prg_nassn var b = NonBlockingAssign (Var var) (BBOp (Const (VBool b)) And (Const (VBool F)))`;

val prg_foo_foo_def = Define `
 prg_foo_foo var = Seq (BlockingAssign (Var var) (Const (VBool T)))
                       (BlockingAssign (Var var) (Var var))`;

val prg_foo_foo_nb_def = Define `
 prg_foo_foo_nb var = Seq (NonBlockingAssign (Var var) (Const (VBool T)))
                          (NonBlockingAssign (Var var) (Var var))`;

val prg_Seq_def = Define `
 prg_Seq = Seq
         (Seq (BlockingAssign (Var "a") (Const (VBool T)))
              (BlockingAssign (Var "b") (Const (VBool F))))
         (BlockingAssign (Var "c") (BBOp (Var "a") And (Var "b")))`;

val prg_flip_def = Define `
 prg_flip = BlockingAssign (Var "flip") (BUOp Not (Var "flip"))`;

val prg_if_def = Define `
 prg_if = IfElse (Const (VBool T)) (prg_nassn "foo" T) (prg_assn "foo" F)`;
*)
(*
val prg_if_def = Define `
 prg_if = IfElse (Var "c") (NonBlockingAssign (Var "x") (Const (VBool T))) Skip`;

(*

if c
 x <= T;
else
 skip;

Expect: mux(c, T, x)

*)
val prg1_def = Define `
 prg1 = prg_if`;
(* EVAL ``compile_p1 [prg1]`` *)

(*

x = F;

if c
 x <= T;
else
 skip;

Expect: mux(c, T, F)

*)
val prg2_def = Define `
 prg2 = Seq (BlockingAssign (Var "x") (Const (VBool F))) prg_if`;
(* EVAL ``compile_p1 [prg2]`` *)

(*

x <= F;

if c
 x <= T;
else
 skip;

Expect: mux(c, T, F)

*)
val prg3_def = Define `
 prg3 = Seq (NonBlockingAssign (Var "x") (Const (VBool F))) prg_if`;
(* EVAL ``compile_p1 [prg3]`` *)

(*

x <= F;
x = T;

if c
 x <= T;
else
 skip;

Expect: mux(c, T, F)

*)
val prg4_def = Define `
 prg4 = Seq (NonBlockingAssign (Var "x") ((Const (VBool F))))
         (Seq (BlockingAssign (Var "x") ((Const (VBool T))))
          prg_if)`;
(* EVAL ``compile_p1 [prg4]`` *)

(*

if c
 x = T;
else
 x <= F;

Expect: mux(c, T, x); mux(c, T, F)

*)
val prg5_def = Define `
 prg5 = IfElse (Var "c")
         (BlockingAssign (Var "x") (Const (VBool T)))
         (NonBlockingAssign (Var "x") (Const (VBool F)))`;
(* EVAL ``compile_p1 [prg5]`` *)

(*

if c
 x <= T;
else
 x = F;

Expect: mux(c, x, F); mux(c, T, F)

*)
val prg6_def = Define `
 prg6 = IfElse (Var "c")
         (NonBlockingAssign (Var "x") (Const (VBool T)))
         (BlockingAssign (Var "x") (Const (VBool F)))`;
(* EVAL ``compile_p1 [prg6]`` *)

(*

if c
 x <= T;
else
 skip;

x = F;

Expect: mux(c, T, F)

*)
val prg7_def = Define `
 prg7 = Seq
         (IfElse (Var "c")
          (NonBlockingAssign (Var "x") (Const (VBool T)))
          Skip)
         (BlockingAssign (Var "x") (Const (VBool F)))`;
(* EVAL ``compile_p1 [prg7]`` *)

(*

if c
 x <= T;
else
 skip;

x = F & T;

Expect: mux(c, T, inp...)

*)
val prg8_def = Define `
 prg8 = Seq
         (IfElse (Var "c")
          (NonBlockingAssign (Var "x") (Const (VBool T)))
          Skip)
         (BlockingAssign (Var "x") (BBOp (Const (VBool F)) And (Const (VBool T))))`;
(* EVAL ``compile_p1 [prg8]`` *)

(*

x <= T;
x = F;

*)
val prg9_def = Define `
 prg9 = Seq
         (NonBlockingAssign (Var "x") (Const (VBool T)))
         (BlockingAssign (Var "x") (Const (VBool F)))`;
(* EVAL ``compile_p1 [prg9]`` *)

(*

x = F;
x <= T;

*)
val prg10_def = Define `
 prg10 = Seq
         (BlockingAssign (Var "x") (Const (VBool F)))
         (NonBlockingAssign (Var "x") (Const (VBool T)))`;
(* EVAL ``compile_p1 [prg10]`` *)

(*

x <= T /\ T;
x = F;

*)
val prg11_def = Define `
 prg11 = Seq
          (NonBlockingAssign (Var "x") (BBOp (Const (VBool F)) And (Const (VBool T))))
          (BlockingAssign (Var "x") (Const (VBool F)))`;
(* EVAL ``compile_p1 [prg11]`` *)

(*

if c
 x <= T;
else
 skip;

if d
 x <= F;
else
 skip;

Expect: ...

*)
val prg12_def = Define `
 prg12 = Seq
          (IfElse (Var "c")
           (NonBlockingAssign (Var "x") (Const (VBool T)))
           Skip)
          (IfElse (Var "d")
           (NonBlockingAssign (Var "x") (Const (VBool F)))
           Skip)`;
(* EVAL ``compile_p1 [prg12]`` *)
*)

val _ = export_theory ();
