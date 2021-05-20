open hardwarePreamble;

open verilogTheory verilogTypeTheory;

open compileLib RTLPrintLib;

val _ = new_theory "loop";

Definition const8_def:
 const8 n = Const $ n2VArray 8 n (* <-- OLD NOTE: currently 32 here instead of 8 *)
End

Definition controll_state_update_def:
 controll_state_update old new =
  (const8 old, NonBlockingAssign (NoIndexing "state") (SOME $ const8 new))
End

Definition loop_process_controll_def:
 loop_process_controll =
  IfElse (Cmp (InputVar "reg_8") ArrayEqual (Const $ n2VArray 1 1))
         (NonBlockingAssign (NoIndexing "state") (SOME $ const8 11))
         (Case VBool_t (Var "state") 
          [controll_state_update 8 7;
           controll_state_update 4 7;
           controll_state_update 2 1;
           controll_state_update 10 9;
           controll_state_update 6 5;
           controll_state_update 1 1;
           controll_state_update 9 8;
           controll_state_update 5 4;
           controll_state_update 3 1;
           controll_state_update 11 10;
           (const8 7,
            IfElse (Cmp (Var "reg_1") ArrayEqual (Var "reg_3"))
                   (NonBlockingAssign (NoIndexing "state") (SOME $ const8 3))
                   (NonBlockingAssign (NoIndexing "state") (SOME $ const8 6)))]
          NONE)
End

Definition loop_process_state_def:
 loop_process_state =
  Case VBool_t (Var "state")
       [(*(const8 8, Skip);*)
        (*(const8 4, Skip);*)
        (const8 2, NonBlockingAssign (NoIndexing "reg_4") (SOME $ const8 0));
        (const8 10, NonBlockingAssign (NoIndexing "reg_2") (SOME $ const8 0));
        (const8 6, NonBlockingAssign (NoIndexing "reg_2")
                                      (SOME $ Arith (Var "reg_2")
                                                    Plus
                                                    (Arith (Var "reg_1") Plus (const8 0))));
        (const8 1, Seq (NonBlockingAssign (NoIndexing "finish") (SOME $ Const $ n2VArray 1 1))
                        (NonBlockingAssign (NoIndexing "ret") (SOME $ Var "reg_4")));
        (const8 9, NonBlockingAssign (NoIndexing "reg_1") (SOME $ const8 0));
        (const8 5, NonBlockingAssign (NoIndexing "reg_1")
                                      (SOME $ Arith (Var "reg_1") Plus (const8 1)));
        (const8 3, NonBlockingAssign (NoIndexing "reg_4")
                                      (SOME $ Arith (Var "reg_2") Plus (const8 2)));
        (const8 11, NonBlockingAssign (NoIndexing "reg_3")
                                       (SOME $ const8 5))
        (*(const8 7, Skip)*)]
       NONE
End

Definition loop_module_def:
 loop_module =
 <| fextty := [("reg_7", VArray_t 1); ("reg_8", VArray_t 1)];
    decls := [("finish", <| output := T; type := VArray_t 1; init := NONE |>);
              ("ret", <| output := T; type := VArray_t 8; init := NONE |>)] ++
             MAP (λreg. (reg, <| output := F; type := VArray_t 8; init := NONE |>))
                 ["reg_4"; "reg_2"; "state"; "reg_1"; "reg_3"];
    ffs := [loop_process_controll; loop_process_state];
    combs := [] |>
End

val (circuit, circuit_correct) = compile loop_module_def;

Theorem loop_circuit_correct = circuit_correct;

(* print_Circuit (circuit |> concl |> rhs) |> print *)

val _ = export_theory ();
