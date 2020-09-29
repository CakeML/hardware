open hardwarePreamble;

open verilogTheory verilogTypeTheory;

open fullCompilerTheory TechMapLib BetterLECLib RTLPrintLib;

val _ = new_theory "loop";

Definition const8_def:
 const8 n = Const $ n2VArray 32 n (* <-- NOTE: currently 32 here instead of 8 *)
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
 loop_module = Module
  [("reg_7", VArray_t 1); ("reg_8", VArray_t 1)]
  ([(VArray_t 1, "finish", NONE); (VArray_t 32, "ret", NONE)] ++
   MAP (λreg. (VArray_t 32, reg, NONE)) ["reg_4"; "reg_2"; "state"; "reg_1"; "reg_3"])
  [loop_process_controll; loop_process_state]
End

(*EVAL “typecheck loop_module”*)

(* val c = Timer.startRealTimer (); *)
val compile_result = EVAL “compile ["finish"; "ret"] loop_module”;
(* val () = c |> Timer.checkRealTimer |> Time.toString |> print; *)
val circuit = compile_result |> concl |> rhs |> sumSyntax.dest_inr |> fst;
val newnl = tech_map circuit;

val (extenv, regs, nl) = dest_Circuit circuit;

Definition loop_extenv_def:
 loop_extenv = ^extenv
End

Definition loop_regs_def:
 loop_regs = ^regs
End

Definition nl_hi_def:
 nl_hi = ^nl
End

Definition nl_low_def:
 nl_low = ^newnl
End

Definition loop_circuit_def:
 loop_circuit = Circuit loop_extenv loop_regs nl_low
End

(* val th = betterlec loop_extenv_def loop_regs_def nl_hi_def nl_low_def; *)

(*

loop_circuit_def |> REWRITE_RULE [loop_extenv_def, loop_regs_def, nl_low_def] |> concl |> rhs
                 |> print_Circuit |> writeFile "loop_luts.sv";

unblast_regs "ret" 32;
unblast_regs "state" 32;

 output logic[7:0] state,
 output finish,
 output logic[7:0] ret

assign state = {state0, state1, state2, state3, state4, state5, state6, state7};
assign finish = finish0;
assign ret = {ret0, ret1, ret2, ret3, ret4, ret5, ret6, ret7};

*)

val _ = export_theory ();
