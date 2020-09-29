open hardwarePreamble;

open alistTheory wordsTheory;
open dep_rewrite wordsLib;

open sumExtraTheory verilogTheory verilogTypeTheory verilogMetaTheory;
open RTLTheory RTLTypeTheory RTLPropsTheory;

open RTLLib;

val _ = new_theory "RTLOptimizer";
(*
val cell_not_inp_def = Define `
 (cell_not_inp (Cell1 CNot _ inp) = SOME inp) /\
 (cell_not_inp _ = NONE)`;

val mux_not_cond_opt_def = Define `
 (mux_not_cond_opt above (CellMux out cond tin fin) =
  case cell_input_num cond of
    NONE => NONE
  | SOME n =>
    case get_cell above n of
      NONE => NONE
    | SOME ccond =>
      case cell_not_inp ccond of
        NONE => NONE
      | SOME ccond_inp => SOME (CellMux out ccond_inp fin tin)) /\
 (mux_not_cond_opt above _ = NONE)`

val THE_default_def = Define `
 (THE_default (SOME x) d = x) /\
 (THE_default NONE d = d)`;

val muxes_not_cond_opt_def = Define `
 (muxes_not_cond_opt above [] = []) /\
 (muxes_not_cond_opt above (c::cs) =
  (THE_default (mux_not_cond_opt above c) c) :: muxes_not_cond_opt (c::above) cs)`;

(*
cell_run env h = INR fx ==>
cell_run env (THE_default (mux_not_cond_opt [] h) h) = INR fx

Theorem muxes_not_cond_opt_correct_lem:
 !cells env env'.
 sum_foldM cell_run env cells = INR env' ==>
 sum_foldM cell_run env (muxes_not_cond_opt [] cells) = INR env'
Proof
 Induct \\ rw [sum_foldM_def, muxes_not_cond_opt_def, sum_bind_INR] \\
 Cases_on `h` \\ simp [mux_not_cond_opt_def, THE_default_def]
QED

Theorem muxes_not_cond_opt_correct:
 !n cenv cenv' cells regs.
 netlist_run cenv cells regs n = INR cenv' ==>
 netlist_run cenv (muxes_not_cond_opt [] cells) regs n = INR cenv'
Proof
 Induct \\ rw [netlist_run_def, sum_bind_INR] \\
 drule_first \\ asm_exists_tac \\

 fs [netlist_step_def, sum_bind_INR]
QED
*)
*)
val _ = export_theory ();
