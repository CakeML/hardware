open hardwarePreamble;

open pulseCounterCircuitTheory;

open newTranslatorLib compileLib;

val _ = new_theory "pulseCounterCircuitCompile";

(** to Verilog **)

val trans_thm = module2hardware pcounter_def ["done"] ["count"];

(** to netlist **)

(* val _ = compile (definition"pcounter_v") *)

(* pcounter_correct *)

val _ = export_theory ();
