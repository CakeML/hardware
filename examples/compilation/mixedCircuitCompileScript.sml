open hardwarePreamble;

open mixedCircuitTheory;

open translatorLib compileLib RTLPrintLib;

val _ = new_theory "mixedCircuitCompile";

(** HOL -> Verilog **)

val trans_thm = module2hardware mixed_def ["var3","var_comb"] ["var1", "var3"];

(** Verilog -> netlist **)

val (circuit, circuit_correct) = compile (definition "mixed_v_def");

(*
print_Circuit (circuit |> concl |> rhs) |> print
*)

val _ = export_theory ();
