open hardwarePreamble;

open RTLTheory;

val _ = new_theory "RTLStats";

Datatype:
 stats = <| num_cell1 : num; num_cell2 : num; num_mux : num; num_luts : num list; num_carry4 : num |>
End

Definition inc_lut_counter_def:
 (inc_lut_counter idx [] = INL NotImplemented) ∧ (* should never happen *)
 (inc_lut_counter 0 (n::ns) = INR (n + 1 :: ns)) ∧
 (inc_lut_counter (SUC idx) (n::ns) = do
  ns <- inc_lut_counter idx ns;
  return (n :: ns)
 od)
End

Definition cell_stats_def:
 cell_stats s cell = case cell of
   Cell1 _ _ _ => INR $ s with num_cell1 := s.num_cell1 + 1
 | Cell2 _ _ _ _ => INR $ s with num_cell2 := s.num_cell2 + 1
 | CellMux _ _ _ _ => INR $ s with num_mux := s.num_mux + 1
 | CellLUT _ inps _ => let len = LENGTH inps in
                        if len ≠ 0 ∧ len ≤ 6 then do
                         num_luts <- inc_lut_counter (len - 1) s.num_luts;
                         return (s with num_luts := num_luts)
                        od else
                         INL NotImplemented
 | Carry4 _ _ _ _ _ => INR $ s with num_carry4 := s.num_carry4 + 1
 |  _ => INL NotImplemented
End

Definition netlist_stats_def:
 netlist_stats nl =
 sum_foldM cell_stats <| num_cell1 := 0; num_cell2 := 0; num_mux := 0; num_luts := REPLICATE 6 0; num_carry4 := 0|> nl
End

(*
EVAL “netlist_stats nl_hi”;
EVAL “netlist_stats nl_low”;

open loopTheory;
open RTLSyntax;

val (_, regs, _) = loop_circuit_def |> concl |> rhs |> dest_Circuit

EVAL “LENGTH ^regs”

*)

val _ = export_theory ();
