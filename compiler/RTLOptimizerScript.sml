open hardwarePreamble;

open alistTheory wordsTheory;
open dep_rewrite wordsLib;

open sumExtraTheory verilogTheory verilogTypeTheory verilogMetaTheory;
open RTLTheory RTLTypeTheory RTLPropsTheory;

open comparisonTheory balanced_mapTheory;

(*open RTLLib;*)

val _ = new_theory "RTLOptimizer";

Datatype:
 opt_inp = OptConst bool
         | OptNet num
End

val _ = type_abbrev_pp ("optm_t", ``:(num, cell_input) balanced_map``);

(*Definition var_cmp_def:
 (var_cmp (RegVar reg1 n1) (RegVar reg2 n2) =
  let scmp = string_cmp reg1 reg2 in
   if scmp = Equal then
    num_cmp n1 n2
   else
    scmp) /\
 (var_cmp (RegVar _ _) (NetVar _) = Less) /\
 (var_cmp (NetVar n1) (NetVar n2) = num_cmp n1 n2) /\
 (var_cmp (NetVar _) (RegVar _ _) = Greater)
End

Theorem var_cmp_good:
 good_cmp var_cmp
Proof
 rewrite_tac [good_cmp_def] \\ rpt conj_tac \\ rpt Cases \\
 rw [var_cmp_def] \\ metis_tac [good_cmp_def, string_cmp_good, num_cmp_good, string_cmp_antisym]
QED

Theorem var_cmp_antisym:
 !x y. var_cmp x y = Equal <=> x = y
Proof
 Cases \\ Cases \\ rw [var_cmp_def]
QED*)

Definition gol_cell_def:
 (gol_cell (Cell1 _ _ _) = T) ∧
 (gol_cell (Cell2 t _ _ _) =
  case t of
  | CAnd => T
  | COr => T
  | CXOr => T
  | _ => F) ∧
 (gol_cell _ = F)
End

Definition opt_cell_input_def:
 (opt_cell_input m (VarInp (NetVar n) idx) =
  case lookup num_cmp n m of
    NONE => VarInp (NetVar n) idx
  | SOME inp => inp) ∧
 (opt_cell_input m inp = inp)
End

Definition bool_of_cell_input_def:
 (bool_of_cell_input (ConstInp (CBool b)) = SOME b) ∧
 (bool_of_cell_input _ = NONE)
End

Definition opt_cell2_1_def:
 opt_cell2_1 m cell2 out b inp =
  case cell2 of
  | CAnd =>
    if b then
     (insert num_cmp out inp m, NONE)
    else
     (insert num_cmp out (ConstInp (CBool F)) m, NONE)
  | COr =>
    if b then
     (insert num_cmp out (ConstInp (CBool T)) m, NONE)
    else
     (insert num_cmp out inp m, NONE)
  | CXOr =>
    if b then
     (m, SOME $ Cell1 CNot out inp)
    else
     (insert num_cmp out inp m, NONE)
  | _ => (m, SOME $ Cell2 cell2 out (ConstInp (CBool b)) inp)
End

Definition opt_cell2_2_def:
 opt_cell2_2 cell2 b1 b2 =
  case cell2 of
  | CAnd => b1 ∧ b2
  | COr => b1 ∨ b2
  | CXOr => b1 ≠ b2
End

Definition opt_cell_def:
 (opt_cell m (Cell1 CNot out inp1) =
  let inp1 = opt_cell_input m inp1 in
   case bool_of_cell_input inp1 of
   | NONE => (m, SOME $ Cell1 CNot out inp1)
   | SOME b => (insert num_cmp out (ConstInp $ CBool ~b) m, NONE)) ∧
 (opt_cell m (Cell2 cell2 out inp1 inp2) =
  let inp1 = opt_cell_input m inp1;
      inp2 = opt_cell_input m inp2 in
   case (bool_of_cell_input inp1, bool_of_cell_input inp2) of
   | (NONE, NONE) => (m, SOME $ Cell2 cell2 out inp1 inp2)
   | (SOME b, NONE) => opt_cell2_1 m cell2 out b inp2
   | (NONE, SOME b) => opt_cell2_1 m cell2 out b inp1
   | (SOME b1, SOME b2) => (insert num_cmp out (ConstInp $ CBool $ opt_cell2_2 cell2 b1 b2) m, NONE)) ∧
 (opt_cell m cell = (m, SOME cell))
End

Definition opt_netlist_def:
 (opt_netlist m [] = (m, [])) /\
 (opt_netlist m (c::cs) =
  let (m', c') = opt_cell m c;
      (m'', cs') = opt_netlist m' cs in
  (m'', case c' of | NONE => cs' | SOME c' => c' :: cs'))
End

Definition opt_reg_def:
 opt_reg m (regi, data) =
  (regi, case data.inp of
         | NONE => data
         | SOME inp => data with inp := SOME $ opt_cell_input m inp)
End

Definition opt_outs_def:
 (opt_outs m (out, OutInp inp) = (out, OutInp (opt_cell_input m inp))) ∧
 (opt_outs m (out, OutInps inps) = (out, OutInps (MAP (opt_cell_input m) inps)))
End

Definition opt_circuit_def:
 opt_circuit (Circuit extenv outs regs nl_combs nl_ffs) =
  if EVERY gol_cell nl_combs ∧ ALL_DISTINCT (FLAT $ MAP cell_output nl_combs) then let (* <-- should really be established by blasting, but shortcut for now *)
   (m, nl_combs) = opt_netlist empty nl_combs in
   INR $ Circuit extenv (MAP (opt_outs m) outs) (MAP (opt_reg m) regs) nl_combs nl_ffs
  else
   INL NotImplemented
End

val _ = export_theory ();
