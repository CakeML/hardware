open hardwarePreamble;

open RTLTheory RTLTypeTheory;

val _ = new_theory "RTLDeterminizer";

Datatype:
 dfill = TBD rtltype (* to be determined *)
       | HBD value (* has been determined *)
End

(** Pass 1: Find out what to fill with **)

Definition cell_input_tbd_def:
 (cell_input_tbd si (VarInp (NetVar n) idx) ⇔
  case lookup num_cmp n si of
   SOME (TBD t) => SOME (t, n)
  | _ => NONE) ∧
 (cell_input_tbd si _ ⇔ NONE)
End

(* Will never fail on well-typed netlists... with more proofs one could remove the runtime checks... *)
Definition find_fills_def:
 (find_fills si [] = INR si) ∧
 (find_fills si (c::cs) =
  let si' = (case c of
    NDetCell out t => INR $ insert num_cmp out (TBD t) si
  | CellMux out cin tin fin => (case (cell_input_tbd si tin, cell_input_tbd si fin) of
      (NONE, SOME (fin_t, fin_n)) =>
       (case tin of
          ConstInp v => if has_rtltype_v v fin_t then INR (insert num_cmp fin_n (HBD v) si) else INL TypeError
        | _ => INR si)
    | (SOME (tin_t, tin_n), NONE) =>
       (case fin of
          ConstInp v => if has_rtltype_v v tin_t then INR (insert num_cmp tin_n (HBD v) si) else INL TypeError
        | _ => INR si)
    | _ => INR si)
  (* Could bind for more, e.g. addition and multiplication, but muxes enough for now... *)
  | _ => INR si) in
  sum_bind si' (\si. find_fills si cs))
End

(** Pass 2: Do filling **)

Definition build_zero_def:
 (build_zero CBool_t = CBool F) /\
 (build_zero (CArray_t l) = CArray $ GENLIST (K F) l)
End

Definition build_zero_with_idx_def:
 (build_zero_with_idx CBool_t idx = ConstInp $ CBool F) /\
 (build_zero_with_idx (CArray_t l) NoIndexing = ConstInp $ CArray $ GENLIST (K F) l) /\
 (build_zero_with_idx (CArray_t l) (Indexing idx) = ConstInp $ CBool F) ∧
 (build_zero_with_idx (CArray_t l) (SliceIndexing i1 i2) = ConstInp $ CArray $ GENLIST (K F) (i1 - i2 + 1))
End

Definition build_const_def:
 (build_const (CBool b) idx = ConstInp $ CBool b) /\
 (build_const (CArray bs) NoIndexing = ConstInp $ CArray bs) /\
 (build_const (CArray bs) (Indexing idx) = ConstInp $ CBool $ revEL idx bs) ∧
 (build_const (CArray bs) (SliceIndexing i1 i2) = ConstInp $ CArray $ rev_slice bs i1 i2)
End

Definition rtl_determinizer_inp_def:
 (rtl_determinizer_inp si (VarInp (NetVar n) idx) =
  case lookup num_cmp n si of
    NONE => VarInp (NetVar n) idx
  | SOME (TBD t) => build_zero_with_idx t idx
  | SOME (HBD v) => build_const v idx) /\
 (rtl_determinizer_inp si inp = inp)
End

Definition rtl_determinizer_cell_def:
 (rtl_determinizer_cell si (NDetCell out t) = (si, NONE)) /\
 (rtl_determinizer_cell si (Cell1 cell1 out in1) =
  (si, SOME $ Cell1 cell1 out (rtl_determinizer_inp si in1))) /\
 (rtl_determinizer_cell si (Cell2 cell2 out in1 in2) =
  (si, SOME $ Cell2 cell2 out (rtl_determinizer_inp si in1) (rtl_determinizer_inp si in2))) /\
 (rtl_determinizer_cell si (CellMux out cin tin fin) =
  let tin' = rtl_determinizer_inp si tin;
      fin' = rtl_determinizer_inp si fin in
  case (tin', fin') of
   (ConstInp tv, ConstInp fv) =>
    if tv = fv then
     (insert num_cmp out (HBD tv) si, NONE)
    else
     (si, SOME $ CellMux out (rtl_determinizer_inp si cin) tin' fin')
   | _ => (si, SOME $ CellMux out (rtl_determinizer_inp si cin) tin' fin')) /\
 (rtl_determinizer_cell si (CellArrayWrite out in1 idx in2) =
  (si, SOME $ CellArrayWrite out (rtl_determinizer_inp si in1) idx (rtl_determinizer_inp si in2))) /\
 (rtl_determinizer_cell si cell = (si, SOME cell))
End

Definition rtl_determinizer_netlist_def:
 (rtl_determinizer_netlist si [] = (si, [])) /\
 (rtl_determinizer_netlist si (c::cs) =
  let (si, c) = rtl_determinizer_cell si c;
      (si, cs) = rtl_determinizer_netlist si cs in
   (si, case c of SOME c => c :: cs | NONE => cs))
End

(*
Actually, only regs in outs so no need to do anything:

Definition rtl_determinizer_out_def:
 (rtl_determinizer_out si (out, OutInp inp) = (out, OutInp $ rtl_determinizer_inp si inp)) ∧
 (rtl_determinizer_out si (out, OutInps inps) = (out, OutInps $ MAP (rtl_determinizer_inp si) inps))
End
*)

Definition rtl_determinizer_reg_def:
 rtl_determinizer_reg si ((reg, i), rdata) =
  ((reg, i),
   rdata with <| init := (SOME $ case rdata.init of SOME v => v | NONE => build_zero rdata.type);
                 inp := OPTION_MAP (rtl_determinizer_inp si) rdata.inp |>)
End

Definition rtl_determinizer_def:
 rtl_determinizer (Circuit extenv outs regs combs_nl ffs_nl) = do
  (* can do this without concatenation, but this would require proof refactorings: *)
  si <- find_fills empty (combs_nl ++ ffs_nl);
  (si, combs_nl_det) <<- rtl_determinizer_netlist si combs_nl;
  (si, ffs_nl_det) <<- rtl_determinizer_netlist si ffs_nl;
  (* TODO: Does not change key-field so could write this in a better way: *)
  regs_det <<- MAP (rtl_determinizer_reg si) regs;
  return $ Circuit extenv outs regs_det combs_nl_det ffs_nl_det
 od
End

val _ = export_theory ();
