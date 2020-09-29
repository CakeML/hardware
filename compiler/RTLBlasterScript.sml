open hardwarePreamble;

open ASCIInumbersTheory alistTheory wordsTheory stringTheory bitstringTheory sptreeTheory;
open wordsLib;

open comparisonTheory balanced_mapTheory;

open sumExtraTheory RTLTheory;

val _ = new_theory "RTLBlaster";

val var_cmp_def = Define `
 (var_cmp (RegVar reg1 n1) (RegVar reg2 n2) =
  let scmp = string_cmp reg1 reg2 in
   if scmp = Equal then
    num_cmp n1 n2
   else
    scmp) /\
 (var_cmp (RegVar _ _) (NetVar _) = Less) /\
 (var_cmp (NetVar n1) (NetVar n2) = num_cmp n1 n2) /\
 (var_cmp (NetVar _) (RegVar _ _) = Greater)`;

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
QED

val _ = Datatype `
 inp_trans = BoolInp cell_input
           | ArrayInp (cell_input list)`;

val _ = type_abbrev_pp ("blastsi_t", ``:(var, inp_trans) balanced_map``);

val _ = Datatype `
 blasterstate =
   <| si : blastsi_t (* <-- everything that has been blasted *)
    ; extenv : (string, rtltype) alist
    ; tmpnum : num
    |>`;

val blast_cell_input_def = Define `
 (blast_cell_input s (ConstInp (CBool b)) = BoolInp $ ConstInp $ CBool b) /\
 (blast_cell_input s (ConstInp (CArray bs)) = ArrayInp $ MAP (ConstInp o CBool) bs) /\

 (blast_cell_input s (ExtInp var idx) =
  case idx of
    SOME _ => BoolInp (ExtInp var idx)
  | NONE =>
     case ALOOKUP s.extenv var of
       NONE => (* should not happen *) BoolInp (ExtInp var idx)
     | SOME CBool_t => BoolInp (ExtInp var idx)
     | SOME (CArray_t l) => ArrayInp $ GENLIST (\i. ExtInp var (SOME $ l - 1 - i)) l) /\

 (blast_cell_input s (VarInp var idx) = case lookup var_cmp var s.si of
   NONE => BoolInp (VarInp var idx)
 | SOME (BoolInp inp) => BoolInp inp (* we know that idx must be NONE here *)
 | SOME (ArrayInp inps) => case idx of
                             SOME idx => BoolInp (if idx < LENGTH inps then revEL idx inps else ConstInp (CBool F)) (* <-- if only needed for non-valid netlists *)
                           | NONE => ArrayInp inps)`;

val blaster_new_names_def = Define `
 blaster_new_names s len = (s with tmpnum := s.tmpnum + len, s.tmpnum)`;

Definition blast_cell_bitwise_def:
 (blast_cell_bitwise s (Cell1 CNot out inp) =
  case blast_cell_input s inp of
  | BoolInp inp => (s, [Cell1 CNot out inp])
  | ArrayInp inps =>
     let (s, tmpnum) = blaster_new_names s (LENGTH inps);
         outs = GENLIST (\i. VarInp (NetVar (i + tmpnum)) NONE) (LENGTH inps);
         s = s with si := insert var_cmp (NetVar out) (ArrayInp outs) s.si in
      (s, MAPi (\i inp. Cell1 CNot (tmpnum + i) inp) inps)) /\

 (blast_cell_bitwise s (Cell2 cell2 out inp1 inp2) =
  case (blast_cell_input s inp1, blast_cell_input s inp2) of
  | (BoolInp inp1, BoolInp inp2) => (s, [Cell2 cell2 out inp1 inp2])
  (*| (ArrayInp inps1, ArrayInp inps2) =>
     let (s, tmpnum) = blaster_new_names s (LENGTH inps1);
         outs = GENLIST (\i. VarInp (NetVar (i + tmpnum)) NONE) (LENGTH inps1);
         s = s with si := insert var_cmp (NetVar out) (ArrayInp outs) s.si in
      (s, MAPi (\i (inp1, inp2). Cell2 cell2 (tmpnum + i) inp1 inp2) (ZIP (inps1, inps2)))*)
  | _ => (* does not happen on well-typed netlists: *) (s, []))
End

Definition xor_lut_table_def:
 xor_lut_table = [[F; T]; [T; F]]
End

Definition blast_cell_add4_def:
 blast_cell_add4 tmpnum cin lhs rhs = let
  di = PAD_LEFT (ConstInp (CBool F)) 4 $ (*if inps1t = [] then FRONT inps1h else*) lhs;
  xor_cells = MAP2i (λi inp1 inp2. CellLUT (tmpnum + i) [inp1; inp2] xor_lut_table) lhs rhs;
  s = PAD_LEFT (ConstInp (CBool F)) 4 $ GENLIST (λi. VarInp (NetVar (tmpnum + i)) NONE) (LENGTH lhs);
  tmpnum = tmpnum + LENGTH lhs;
  cell = Carry4 tmpnum (tmpnum + 1) cin di s;
  outs = REVERSE $ GENLIST (λi. VarInp (NetVar tmpnum) (SOME i)) (LENGTH lhs) in
   (tmpnum + 2, outs, VarInp (NetVar $ tmpnum + 1) (SOME (LENGTH lhs - 1)), xor_cells ++ [cell])
End

(* Other synthesizers seem to have special cases for very short additions, where no carry chain is needed --
   such adders are compiled into LUTs directly without any carry4 involved.
   Also, the a bit in the input can be skipped in the last adder if we don't care about
   the carry output of that adder... Not sure why this is considered an optimization... *)
Definition blast_cell_add_def:
 blast_cell_add tmpnum cin inps1 inps2 =
  if inps1 = [] then (tmpnum, [], cin, []) else (* only relevant if top-level input is empty? *)
  let inps1h = REVERSE (TAKE 4 inps1);
      inps2h = REVERSE (TAKE 4 inps2);
      inps1t = DROP 4 inps1;
      inps2t = DROP 4 inps2;
      (tmpnum, outs4, cout, cells4) = blast_cell_add4 tmpnum cin inps1h inps2h in
  if inps1t = [] then
   (tmpnum, outs4, cout, cells4)
  else
   let (tmpnum, cells_outs, cout, cells) = blast_cell_add tmpnum cout inps1t inps2t in
   (tmpnum, cells_outs ++ outs4, cout, cells4 ++ cells)
Termination
 WF_REL_TAC `measure (LENGTH o (λ(_, _, inps1, _). inps1))` \\ rw [] \\ Cases_on ‘inps1’ \\ fs []
End

Definition take_drop_def:
 (take_drop n [] = ([], [])) ∧
 (take_drop n (x::xs) =
  if n = 0 then
   ([], x::xs)
  else
   let (take, drop) = take_drop (n - 1) xs in (x :: take, drop))
End

Theorem take_drop_TAKE_DROP:
 ∀l n. take_drop n l = (TAKE n l, DROP n l)
Proof
 Induct \\ rw [take_drop_def]
QED

Definition flat_zip_def:
 (flat_zip [] ys = []) ∧
 (flat_zip xs [] = []) ∧
 (flat_zip (x::xs) (y::ys) = [x;y] ++ flat_zip xs ys)
End

Definition blast_cell_equal_lut_def:
 blast_cell_equal_lut out lhs rhs =
  case lhs of
  | [lhs0] =>
    CellLUT out (flat_zip lhs rhs) [[F;F]; [T;T]]
  | [lhs0; lhs1] =>
    CellLUT out (flat_zip lhs rhs) [[F;F;F;F]; [F;F;T;T]; [T;T;F;F]; [T;T;T;T]]
  | [lhs0; lhs1; lhs2] =>
    CellLUT out (flat_zip lhs rhs) [[F;F;F;F;F;F]; [F;F;F;F;T;T]; [F;F;T;T;F;F]; [F;F;T;T;T;T]; [T;T;F;F;F;F]; [T;T;F;F;T;T]; [T;T;T;T;F;F]; [T;T;T;T;T;T]]
End

(* Doing this recursion a lot... could have a MAP for chunks... *)
Definition blast_cell_equal_luts_def:
 blast_cell_equal_luts tmpnum lhs rhs =
  let (lhsh, lhst) = take_drop 3 lhs;
      (rhsh, rhst) = take_drop 3 rhs;
      cell3 = blast_cell_equal_lut tmpnum lhsh rhsh in
   if lhst = [] then
    (SUC tmpnum, [cell3], [VarInp (NetVar tmpnum) NONE])
   else
    let (tmpnum', cells, outs) = blast_cell_equal_luts (SUC tmpnum) lhst rhst in
     (tmpnum', cell3 :: cells, VarInp (NetVar tmpnum) NONE :: outs)
Termination
 WF_REL_TAC `measure (LENGTH o (λ(_, lhs, _). lhs))` \\ rw [take_drop_TAKE_DROP] \\
 Cases_on ‘lhs’ \\ fs []
End

Definition blast_cell_equal12_def:
 blast_cell_equal12 tmpnum preveq lhs rhs =
  let (tmpnum, cells, outs) = blast_cell_equal_luts tmpnum lhs rhs in
   if LENGTH cells = 1 ∧ preveq = ConstInp (CBool T) then
    (tmpnum, cells, HD outs)
   else
    let carrycell = Carry4 tmpnum (SUC tmpnum) preveq (REPLICATE 4 (ConstInp (CBool F)))
                                                      (PAD_LEFT (ConstInp (CBool F)) 4 outs) in
    (tmpnum + 2, SNOC carrycell cells, VarInp (NetVar (SUC tmpnum)) (SOME (LENGTH outs - 1)))
End

Definition blast_cell_equalarray_def:
 blast_cell_equalarray tmpnum preveq lhs rhs =
  if lhs = [] then (tmpnum, [], preveq) else
  let (lhsh, lhst) = take_drop 12 lhs;
      (rhsh, rhst) = take_drop 12 rhs;
      (tmpnum, cells12, out) = blast_cell_equal12 tmpnum preveq lhsh rhsh in
  if lhst = [] then
   (tmpnum, cells12, out)
  else
   let (tmpnum, cells, out) = blast_cell_equalarray tmpnum out lhst rhst in
    (tmpnum, cells12 ++ cells, out)
Termination
 WF_REL_TAC `measure (LENGTH o (λ(_, _, lhs, _). lhs))` \\ rw [take_drop_TAKE_DROP] \\
 Cases_on ‘lhs’ \\ fs []
End

Definition blast_cell_equal_def:
 blast_cell_equal s out inp1 inp2 =
  case (blast_cell_input s inp1, blast_cell_input s inp2) of
    (BoolInp inp1, BoolInp inp2) =>
      (s, [Cell2 CEqual out inp1 inp2])
  | (ArrayInp inps1, ArrayInp inps2) =>
      (let (tmpnum, cells, out') = blast_cell_equalarray s.tmpnum (ConstInp (CBool T)) inps1 inps2 in (s with <| tmpnum := tmpnum; si := insert var_cmp (NetVar out) (BoolInp out') s.si |>, cells))
  | _ => (s, []) (* does not happen on well-typed netlists *)
End

val blast_cell_def = Define `
 (blast_cell s (Cell1 CNot out inp1) = blast_cell_bitwise s (Cell1 CNot out inp1)) /\

 (blast_cell s (Cell2 cell2 out inp1 inp2) = 
  case cell2 of
    CAnd => blast_cell_bitwise s (Cell2 cell2 out inp1 inp2)
  | COr => blast_cell_bitwise s (Cell2 cell2 out inp1 inp2)
  | CEqual => blast_cell_equal s out inp1 inp2
  | CAdd => (case (blast_cell_input s inp1, blast_cell_input s inp2) of
              (ArrayInp inps1, ArrayInp inps2) =>
               (let (tmpnum, outs, cout, cells) = blast_cell_add s.tmpnum (ConstInp (CBool F)) (REVERSE inps1) (REVERSE inps2) in (s with <| tmpnum := tmpnum; si := insert var_cmp (NetVar out) (ArrayInp outs) s.si |>, cells))
             | _ => (s, []) (* does not happen on well-typed netlists *))) /\

 (blast_cell s (CellMux out inp1 inp2 inp3) =
  case (blast_cell_input s inp1, blast_cell_input s inp2, blast_cell_input s inp3) of
  | (BoolInp inp1, BoolInp inp2, BoolInp inp3) => (s, [CellMux out inp1 inp2 inp3])
  | (BoolInp inp1, ArrayInp inps1, ArrayInp inps2) =>
     let (s, tmpnum) = blaster_new_names s (LENGTH inps1);
         outs = GENLIST (\i. VarInp (NetVar (i + tmpnum)) NONE) (LENGTH inps1);
         s = s with si := insert var_cmp (NetVar out) (ArrayInp outs) s.si in
      (s, MAP2i (\i inp2 inp3. CellMux (tmpnum + i) inp1 inp2 inp3) inps1 inps2)
  | _ => (* does not happen on well-typed netlists: *) (s, [])) ∧

 (blast_cell s (CellArrayWrite out inp1 idx inp2) =
  case blast_cell_input s inp1 of
   ArrayInp inps =>
    (case blast_cell_input s inp2 of
       BoolInp inp2 =>
        (s with si := insert var_cmp (NetVar out) (ArrayInp (if idx < LENGTH inps then revLUPDATE inp2 idx inps else inps)) s.si, [])
     | _ => (* should not happen, inp2 must be bool *) (s, []))
  | _ => (* should not happen, inp1 must be array *) (s, [])) /\
 (* shouldn't be any of these: *)
 (blast_cell s c = (s, [c]))`;

val blast_netlist_def = Define `
 (blast_netlist s [] = (s, [])) /\
 (blast_netlist s (c::cs) =
  let (s, c') = blast_cell s c;
      (s, cs') = blast_netlist s cs in
   (s, c' ++ cs'))`;

val blast_regs_def = Define `
 (blast_regs s [] = return []) /\
 (blast_regs s ((ty, dest, destnum, v, inp)::rs) =
  case ty of
    CBool_t =>
     (case OPTION_MAP (blast_cell_input s) inp of (* TODO: Can remove OPTION_MAP here... *)
       NONE => do
        rs' <- blast_regs s rs;
        return $ (ty, dest, destnum, v, NONE) :: rs'
       od
     | SOME (BoolInp inp) => do
        rs' <- blast_regs s rs;
        return $ (ty, dest, destnum, v, SOME inp) :: rs'
       od
     | _ => INL TypeError)
  | CArray_t l =>
     case v of
       SOME (CArray vs) =>
        (case inp of
          NONE => do
           rs' <- blast_regs s rs;
           return ((GENLIST (\i. (CBool_t, dest, i, SOME $ CBool $ EL i vs, NONE)) (LENGTH vs)) ++ rs')
          od
        | SOME inp =>
           (case blast_cell_input s inp of
             BoolInp _ => INL TypeError
           | ArrayInp inp' => do
              (* can be false if we are compiling ill-typed circuits: *)
              sum_check (LENGTH vs = LENGTH inp') TypeError;
              rs' <- blast_regs s rs;
              return (MAPi (\i inp. (CBool_t, dest, i, SOME $ CBool $ EL i vs, SOME inp)) inp' ++ rs')
             od))
     | _ => INL TypeError (* we only care about wf+deterministic circuits currently *))`;

val build_si_entry_def = Define `
 build_si_entry (t, var, n, v, inp) = case t of
   CBool_t => NONE
 | CArray_t l => SOME (RegVar var 0, ArrayInp $ GENLIST (\i. VarInp (RegVar var i) NONE) l)`;

val option_flatMap_def = Define `
 (option_flatMap f [] = []) /\
 (option_flatMap f (x::xs) =
  case f x of
    NONE => option_flatMap f xs
  | SOME x => x :: option_flatMap f xs)`;

val blast_circuit_def = Define `
 blast_circuit (Circuit extenv regs nl) tmpnum =
  let s = <| si := fromList var_cmp (option_flatMap build_si_entry regs);
             extenv := extenv;
             tmpnum := tmpnum |>;
             (s', nl') = blast_netlist s nl in
   do
    regs' <- blast_regs s' regs;
    return (Circuit extenv regs' nl', s')
   od`;

val _ = export_theory ();
