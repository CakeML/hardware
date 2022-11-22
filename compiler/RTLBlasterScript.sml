open hardwarePreamble;

open ASCIInumbersTheory alistTheory wordsTheory stringTheory bitstringTheory sptreeTheory;
open wordsLib;

open comparisonTheory balanced_mapTheory;

open sumExtraTheory RTLTheory;

val _ = new_theory "RTLBlaster";

Datatype:
 inp_trans = BoolInp cell_input
           | ArrayInp (cell_input list)
End

Datatype:
 inp_marked = GoodInp cell_input
            | BadInp string (num option) (* included data (string+num) only needed for error reporting! *)
End

Datatype:
 inp_trans_marked = MBoolInp inp_marked
                  | MArrayInp (inp_marked list)
End

val _ = type_abbrev_pp ("blastsi_t", ``:(var, inp_trans_marked) balanced_map``);

Datatype:
 blasterstate =
   <| si : blastsi_t
    ; extenv : (string, rtltype) alist
    ; tmpnum : num
    |>
End

Definition var_cmp_def:
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
QED

Definition BadInp2str_def:
 (BadInp2str reg NONE = reg) ∧
 (* i is confusing currently since reg indexing is backwards (w.r.t. everything else),
    should change that... *)
 (BadInp2str reg (SOME i) = reg (*++ "[" ++ (num_to_dec_string i) ++ "]"*))
End

Definition inp_marked_get_def:
 (inp_marked_get (GoodInp inp) = INR inp) ∧
 (inp_marked_get (BadInp reg idx) = INL (CombError $ "Bad cell input: " ++ BadInp2str reg idx))
End

Theorem inp_marked_get_INR:
 ∀minp inp. inp_marked_get minp = INR inp ⇔ minp = GoodInp inp
Proof
 Cases \\ simp [inp_marked_get_def]
QED

Definition blast_cell_input_def:
 (blast_cell_input s (ConstInp (CBool b)) = INR $ BoolInp $ ConstInp $ CBool b) /\
 (blast_cell_input s (ConstInp (CArray bs)) = INR $ ArrayInp $ MAP (ConstInp o CBool) bs) /\

 (blast_cell_input s (ExtInp var idx) = case idx of
   NoIndexing =>
    (case ALOOKUP s.extenv var of
       NONE => INL TypeError
     | SOME CBool_t => INR $ BoolInp $ ExtInp var idx
     | SOME (CArray_t l) => INR $ ArrayInp $ GENLIST (\i. ExtInp var (Indexing $ l - 1 - i)) l)
 | Indexing _ => INR $ BoolInp (ExtInp var idx)
 | SliceIndexing i1 i2 => INR $ ArrayInp $ GENLIST (\i. ExtInp var (Indexing $ i1 - i)) (i1 - i2 + 1)) /\

 (blast_cell_input s (VarInp var idx) = case lookup var_cmp var s.si of
   NONE => INR $ BoolInp (VarInp var idx)
 | SOME (MBoolInp (GoodInp inp)) => INR $ BoolInp inp (* we know that idx must be NONE here *)
 | SOME (MBoolInp (BadInp reg idx)) => INL $ CombError $ "Bad cell input: " ++ BadInp2str reg idx
 | SOME (MArrayInp inps) =>
    case idx of
      NoIndexing => sum_map ArrayInp (sum_mapM inp_marked_get inps)
     (* if-expression only needed for ill-typed netlists *)
    | Indexing idx =>
       if idx < LENGTH inps then
        sum_map BoolInp (inp_marked_get (revEL idx inps))
       else
        INL InvalidIndex
    | SliceIndexing i1 i2 => sum_map ArrayInp (sum_mapM inp_marked_get (rev_slice inps i1 i2)))
End

Definition blaster_new_names_def:
 blaster_new_names s len = (s with tmpnum := s.tmpnum + len, s.tmpnum)
End

Definition blast_cell_bitwise_def:
 (blast_cell_bitwise s (Cell1 CNot out inp) = do
  inp <- blast_cell_input s inp;
  return $ case inp of
  | BoolInp inp => (s, [Cell1 CNot out inp])
  | ArrayInp inps =>
     let (s, tmpnum) = blaster_new_names s (LENGTH inps);
         outs = GENLIST (\i. GoodInp $ VarInp (NetVar (i + tmpnum)) NoIndexing) (LENGTH inps);
         s = s with si := insert var_cmp (NetVar out) (MArrayInp outs) s.si in
      (s, MAPi (\i inp. Cell1 CNot (tmpnum + i) inp) inps)
 od) ∧

 (blast_cell_bitwise s (Cell2 cell2 out inp1 inp2) = do
  inp1 <- blast_cell_input s inp1;
  inp2 <- blast_cell_input s inp2;
  return $ case (inp1, inp2) of
  | (BoolInp inp1, BoolInp inp2) => (s, [Cell2 cell2 out inp1 inp2])
  (*| (ArrayInp inps1, ArrayInp inps2) =>
     let (s, tmpnum) = blaster_new_names s (LENGTH inps1);
         outs = GENLIST (\i. VarInp (NetVar (i + tmpnum)) NONE) (LENGTH inps1);
         s = s with si := insert var_cmp (NetVar out) (ArrayInp outs) s.si in
      (s, MAPi (\i (inp1, inp2). Cell2 cell2 (tmpnum + i) inp1 inp2) (ZIP (inps1, inps2)))*)
  | _ => (* does not happen on well-typed netlists: *) (s, [])
 od)
End

Definition blast_cell_add1_def:
 blast_cell_add1 tmpnum cin l r =
  let tmpinp offset = VarInp (NetVar (tmpnum + offset)) NoIndexing;
  cells = [
   Cell2 CXOr tmpnum l r;
   Cell2 CXOr (tmpnum + 1) (tmpinp 0) cin;
   Cell2 CAnd (tmpnum + 2) cin (tmpinp 0);
   Cell2 CAnd (tmpnum + 3) l r;
   Cell2 COr (tmpnum + 4) (tmpinp 2) (tmpinp 3)] in
  (tmpnum + 5, tmpinp 1, tmpinp 4, cells)
End

Definition blast_cell_addarray_def:
 (blast_cell_addarray tmpnum cin (l::ls) (r::rs) =
  let (tmpnum, out, cout, cells1) = blast_cell_add1 tmpnum cin l r in
  let (tmpnum, outs, cout, cells) = blast_cell_addarray tmpnum cout ls rs in
   (tmpnum, out :: outs, cout, cells1 ++ cells)) ∧
 (* empty and remaining nonsense cases *)
 (blast_cell_addarray tmpnum cin _ _ = (tmpnum, [], cin, []))
End

Definition blast_cell_add_def:
 blast_cell_add s out inp1 inp2 = do
  inp1 <- blast_cell_input s inp1;
  inp2 <- blast_cell_input s inp2;
  return $ case (inp1, inp2) of
   (ArrayInp inps1, ArrayInp inps2) =>
    (let (tmpnum, outs, cout, cells) =
          blast_cell_addarray s.tmpnum (ConstInp (CBool F)) (REVERSE inps1) (REVERSE inps2) in
     (s with <| tmpnum := tmpnum; si := insert var_cmp (NetVar out) (MArrayInp (MAP GoodInp (REVERSE outs))) s.si |>, cells))
  | _ => (s, []) (* does not happen on well-typed netlists *)
 od
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
    (SUC tmpnum, [cell3], [VarInp (NetVar tmpnum) NoIndexing])
   else
    let (tmpnum', cells, outs) = blast_cell_equal_luts (SUC tmpnum) lhst rhst in
     (tmpnum', cell3 :: cells, VarInp (NetVar tmpnum) NoIndexing :: outs)
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
    (tmpnum + 2, SNOC carrycell cells, VarInp (NetVar (SUC tmpnum)) (Indexing (LENGTH outs - 1)))
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
 blast_cell_equal s out inp1 inp2 = do
  inp1 <- blast_cell_input s inp1;
  inp2 <- blast_cell_input s inp2;
  return $ case (inp1, inp2) of
    (BoolInp inp1, BoolInp inp2) =>
      (s, [Cell2 CEqual out inp1 inp2])
  | (ArrayInp inps1, ArrayInp inps2) =>
     (let (tmpnum, cells, out') = blast_cell_equalarray s.tmpnum (ConstInp (CBool T)) inps1 inps2 in
      (s with <| tmpnum := tmpnum; si := insert var_cmp (NetVar out) (MBoolInp (GoodInp out')) s.si |>, cells))
  | _ => (s, []) (* does not happen on well-typed netlists *)
 od
End

Definition gol_mux_length_def:
 gol_mux_length = 4
End

Definition gol_mux_out_def:
 gol_mux_out = 3
End

Definition gol_mux_def:
 gol_mux tmpnum inpc inpt inpf =
  [Cell2 CAnd tmpnum inpc inpt;
   Cell1 CNot (tmpnum + 1) inpc;
   Cell2 CAnd (tmpnum + 2) (VarInp (NetVar (tmpnum + 1)) NoIndexing) inpf;
   Cell2 COr (tmpnum + 3) (VarInp (NetVar tmpnum) NoIndexing) (VarInp (NetVar (tmpnum + 2)) NoIndexing)]
End

(* variant for array *)
Definition gol_mux_array_def:
 gol_mux_array tmpnum inpc not_inpc inpt inpf =
  [Cell2 CAnd tmpnum inpc inpt;
   Cell2 CAnd (tmpnum + 1) not_inpc inpf;
   Cell2 COr (tmpnum + 2) (VarInp (NetVar tmpnum) NoIndexing) (VarInp (NetVar (tmpnum + 1)) NoIndexing)]
End

Definition blast_cell_def:
 (blast_cell s (Cell1 CNot out inp1) = blast_cell_bitwise s (Cell1 CNot out inp1)) ∧

 (blast_cell s (Cell2 cell2 out inp1 inp2) = 
  case cell2 of
    CAnd => blast_cell_bitwise s (Cell2 cell2 out inp1 inp2)
  | COr => blast_cell_bitwise s (Cell2 cell2 out inp1 inp2)
  | CXOr => blast_cell_bitwise s (Cell2 cell2 out inp1 inp2)
  | CEqual => blast_cell_equal s out inp1 inp2
  | CAdd => blast_cell_add s out inp1 inp2) ∧

 (blast_cell s (CellMux out inp1 inp2 inp3) = do
  inp1 <- blast_cell_input s inp1;
  inp2 <- blast_cell_input s inp2;
  inp3 <- blast_cell_input s inp3;
  return $ case (inp1, inp2, inp3) of
    (BoolInp inp1, BoolInp inp2, BoolInp inp3) => 
     let (s, tmpnum) = blaster_new_names s gol_mux_length;
         s = s with si := insert var_cmp (NetVar out) (MBoolInp $ GoodInp $ VarInp (NetVar (tmpnum + gol_mux_out)) NoIndexing) s.si in
     (s, gol_mux tmpnum inp1 inp2 inp3)
  | (BoolInp inp1, ArrayInp inps1, ArrayInp inps2) =>
     let (s, tmpnum) = blaster_new_names s (1 + 3*(LENGTH inps1));
         outs = GENLIST (\i. GoodInp (VarInp (NetVar (tmpnum + 1 + 3*i + 2)) NoIndexing)) (LENGTH inps1);
         s = s with si := insert var_cmp (NetVar out) (MArrayInp outs) s.si;
         not_inp1_cell = Cell1 CNot tmpnum inp1;
         not_inp1 = VarInp (NetVar tmpnum) NoIndexing in
      (s, not_inp1_cell :: (FLAT $ MAP2i (\i inp2 inp3. gol_mux_array (tmpnum + 1 + 3*i) inp1 not_inp1 inp2 inp3) inps1 inps2))
  | _ => (* does not happen on well-typed netlists: *) (s, [])
 od) ∧

 (blast_cell s (CellArrayWrite out inp1 idx inp2) =
  case inp1 of
   VarInp var NoIndexing => do
    inp2 <- blast_cell_input s inp2;
    case (lookup var_cmp var s.si, inp2) of
     (SOME (MArrayInp inps), BoolInp inp2) =>
      INR (s with si := insert var_cmp (NetVar out) (MArrayInp (if idx < LENGTH inps then revLUPDATE (GoodInp inp2) idx inps else inps)) s.si, [])
    | _ => INL TypeError (* might work with (s, []) here instead, not important anyway *)
 od
  | _ => INL TypeError) ∧

 (blast_cell s c = return (s, [c]))
End

Definition blast_netlist_def:
 (blast_netlist s [] = return (s, [])) /\
 (blast_netlist s (c::cs) = do
  (s, c') <- blast_cell s c;
  (s, cs') <- blast_netlist s cs;
  return (s, c' ++ cs')
 od)
End

Definition blast_regs_def:
 (blast_regs s [] = return []) /\
 (blast_regs s (((reg, i), rdata)::rs) =
 case rdata.reg_type of
  Reg =>
  (case rdata.type of
    CBool_t =>
     (case rdata.inp of
       NONE => do
        rs' <- blast_regs s rs;
        return $ ((reg, i), rdata) :: rs'
       od
     | SOME inp => do
        inp <- blast_cell_input s inp;
        (case inp of
           ArrayInp _ => INL TypeError
         | BoolInp inp => do
            rs' <- blast_regs s rs;
            return $ ((reg, i), rdata with inp := SOME inp) :: rs'
           od)
        od)
  | CArray_t l =>
     case rdata.init of
       SOME (CArray vs) =>
        (case rdata.inp of
          NONE => do
           rs' <- blast_regs s rs;
           return $ GENLIST (λi. ((reg, i), <| type := CBool_t; reg_type := Reg; init := SOME $ CBool $ EL i vs; inp := NONE |>)) (LENGTH vs) ++ rs'
          od
        | SOME inp => do
          inp <- blast_cell_input s inp;
          (case inp of
             BoolInp _ => INL TypeError
           | ArrayInp inp => do
              (* can be false if we are compiling ill-typed circuits: *)
              sum_check (LENGTH vs = LENGTH inp) TypeError;
              rs' <- blast_regs s rs;
              return $ MAPi (λi inp. ((reg, i), <| type := CBool_t; reg_type := Reg; init := SOME $ CBool $ EL i vs; inp := SOME inp |>)) inp ++ rs'
             od)
          od)
     | _ => INL TypeError (* we only care about wf+deterministic circuits currently *))
   | PseudoReg =>
      blast_regs s rs)
End

Definition mk_inp_marked_def:
 (mk_inp_marked Reg reg i = GoodInp (VarInp (RegVar reg i) NoIndexing)) ∧
 (mk_inp_marked PseudoReg reg i = BadInp reg (SOME i))
End

Definition build_combs_si_reg_entry_def:
 build_combs_si_reg_entry ((reg, i), rdata) =
  case rdata.type of
    CBool_t => (case rdata.reg_type of
                  Reg => NONE
                | PseudoReg => SOME (RegVar reg i, MBoolInp $ BadInp reg NONE))
  | CArray_t l => SOME (RegVar reg i, MArrayInp $ GENLIST (mk_inp_marked rdata.reg_type reg) l)
End

Definition option_flatMap_def:
 (option_flatMap f [] = []) /\
 (option_flatMap f (x::xs) =
  case f x of
    NONE => option_flatMap f xs
  | SOME x => x :: option_flatMap f xs)
End
        
Definition initial_si_def:
 initial_si regs = fromList var_cmp $ option_flatMap build_combs_si_reg_entry regs
End

Definition blast_out_def:
 (blast_out s (var, OutInp inp) = do
   binp <- blast_cell_input s inp;
   return (case binp of
             BoolInp inp => (var, OutInp inp)
           | ArrayInp inps => (var, OutInps inps))
  od) ∧
 (blast_out s x = (* should never happen *) return x)
End

Definition blast_outs_def:
 blast_outs s outs = sum_mapM (blast_out s) outs
End

(* This can be made more fine-grained by not requiring everything to be good inputs,
   i.e. passing blast_cell_input. But the current way is simpler for now. *)
Definition blast_pseudoreg_inp_def:
 blast_pseudoreg_inp s inp = do
  binp <- blast_cell_input s inp;
  return $ case binp of
             BoolInp inp => MBoolInp $ GoodInp inp
           | ArrayInp inps => MArrayInp $ MAP GoodInp inps
 od
End

Definition build_ffs_si_reg_entry_def:
 build_ffs_si_reg_entry s ((reg, i), rdata) =
  case rdata.reg_type of
   PseudoReg =>
    (case rdata.inp of
      NONE => 
        (case rdata.init of
          NONE => INL Impossible (* cannot happen since regs are deterministic *)
         | SOME init => do
           minp <- blast_pseudoreg_inp s (ConstInp init);
           return $ SOME (RegVar reg i, minp)
          od)
     | SOME inp => do
      minp <- blast_pseudoreg_inp s inp;
      (* since we might have been given an ill-typed netlist *)
      (case (rdata.type, minp) of
         (CBool_t, MBoolInp inp) => return $ SOME (RegVar reg i, minp)
       | (CArray_t l, MArrayInp inps) => do
          sum_check (LENGTH inps = l) TypeError;
          return $ SOME (RegVar reg i, minp)
         od
       | _ => INL TypeError)
     od)
  | Reg => 
     return $ case rdata.type of
                CBool_t => NONE
              | CArray_t l =>
                 SOME (RegVar reg i, MArrayInp $ GENLIST (λi. GoodInp $ VarInp (RegVar reg i) NoIndexing) l)
End

Definition sum_option_flatMap_def:
 (sum_option_flatMap f [] = INR []) /\
 (sum_option_flatMap f (x::xs) = do
  x' <- f x;
  case x' of
    NONE => sum_option_flatMap f xs
  | SOME x' => do
     xs' <- sum_option_flatMap f xs;
     return $ x' :: xs'
    od
  od)
End

(* Would be nice to drop all NetVars here, but then we have to prove that the ffs netlist
   never refers to combs netlist, which we have not done yet.
   (Nice because we would get better performance.) *)
Definition ffs_si_def:
 ffs_si s regs = sum_map (FOLDR (λ(k,v) t. insert var_cmp k v t) s.si)
                         (sum_option_flatMap (build_ffs_si_reg_entry s) regs)
End

Definition blast_circuit_def:
 blast_circuit (Circuit extenv outs regs nl_combs nl_ffs) tmpnum = do
  s <<- <| si := initial_si regs; extenv := extenv; tmpnum := tmpnum |>;

  (s, nl_combs') <- blast_netlist s nl_combs;

  new_si <- ffs_si s regs;
  s <<- s with si := new_si;
  (s, nl_ffs') <- blast_netlist s nl_ffs;

  regs' <- blast_regs s regs;
  outs' <- blast_outs s outs;
  return (Circuit extenv outs' regs' (nl_combs' ++ nl_ffs') [], s)
 od
End

val _ = export_theory ();
