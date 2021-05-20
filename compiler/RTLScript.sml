open hardwarePreamble;

open ASCIInumbersTheory alistTheory wordsTheory stringTheory bitstringTheory sptreeTheory;
open wordsLib;

open balanced_mapTheory;

open oracleTheory sumExtraTheory verilogTheory;

val _ = new_theory "RTL";

(* types *)

val _ = Datatype `
 rtltype = CBool_t | CArray_t num`;

(* values *)

val _ = Datatype `
 value = CBool bool
       | CArray (bool list)`;

val is_CBool_def = Define `
 (is_CBool (CBool _) = T) /\
 (is_CBool (CArray _) = F)`;

val get_bool_def = Define `
 (get_bool (CBool b) = INR b) /\
 (get_bool (CArray bs) = INL TypeError)`;

Theorem get_bool_INR:
 !v b. get_bool v = INR b <=> v = CBool b
Proof
 Cases \\ rw [get_bool_def]
QED

val is_CArray_def = Define `
 (is_CArray (CBool _) = F) /\
 (is_CArray (CArray _) = T)`;

val get_array_def = Define `
 (get_array (CBool b) = INL TypeError) /\
 (get_array (CArray bs) = INR bs)`;

Theorem get_array_INR:
 !v bs. get_array v = INR bs <=> v = CArray bs
Proof
 Cases \\ rw [get_array_def]
QED

Definition value_bits_def:
 (value_bits (CBool b) = 1) ∧
 (value_bits (CArray bs) = LENGTH bs)
End

val same_shape_def = Define `
 (same_shape (CBool x) (CBool y) <=> T) /\
 (same_shape (CArray xs) (CArray ys) <=> LENGTH xs = LENGTH ys) /\
 (same_shape _ _ <=> F)`;

Theorem same_shape_cases:
 ∀v v'.
 same_shape v v' ⇔ (∃b b'. v = CBool b ∧ v' = CBool b') ∨
                   (∃bs bs'. v = CArray bs ∧ v' = CArray bs' ∧ LENGTH bs = LENGTH bs')
Proof
 Cases \\ Cases \\ simp [same_shape_def]
QED

(* types and values *)

val has_rtltype_v_def = Define `
 (has_rtltype_v (CBool v) CBool_t <=> T) /\
 (has_rtltype_v (CArray vs) (CArray_t l) <=> l = LENGTH vs) /\
 (has_rtltype_v _ _ <=> F)`;

(* programs *)

val _ = Datatype `
 var = RegVar string num (* second argument useful when bitblasting *)
     | NetVar num`;

val is_netvar_def = Define `
 (is_netvar (NetVar _) = T) /\
 (is_netvar _ = F)`;

Theorem is_netvar_not_reg:
 !var. is_netvar var <=> !reg i. var <> RegVar reg i
Proof
 Cases \\ rw [is_netvar_def]
QED
 
val var_num_def = Define `
 (var_num (RegVar _ _) = NONE) /\
 (var_num (NetVar n) = SOME n)`;

Datatype:
 cell_input_idx = NoIndexing
                | Indexing num
                | SliceIndexing num num
End

Datatype:
 cell_input = ConstInp value
            | ExtInp string cell_input_idx
            | VarInp var cell_input_idx
End

val cell_input_is_var_def = Define `
 (cell_input_is_var (ConstInp _) var <=> F) /\
 (cell_input_is_var (ExtInp _ _) var <=> F) /\
 (cell_input_is_var (VarInp var' _) var <=> var' = var)`;

val cell_input_num_def = Define `
 (cell_input_num (ConstInp _) = NONE) /\
 (cell_input_num (ExtInp _ _) = NONE) /\
 (cell_input_num (VarInp var _) = var_num var)`;

Definition not_reg_inp_def:
 (not_reg_inp (ConstInp _) <=> T) /\
 (not_reg_inp (ExtInp _ _) <=> T) /\
 (not_reg_inp (VarInp var _) <=> is_netvar var)
End

val _ = Datatype `
 cell1 = CNot`;

val _ = Datatype `
 cell2 = CAnd | COr | CEqual | CAdd`;

val _ = Datatype `
 (* output := op input0 input1 ... inputn <=> op output intput1 input2 ... inputn *)
 cell = NDetCell num rtltype
      | Cell1 cell1 num cell_input
      | Cell2 cell2 num cell_input cell_input
      | CellMux num cell_input cell_input cell_input
      | CellArrayWrite num cell_input num cell_input
      (* the inputs must be bools, output high iff input in tb: *)
      | CellLUT num (cell_input list) (bool list list)
      (* model of CARRY4 (carry chain primitive) in 7 Series FPGAs,
         except (currently) no input CYINIT.

         on the abstraction level this is used, all inputs are bools, so this gates
         takes list of bools as inputs rather than arrays as inputs. (outputs are arrays however.)

         ports: sum out -> carry out -> carry in -> "data in" (lhs) -> "select in" (rhs) *)
      | Carry4 num num cell_input (cell_input list) (cell_input list)`;

(* todo: rename to cell_outputs *)
val cell_output_def = Define `
 (cell_output (NDetCell out _) = [out]) /\
 (cell_output (Cell1 _ out _) = [out]) /\
 (cell_output (Cell2 _ out _ _) = [out]) /\
 (cell_output (CellMux out _ _ _) = [out]) /\
 (cell_output (CellArrayWrite out _ _ _) = [out]) /\
 (cell_output (CellLUT out _ _) = [out]) ∧
 (cell_output (Carry4 out1 out2 _ _ _) = [out1; out2])`;

Definition cell_inputs_def:
 (cell_inputs (NDetCell _ _) = []) /\
 (cell_inputs (Cell1 _ _ in1) = [in1]) /\
 (cell_inputs (Cell2 _ _ in1 in2) = [in1; in2]) /\
 (cell_inputs (CellMux _ in1 in2 in3) = [in1; in2; in3]) /\
 (cell_inputs (CellArrayWrite _ in1 _ in2) = [in1; in2]) /\
 (cell_inputs (CellLUT _ ins _) = ins) ∧
 (cell_inputs (Carry4 _ _ in1 lhs rhs) = in1 :: lhs ++ rhs)
End

(*
  component 1) regs (type, name, optional initial value, connection to netlist)
  component 2) combinational netlist
*)

Datatype:
 reg_type = Reg | PseudoReg
End

Theorem reg_type_not_PseudoReg:
 ∀reg_type. reg_type ≠ PseudoReg ⇔ reg_type = Reg
Proof
 Cases \\ simp []
QED

Datatype:
 reg_metadata =
  <| type : rtltype
   ; reg_type : reg_type
   ; init : value option
   ; inp : cell_input option |>
End

Datatype:
 out_spec = OutInp cell_input
          | OutInps (cell_input list)
End

Datatype:
 circuit = Circuit ((string, rtltype) alist)
                   ((string, out_spec) alist)
                   (((string # num), reg_metadata) alist)
                   (cell list) (* nl_combs *)
                   (cell list) (* nl_ffs *)
End

val _ = type_abbrev("regty", ``:((string # num) # reg_metadata)``);

val circuit_extenv_def = Define `
 circuit_extenv (Circuit extenv _ _ _ _) = extenv`;

val circuit_outs_def = Define `
 circuit_outs (Circuit _ outs _ _ _) = outs`;

val circuit_regs_def = Define `
 circuit_regs (Circuit _ _ regs _ _) = regs`;

val circuit_nl_combs_def = Define `
 circuit_nl_combs (Circuit _ _ _ nl _) = nl`;

val circuit_nl_ffs_def = Define `
 circuit_nl_ffs (Circuit _ _ _ _ nl) = nl`;

Theorem Circuit_components:
 ∀c. Circuit (circuit_extenv c) (circuit_outs c) (circuit_regs c) (circuit_nl_combs c) (circuit_nl_ffs c) = c
Proof
 Cases \\ EVAL_TAC
QED

(* semantics *)

val _ = type_abbrev("env", ``:(var, value) alist``);

val _ = Datatype `
 rtlstate =
  <| env : env
   ; fbits : num -> bool |>`;

val cget_var_def = Define `
 cget_var s name = case ALOOKUP s.env name of
                     SOME v => INR v
                   | NONE => INL UnknownVariable`;

Theorem cget_var_INL:
 !s var err. cget_var s var = INL err ==> err = UnknownVariable
Proof
 rw [cget_var_def] \\ every_case_tac \\ fs []
QED

Definition cget_fext_var_def:
 cget_fext_var idx v =
  case idx of
     NoIndexing => INR v
   | Indexing idx =>
      (case v of
        CBool b => INL TypeError
      | CArray bs => sum_map CBool $ sum_revEL idx bs)
   | SliceIndexing i1 i2 =>
      (case v of
        CBool b => INL TypeError
      | CArray bs =>
         let len = LENGTH bs in
          if i1 < len ∧ i2 ≤ i1 then
           INR (CArray (TAKE (i1 - i2 + 1) (DROP (len - i1 - 1) bs)))
          else
           INL InvalidIndex)
End

Theorem cget_fext_var_NONE[simp]:
 cget_fext_var NoIndexing = INR
Proof
 rw [FUN_EQ_THM, cget_fext_var_def]
QED

val cell_inp_run_def = Define `
 (cell_inp_run fext s (ConstInp v) = INR v) /\
 (cell_inp_run fext s (ExtInp var idx) = sum_bind (fext var) (cget_fext_var idx)) /\
 (cell_inp_run fext s (VarInp var idx) = sum_bind (cget_var s var) (cget_fext_var idx))`;

Theorem cell_inp_run_ConstInp:
 ∀fext s b. cell_inp_run fext s (ConstInp (CBool b)) = INR (CBool b)
Proof
 simp [cell_inp_run_def]
QED

val cset_var_def = Define `
 cset_var s k v = s with env := (k, v) :: s.env`;

val ndetcell_run_def = Define `
 (ndetcell_run s CBool_t = let (b, fbits) = oracle_bit s.fbits in (s with fbits := fbits, CBool b)) /\
 (ndetcell_run s (CArray_t l) = let (bs, fbits) = oracle_bits s.fbits l in (s with fbits := fbits, CArray bs))`;

val cell1_run_def = Define `
 (cell1_run f (CBool b) <=> (INR $ CBool $ f b)) /\
 (cell1_run f (CArray bs) <=> (INR $ CArray $ MAP f bs))`;

Definition cell2_run_def:
 (cell2_run CAnd (CBool in1) (CBool in2) = (INR $ CBool (in1 ∧ in2))) ∧
 (cell2_run COr (CBool in1) (CBool in2) = (INR $ CBool (in1 ∨ in2))) ∧
 (cell2_run CEqual (CBool in1) (CBool in2) = (INR $ CBool (in1 = in2))) ∧
 (cell2_run CEqual (CArray in1) (CArray in2) = do
  sum_check (LENGTH in1 = LENGTH in2) TypeError;
  return $ CBool (in1 = in2)
 od) ∧
 (cell2_run CAdd (CArray in1) (CArray in2) = do
  sum_check (LENGTH in1 = LENGTH in2) TypeError;
  return $ CArray $ fixwidth (LENGTH in1) $ n2v $ (v2n in1) + (v2n in2)
 od) ∧
 (cell2_run _ _ _ = INL TypeError)
End

val cellMux_run_def = Define `
 (cellMux_run (CBool c) (CBool in1) (CBool in2) = (INR $ CBool $ if c then in1 else in2)) /\
 (cellMux_run (CBool c) (CArray in1) (CArray in2) = do
  sum_check (LENGTH in1 = LENGTH in2) TypeError;
  return $ CArray $ if c then in1 else in2
 od) /\
 (cellMux_run _ _ _ = INL TypeError)`;

val cellArrayWrite_run_def = Define ‘
 (cellArrayWrite_run (CArray bs) n (CBool b) =
  (INR $ CArray $ if n < LENGTH bs then (revLUPDATE b n bs) else bs)) /\
 (cellArrayWrite_run _ _ _ = INL TypeError)’;

val cellLUT_run_def = Define `
 cellLUT_run fext s ins tb = do
  ins <- sum_mapM (cell_inp_run fext s) ins;
  ins <- sum_mapM get_bool ins;
  return $ CBool $ MEM ins tb
 od`;

(*
         /-------\
 cond -->| MUXCY |
         ---------
           ^  ^
 in1 -----/  /
 in2 -------/
*) 
Definition carry4_muxcy_def:
 carry4_muxcy cond in1 in2 ⇔ if cond then in2 else in1
End

(*
        \\------\
 in1 -->|| XOR  |
 in2 -->||      |
        //------/ 
*)
Definition carry4_xor_def:
 carry4_xor in1 in2 ⇔ in1 ≠ in2
End
 
(* CYINIT represented implicitly: If cin is a constant, then it represents CYINIT,
   otherwise it's a cout output from the previous carry cell. *)
Definition cellCarry4_run_def:
 cellCarry4_run cin di s = do
  cin <- get_bool cin;
  di <- sum_mapM get_bool di;
  s <- sum_mapM get_bool s;
  (case (di, s) of
     ([di3; di2; di1; di0], [s3; s2; s1; s0]) =>
      (let o0 = carry4_xor s0 cin;
           co0 = carry4_muxcy s0 di0 cin;

           o1 = carry4_xor s1 co0;
           co1 = carry4_muxcy s1 di1 co0;

           o2 = carry4_xor s2 co1;
           co2 = carry4_muxcy s2 di2 co1;

           o3 = carry4_xor s3 co2;
           co3 = carry4_muxcy s3 di3 co2 in
       return (CArray [o3; o2; o1; o0], CArray [co3; co2; co1; co0]))
   | _ => INL TypeError) (* both must be of length 4... *)
 od
End

Definition cell_run_def:
 (cell_run fext s (NDetCell out t) =
  let (s, res) = ndetcell_run s t in
   return $ cset_var s (NetVar out) res) /\
 (cell_run fext s (Cell1 CNot out in1) = do
  in1 <- cell_inp_run fext s in1;
  res <- cell1_run ($~) in1;
  return $ cset_var s (NetVar out) res
 od) /\
 (cell_run fext s (Cell2 op2 out in1 in2) = do
  in1 <- cell_inp_run fext s in1;
  in2 <- cell_inp_run fext s in2;
  res <- cell2_run op2 in1 in2;
  return $ cset_var s (NetVar out) res
 od) /\
 (cell_run fext s (CellMux out c in1 in2) = do
  c <- cell_inp_run fext s c;
  in1 <- cell_inp_run fext s in1;
  in2 <- cell_inp_run fext s in2;
  res <- cellMux_run c in1 in2;
  return $ cset_var s (NetVar out) res
 od) /\
 (cell_run fext s (CellArrayWrite out in1 n in2) = do
  in1 <- cell_inp_run fext s in1;
  in2 <- cell_inp_run fext s in2;
  res <- cellArrayWrite_run in1 n in2;
  return $ cset_var s (NetVar out) res
 od) /\ 
 (cell_run fext s (CellLUT out ins tb) = do
  res <- cellLUT_run fext s ins tb;
  return $ cset_var s (NetVar out) res
 od) ∧
 (cell_run fext s (Carry4 out cout cin lhs rhs) = do
  cin <- cell_inp_run fext s cin;
  lhs <- sum_mapM (cell_inp_run fext s) lhs;
  rhs <- sum_mapM (cell_inp_run fext s) rhs;
  (outres, coutres) <- cellCarry4_run cin lhs rhs;
  return $ cset_var (cset_var s (NetVar cout) coutres) (NetVar out) outres
 od)
End

val reg_run_def = Define `
 reg_run fext s_net s_reg ((reg, i), rdata) =
  case rdata.inp of
    NONE => INR s_reg
  | SOME inp => do
     v <- cell_inp_run fext s_net inp;
     if has_rtltype_v v rdata.type then
      return $ cset_var s_reg (RegVar reg i) v
     else
      INL TypeError
    od`;

Definition is_RegVar_def:
 (is_RegVar (RegVar _ _) = T) ∧
 (is_RegVar (NetVar _) = F)
End

Theorem is_RegVar_cases:
 ∀var. is_RegVar var = ∃reg i. var = RegVar reg i
Proof
 Cases \\ simp [is_RegVar_def]
QED

(* Common part of all netlist cycle steps *)
Definition netlist_step_def:
 netlist_step fext s comb_cells ff_cells regs = do
  s <- sum_foldM (cell_run fext) s comb_cells;
  s <- sum_foldM (reg_run fext s) s (FILTER (λ(var, data). data.reg_type = PseudoReg) regs);
  sum_foldM (cell_run fext) s ff_cells
 od
End

Definition netlist_run_def:
 (netlist_run fext s comb_cells ff_cells regs 0 = netlist_step (fext 0) s comb_cells ff_cells regs) ∧
 (netlist_run fext s comb_cells ff_cells regs (SUC n) = do
  s <- netlist_run fext s comb_cells ff_cells regs n;

  (* Note that we cannot re-run the pseudo regs here,
     since we do not know if they actually represent combinational behavior! *)
  s <- sum_foldM (reg_run (fext n) s)
                 (s with env := FILTER (is_RegVar o FST) s.env)
                 (FILTER (λ(var, data). data.reg_type = Reg) regs);

  netlist_step (fext (SUC n)) s comb_cells ff_cells regs
 od)
End

val rtl_nd_value_def = Define `
 (rtl_nd_value oracle CBool_t <=> let (b, oracle') = oracle_bit oracle in (CBool b, oracle')) /\
 (rtl_nd_value oracle (CArray_t len) <=> let (bs, oracle') = oracle_bits oracle len in (CArray bs, oracle'))`;

(* todo: rewrite to sum_foldM? *)
val init_run_def = Define `
 (init_run s [] = INR s) /\
 (init_run s (((reg, i), rdata) :: decls) =
  case rdata.init of
    NONE => let (v, fbits') = rtl_nd_value s.fbits rdata.type in
             init_run ((cset_var s (RegVar reg i) v) with fbits := fbits') decls
  | SOME v => if has_rtltype_v v rdata.type then
               init_run (cset_var s (RegVar reg i) v) decls
              else
               INL TypeError)`;

Definition out_run_def:
 (out_run fext s (var, OutInp inp) = do
  b <- cell_inp_run fext s inp;
  return (var, b)
 od) ∧
 (out_run fext s (var, OutInps inps) = do
  b <- sum_mapM (cell_inp_run fext s) inps;
  b <- sum_mapM get_bool b;
  return $ (var, CArray b)
 od)
End

Definition circuit_run_def:
 circuit_run fext fbits (Circuit extenv outs regs comb_cells ff_cells) n = do
  s <- init_run <| fbits := fbits; env := [] |> regs;
  s <- netlist_run fext s comb_cells ff_cells regs n;
  res <- sum_mapM (out_run (fext n) s) outs;
  return (res, s.fbits)
 od
End

(* Semantics for circuits without pseudo-regs *)

Definition netlist_run_no_pseudos_def:
 (netlist_run_no_pseudos fext s cells regs 0 =
  sum_foldM (cell_run (fext 0)) s cells) ∧
 (netlist_run_no_pseudos fext s cells regs (SUC n) = do
  s <- netlist_run_no_pseudos fext s cells regs n;
  (* Note that we cannot start from the empty list here since some regs have NONE as input *)
  s <- sum_foldM (reg_run (fext n) s) (s with env := FILTER (is_RegVar o FST) s.env) regs;
  sum_foldM (cell_run (fext (SUC n))) s cells
 od)
End

Definition circuit_run_no_pseudos_def:
 circuit_run_no_pseudos fext fbits (Circuit extenv outs regs comb_cells ff_cells) n = do
  s <- init_run <| fbits := fbits; env := [] |> regs;
  s <- netlist_run_no_pseudos fext s comb_cells regs n;
  res <- sum_mapM (out_run (fext n) s) outs;
  return (res, s.fbits)
 od
End

val _ = export_theory ();
