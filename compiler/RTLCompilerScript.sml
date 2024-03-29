open hardwarePreamble;

open ASCIInumbersTheory alistTheory wordsTheory stringTheory bitstringTheory sptreeTheory;
open wordsLib;

open balanced_mapTheory;

open sumExtraTheory verilogTheory;

open RTLTheory;

val _ = new_theory "RTLCompiler";

(** Phase 1: Verilog to RTL **)

val _ = type_abbrev_pp ("si_t", ``:(string, cell_input) balanced_map``);

val compilerstate_def = Datatype `
 compilerstate =
   <| bsi : si_t list  (* Blocking sigma *)
    ; nbsi : si_t list (* Non-blocking sigma *)
    ; vertypes : declty (* types of verilog variables *)
    ; tmpnum : num     (* free name for new cells *)
    |>`;

val compile_new_name_def = Define `
 compile_new_name s = (s with tmpnum := SUC s.tmpnum, s.tmpnum)`;

(* Expressions *)

(* Redundant maybe? Just factor out op names... *)
val compile_bbop_def = Define `
 (compile_bbop And = CAnd) /\
 (compile_bbop Or = COr) ∧
 (compile_bbop Equal = CEqual)`;

Definition compile_arith_def:
 compile_arith Plus = CAdd
End

(* First case should never matter except in proofs *)
val cset_net_def = Define `
 (cset_net [] k v = []) /\
 (cset_net (b::bs) k v = insert string_cmp k v b :: bs)`;

val cget_net_var_def = Define `
 (cget_net_var [] name = NONE) /\
 (cget_net_var (b::bs) name = case lookup string_cmp name b of
    NONE => cget_net_var bs name
  | SOME v => SOME v)`;

Theorem cget_net_var_cons_empty:
 !var bs. cget_net_var (empty::bs) var = cget_net_var bs var
Proof
 simp [cget_net_var_def, empty_def, lookup_def]
QED

Theorem cget_net_var_empty:
 !var. cget_net_var [empty] var = NONE
Proof
 simp [cget_net_var_cons_empty] \\ simp [cget_net_var_def]
QED

val cget_net_def = Define `
 cget_net bs name = case cget_net_var bs name of
                     NONE => VarInp (RegVar name 0) NoIndexing
                   | SOME v => v`;

Theorem cget_net_cons_empty:
 !var bs. cget_net (empty::bs) var = cget_net bs var
Proof
 simp [cget_net_def, cget_net_var_cons_empty]
QED

Theorem cget_net_empty:
 !var. cget_net [empty] var = VarInp (RegVar var 0) NoIndexing
Proof
 simp [cget_net_cons_empty] \\ simp [cget_net_def, cget_net_var_def]
QED

val compile_type_def = Define `
 (compile_type VBool_t = CBool_t) /\
 (compile_type (VArray_t l) = CArray_t l)`;

Theorem compile_type_bij:
 !t1 t2. compile_type t1 = compile_type t2 <=> t1 = t2
Proof
 Cases \\ Cases \\ rw [compile_type_def]
QED

val compile_value_def = Define `
 (compile_value (VBool b) = CBool b) /\
 (compile_value (VArray bs) = CArray bs)`;

Definition cell_input_idx_def:
 (cell_input_idx (ConstInp (CArray bs)) idx = INR $ ConstInp $ CBool $ revEL idx bs) /\
 (cell_input_idx (ExtInp var NoIndexing) idx = INR $ ExtInp var (Indexing idx)) /\
 (cell_input_idx (VarInp var NoIndexing) idx = INR $ VarInp var (Indexing idx)) /\
 (cell_input_idx _ _ = INL TypeError)
End

Theorem cell_input_idx_INR:
 !inp inp' idx.
 cell_input_idx inp idx = INR inp' ==>
 (?bs. inp = ConstInp (CArray bs)) \/
 (?var. inp = ExtInp var NoIndexing) \/
 (?var. inp = VarInp var NoIndexing)
Proof
 Cases \\ rpt strip_tac
 >- (Cases_on ‘v’ \\ fs [cell_input_idx_def])
 \\ Cases_on ‘c’ \\ fs [cell_input_idx_def]
QED

Definition cell_input_slice_def:
 (cell_input_slice (ConstInp (CArray bs)) i1 i2 = INR $ ConstInp $ CArray $ rev_slice bs i1 i2) /\
 (cell_input_slice (ExtInp var NoIndexing) i1 i2 = INR $ ExtInp var (SliceIndexing i1 i2)) /\
 (cell_input_slice (VarInp var NoIndexing) i1 i2 = INR $ VarInp var (SliceIndexing i1 i2)) /\
 (cell_input_slice _ _ _ = INL TypeError)
End

Theorem cell_input_slice_INR:
 ∀inp inp' i1 i2.
 cell_input_slice inp i1 i2 = INR inp' ⇒
 (?bs. inp = ConstInp (CArray bs)) \/
 (?var. inp = ExtInp var NoIndexing) \/
 (?var. inp = VarInp var NoIndexing)
Proof
 Cases \\ rpt strip_tac
 >- (Cases_on ‘v’ \\ fs [cell_input_slice_def])
 \\ Cases_on ‘c’ \\ fs [cell_input_slice_def]
QED

(* state -> exp -> (new state, netlist, CellInp - output name) *)
Definition compile_exp_def:
 (compile_exp s (Const v) = return (s, [], ConstInp $ compile_value v)) /\
 (compile_exp s (Var v) = return (s, [], cget_net s.bsi v)) /\
 (compile_exp s (InputVar v) = return (s, [], ExtInp v NoIndexing)) /\
 (compile_exp s (ArrayIndex (Var var) _ (Const v)) = do
  i <- ver2n v;
  inp <- cell_input_idx (cget_net s.bsi var) i;
  return (s, [], inp)
 od) /\
 (compile_exp s (ArrayIndex (InputVar var) _ (Const v)) = do
  i <- ver2n v;
  return (s, [], ExtInp var (Indexing i))
 od) /\
 (compile_exp s (ArraySlice (Var var) i1 i2) = do
  inp <- cell_input_slice (cget_net s.bsi var) i1 i2;
  INR (s, [], inp)
 od) /\
 (compile_exp s (ArraySlice (InputVar var) i1 i2) = do
  INR (s, [], ExtInp var (SliceIndexing i1 i2))
 od) /\

 (compile_exp s (BUOp Not e) = do
  (s, nl, inp) <- compile_exp s e;
   (let (s, tmpvar) = compile_new_name s;
       newcell = Cell1 CNot tmpvar inp in
    return (s, SNOC newcell nl, VarInp (NetVar tmpvar) NoIndexing))
 od) /\

 (compile_exp s (BBOp e1 bbop e2) = do
  (s, nl1, inp1) <- compile_exp s e1;
  (s, nl2, inp2) <- compile_exp s e2;
   (let (s, tmpvar) = compile_new_name s;
       newcell = Cell2 (compile_bbop bbop) tmpvar inp1 inp2 in
   return (s, nl1 ++ nl2 ++ [newcell], VarInp (NetVar tmpvar) NoIndexing))
 od) /\

 (compile_exp s (Arith e1 arith e2) = do
  (s, nl1, inp1) <- compile_exp s e1;
  (s, nl2, inp2) <- compile_exp s e2;
   (let (s, tmpvar) = compile_new_name s;
        newcell = Cell2 (compile_arith arith) tmpvar inp1 inp2 in
   return (s, nl1 ++ nl2 ++ [newcell], VarInp (NetVar tmpvar) NoIndexing))
 od) /\

 (compile_exp s (Cmp e1 cmp e2) = do (* only works for equal *)
  (s, nl1, inp1) <- compile_exp s e1;
  (s, nl2, inp2) <- compile_exp s e2;
   (let (s, tmpvar) = compile_new_name s;
        newcell = Cell2 CEqual tmpvar inp1 inp2 in
   return (s, nl1 ++ nl2 ++ [newcell], VarInp (NetVar tmpvar) NoIndexing))
 od) /\

 (compile_exp _ _ = INL NotImplemented)
End

(* Statements *)

val new_block_def = Define `
 new_block s =
  INR (s with <| bsi := empty :: s.bsi; nbsi := empty :: s.nbsi |>)
  : error + compilerstate`;

val pop_block_def = Define `
 pop_block s =
  (INR (s with <| bsi := TL s.bsi; nbsi := TL s.nbsi |>, HD s.bsi, HD s.nbsi))
  : error + (compilerstate # si_t # si_t)`;

(*val in_block_def = Define `
 in_block f s = do
  s' <- new_block s;
  s'' <- f s';
  pop_block s''
 od`;*)

val compile_merge_if_left_def = Define `
 compile_merge_if_left cond otherenv k v (s, newenv, nl) =
  let otherv = cget_net otherenv k;
      (s, n) = compile_new_name s;
      newcell = CellMux n cond v otherv;
      newenv = cset_net newenv k (VarInp (NetVar n) NoIndexing) in
   (s, newenv, SNOC newcell nl)`; (* <-- cons would yield better complexity than snoc here, but is more difficult to prove correct (need to be able to re-order muxes without affecting the result) *)

val compile_merge_if_right_def = Define `
 compile_merge_if_right cond fallback otherenv k v (s, newenv, nl) =
  case cget_net_var otherenv k of
    SOME otherv => (s, newenv, nl)
  | NONE => let otherv = cget_net fallback k;
                (s, n) = compile_new_name s;
                newcell = CellMux n cond otherv v;
                newenv = cset_net newenv k (VarInp (NetVar n) NoIndexing) in
                 (s, newenv, SNOC newcell nl)`; (* <-- complexity comment above applies here as well *)

(* Can probably do this in some much more efficient way *)
(* TODO: Fix names (env -> si) here and related functions *)
val compile_merge_if_def = Define `
 compile_merge_if s env cond tblock fblock =
  let (s, env', nl) = foldrWithKey (compile_merge_if_left cond (fblock :: env)) (s, env, []) tblock in
   foldrWithKey (compile_merge_if_right cond env [tblock]) (s, env', nl) fblock`;

val compile_stmt_def = Define `
 (compile_stmt s Skip = return (s, [])) /\

 (compile_stmt s (Seq p1 p2) = do
  (s, nl1) <- compile_stmt s p1;
  (s, nl2) <- compile_stmt s p2;
  return (s, nl1 ++ nl2) od) /\

 (compile_stmt s (IfElse cond pt pf) = do
  (s, nl, cond) <- compile_exp s cond;

  s <- new_block s;
  (s, tnl) <- compile_stmt s pt;
  (s, tblock, ntblock) <- pop_block s;

  s <- new_block s;
  (s, fnl) <- compile_stmt s pf;
  (s, fblock, nfblock) <- pop_block s;

  (let (s, bsi, bmuxnl) = compile_merge_if s s.bsi cond tblock fblock;
       (s, nbsi, nbmuxnl) = compile_merge_if s s.nbsi cond ntblock nfblock in
   return (s with <| bsi := bsi; nbsi := nbsi |>, nl ++ tnl ++ fnl ++ bmuxnl ++ nbmuxnl))
 od) /\

 (compile_stmt s (BlockingAssign (NoIndexing var) e) =
  case e of
    NONE =>
     let (s, n) = compile_new_name s in (do
      t <- decls_type s.vertypes var;
      return (s with bsi := cset_net s.bsi var (VarInp (NetVar n) NoIndexing), [NDetCell n (compile_type t)])
     od)
  | SOME e => do
     (s, nl, inp) <- compile_exp s e;
     return (s with bsi := cset_net s.bsi var inp, nl)
    od) /\
 (compile_stmt s (BlockingAssign (Indexing var _ (Const v)) (SOME e)) = do
  (s, nl, inp) <- compile_exp s e;
  i <- ver2n v;
  (let (s, tmpvar) = compile_new_name s;
       newcell = CellArrayWrite tmpvar (cget_net s.bsi var) i inp in
   return (s with bsi := cset_net s.bsi var (VarInp (NetVar tmpvar) NoIndexing), SNOC newcell nl))
 od) /\

 (compile_stmt s (NonBlockingAssign (NoIndexing var) e) =
  case e of
    NONE =>
     let (s, n) = compile_new_name s in (do
      t <- decls_type s.vertypes var;
      return (s with nbsi := cset_net s.nbsi var (VarInp (NetVar n) NoIndexing), [NDetCell n (compile_type t)])
     od)
  | SOME e => do
     (s, nl, inp) <- compile_exp s e;
     return (s with nbsi := cset_net s.nbsi var inp, nl)
    od) /\
 (compile_stmt s (NonBlockingAssign (Indexing var _ (Const v)) (SOME e)) = do
  (s, nl, inp) <- compile_exp s e;
  i <- ver2n v;
  (let (s, tmpvar) = compile_new_name s;
       newcell = CellArrayWrite tmpvar (cget_net s.nbsi var) i inp in
   return (s with nbsi := cset_net s.nbsi var (VarInp (NetVar tmpvar) NoIndexing), SNOC newcell nl))
 od) /\

 (compile_stmt _ _ = INL TypeError)`;

val compile_stmts_def = Define `
 (compile_stmts s [] = INR (s, [])) /\
 (compile_stmts s (p::ps) = do
  (s, nl) <- compile_stmt s p;
  (s, nl') <- compile_stmts s ps;
  return (s, nl ++ nl')
 od)`;

(* TODO: Rename to _fextty *)
Definition compile_fextenv_def:
 compile_fextenv fextenv = MAP (λ(var, t). (var, compile_type t)) fextenv
End

Definition compile_outs_def:
 compile_outs decls =
  MAP (λ(var, data). (var, OutInp $ VarInp (RegVar var 0) NoIndexing)) (FILTER (λ(var, data). data.output) decls)
End

Definition compile_reg_def:
 compile_reg combs_bsi ffs_bsi ffs_nbsi pseudos (var, data) = let
  ty = compile_type data.type;
  v = OPTION_MAP compile_value data.init;
  is_pseudo = member string_cmp var pseudos;
  inp = if is_pseudo then
         cget_net_var combs_bsi var
        else
         case cget_net_var ffs_nbsi var of
           SOME inp => SOME inp
         | NONE => cget_net_var ffs_bsi var in
   ((var, 0), <| type := ty; reg_type := if is_pseudo then PseudoReg else Reg; init := v; inp := inp |>)
End

Definition compile_regs_def:
 compile_regs (pseudos : (string, unit) balanced_map) combs_bsi ffs_bsi ffs_nbsi decls =
 MAP (compile_reg combs_bsi ffs_bsi ffs_nbsi pseudos) decls
End

Definition compile_def:
 compile pseudos m = do
  s <<- <| bsi := [empty]; nbsi := [empty]; vertypes := m.decls; tmpnum := 0 |>;
  (s_combs, nl_combs) <- compile_stmts s m.combs;

  s <<- s_combs with <| bsi := [empty]; nbsi := [empty] |>;
  (s, nl_ffs) <- compile_stmts s m.ffs;

  fextty <<- compile_fextenv m.fextty;
  outs <<- compile_outs m.decls;
  decls <<- compile_regs pseudos s_combs.bsi s.bsi s.nbsi m.decls;

  return (Circuit fextty outs decls nl_combs nl_ffs, s.tmpnum)
 od
End

val _ = export_theory ();
