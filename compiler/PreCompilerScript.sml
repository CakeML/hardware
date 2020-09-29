open hardwarePreamble;

open sumExtraTheory verilogTheory verilogTypeTheory;

val _ = new_theory "PreCompiler";

(** Preprocessing compiler: Verilog to Verilog transformations to make the Verilog to RTL transformation simpler **)

(* Temporary names handling *)

val tmpvar_def = Define ‘
 tmpvar n = "tmpvar" ++ toString n’;

Definition is_tmpvar_def:
 is_tmpvar var ⇔ "tmpvar" ≼ var
End

val not_tmpvar_decl_def = Define ‘
 not_tmpvar_decl (ty, var, v) = ~(is_tmpvar var)’;

val tmpvar_check_def = Define ‘
 tmpvar_check (Module _ decls _) = EVERY not_tmpvar_decl decls’;

Definition fresh_tmpvar_list_def:
 fresh_tmpvar_list tmpnum l = !n. tmpnum <= n ==> sum_alookup l (tmpvar n) = INL UnknownVariable
End

Definition fresh_tmpvar_decls_def:
 fresh_tmpvar_decls tmpnum decls = !n. tmpnum <= n ==> decls_type decls (tmpvar n) = INL UnknownVariable
End

Definition tmpvars_range_def:
 tmpvars_range (l:num) h tmps ⇔ EVERY (λ(i, t). l ≤ i ∧ i < h) tmps
End

Theorem tmpvars_range_nil[simp]:
 ∀l h. tmpvars_range l h []
Proof
 simp [tmpvars_range_def]
QED

Definition tmpvars_extend_def:
 tmpvars_extend tmps1 tmps2 = ∀var t. sum_alookup tmps2 var = INR t ⇒ sum_alookup tmps1 var = INR t
End

Definition tmpvars_distinct_def:
 tmpvars_distinct tmps = ALL_DISTINCT (MAP FST tmps)
End

Theorem tmpvars_distinct_nil[simp]:
 tmpvars_distinct []
Proof
 simp [tmpvars_distinct_def]
QED

(* Fill with Fs instead of NONE here to keep fbits in sync, will anyway be filled with Fs later *)
Definition tmpvardecls_def:
 tmpvardecls tmps = MAP (λ(i, t). (t, tmpvar i, SOME $ build_zero t)) tmps
End

Definition tmpvardecls_env_def:
 tmpvardecls_env tmps = MAP (λ(ty, var, v). (var, ty)) (tmpvardecls tmps)
End

Definition tenv_type_def:
 tenv_type tenv var = case tenv var of SOME t => INR t | NONE => INL UnknownVariable
End

Theorem tenv_type_INR:
 !Ev var t. tenv_type Ev var = INR t <=> Ev var = SOME t
Proof
 rw [tenv_type_def] \\ every_case_tac
QED

(** Preprocess dynamic array read behavior **)

Definition is_ok_idx_const_def:
 (is_ok_idx_const varlen (VArray bs) ⇔ v2n bs < varlen) ∧
 (is_ok_idx_const varlen v ⇔ F)
End

Theorem is_ok_idx_const_inv:
 ∀v len. is_ok_idx_const len v ⇔ ∃bs. v = VArray bs ∧ v2n bs < len
Proof
 Cases \\ simp [is_ok_idx_const_def]
QED

Definition get_arrayindex_var_def:
 (* Partial function! *)
 (get_arrayindex_var (Var var) = var) ∧
 (get_arrayindex_var (InputVar var) = var)
End

Definition compile_array_read_exp_def:
 (compile_array_read_exp tenv tmpnum tmps (ArrayIndex var ilen idx) =
  let varvar = get_arrayindex_var var in
  case decls_type tenv varvar of
    INR (VArray_t varlen) =>
     (case get_const idx of
        INR idx => (tmpnum, tmps, [], if is_ok_idx_const varlen idx then
                                       ArrayIndex var ilen (Const idx)
                                      else
                                       Const (VBool F)) (* <-- will never be executed *)
      | _ => (*let (tmpnum, tmps, newvars, idx) = compile_array_read_exp tenv tmpnum tmps idx in*)
             (* ^-- actually, cannot have nested indexing because of the current limited type system... *)
              (SUC tmpnum, (tmpnum, VBool_t)::tmps,
               [(tmpnum, varlen, varvar, ilen, idx)](*::newvars*), Var (tmpvar tmpnum)))
  | _ => (* ill-typed program: *) (tmpnum, tmps, [], ArrayIndex var ilen idx)) ∧
 (compile_array_read_exp tenv tmpnum tmps (BUOp op e1) =
  let (tmpnum, tmps, newvars, e1) = compile_array_read_exp tenv tmpnum tmps e1 in
   (tmpnum, tmps, newvars, BUOp op e1)) /\
 (compile_array_read_exp tenv tmpnum tmps (BBOp e1 op e2) =
  let (tmpnum, tmps, newvars1, e1) = compile_array_read_exp tenv tmpnum tmps e1;
      (tmpnum, tmps, newvars2, e2) = compile_array_read_exp tenv tmpnum tmps e2 in
   (tmpnum, tmps, newvars1 ++ newvars2, BBOp e1 op e2)) /\
 (compile_array_read_exp tenv tmpnum tmps (Arith e1 op e2) =
  let (tmpnum, tmps, newvars1, e1) = compile_array_read_exp tenv tmpnum tmps e1;
      (tmpnum, tmps, newvars2, e2) = compile_array_read_exp tenv tmpnum tmps e2 in
   (tmpnum, tmps, newvars1 ++ newvars2, Arith e1 op e2)) /\
 (compile_array_read_exp tenv tmpnum tmps (Cmp e1 op e2) =
  let (tmpnum, tmps, newvars1, e1) = compile_array_read_exp tenv tmpnum tmps e1;
      (tmpnum, tmps, newvars2, e2) = compile_array_read_exp tenv tmpnum tmps e2 in
   (tmpnum, tmps, newvars1 ++ newvars2, Cmp e1 op e2)) /\
 (compile_array_read_exp tenv tmpnum tmps e = (tmpnum, tmps, [], e))
End

Definition compile_array_read_exp_opt_def:
 (compile_array_read_exp_opt tenv tmpnum tmps NONE = (tmpnum, tmps, [], NONE)) ∧
 (compile_array_read_exp_opt tenv tmpnum tmps (SOME e) =
  let (tmpnum, tmps, newvars, e) = compile_array_read_exp tenv tmpnum tmps e in
   (tmpnum, tmps, newvars, SOME e))
End

Definition compile_array_read_newvars_def:
 (compile_array_read_newvars tenv [] p = p) ∧
 (compile_array_read_newvars tenv ((tmpnum, varlen, var, ilen, idx)::newvars) p = let
  newvar = tmpvar tmpnum;
  caselen = MIN varlen (2**ilen);
  cases = GENLIST (λi. let i = (Const $ n2VArray ilen i) in
                        (i, BlockingAssign (NoIndexing newvar) (SOME $ ArrayIndex (Var var) ilen i))) caselen in
   Seq (Case (VArray_t ilen) idx cases NONE)
       (compile_array_read_newvars tenv newvars p))
End

Definition compile_array_read_size_def:
 (compile_array_read_size (INL (_, _, _, p)) = vprog_size p) ∧
 (compile_array_read_size (INR (INL (_, _, _, p))) = vprog3_size p) ∧
 (compile_array_read_size (INR (INR (_, _, _, ps))) = vprog1_size ps)
End

Definition compile_array_read_def:
 (compile_array_read tenv tmpnum tmps Skip = (tmpnum, tmps, Skip)) ∧
 (compile_array_read tenv tmpnum tmps (Seq l r) = let
  (tmpnum, tmps, l) = compile_array_read tenv tmpnum tmps l;
  (tmpnum, tmps, r) = compile_array_read tenv tmpnum tmps r in
   (tmpnum, tmps, Seq l r)) ∧
 (compile_array_read tenv tmpnum tmps (IfElse c l r) = let
  (tmpnum, tmps, newvars, c) = compile_array_read_exp tenv tmpnum tmps c;
  (tmpnum, tmps, l) = compile_array_read tenv tmpnum tmps l;
  (tmpnum, tmps, r) = compile_array_read tenv tmpnum tmps r in
   (tmpnum, tmps, compile_array_read_newvars tenv newvars (IfElse c l r))) ∧
 (compile_array_read tenv tmpnum tmps (Case t m cs d) = let
  (tmpnum, tmps, newvars1, m) = compile_array_read_exp tenv tmpnum tmps m;
  (tmpnum, tmps, newvars2, cs) = compile_array_read_case_list tenv tmpnum tmps cs;
  (tmpnum, tmps, d) = compile_array_read_opt tenv tmpnum tmps d in
   (tmpnum, tmps, compile_array_read_newvars tenv newvars2
                   (compile_array_read_newvars tenv newvars1
                    (Case t m cs d)))) ∧
 (compile_array_read tenv tmpnum tmps (BlockingAssign wc rhs) = let
  (tmpnum, tmps, newvars, rhs) = compile_array_read_exp_opt tenv tmpnum tmps rhs in
   (tmpnum, tmps, compile_array_read_newvars tenv newvars (BlockingAssign wc rhs))) ∧
 (compile_array_read tenv tmpnum tmps (NonBlockingAssign wc rhs) = let
  (tmpnum, tmps, newvars, rhs) = compile_array_read_exp_opt tenv tmpnum tmps rhs in
   (tmpnum, tmps, compile_array_read_newvars tenv newvars (NonBlockingAssign wc rhs))) ∧

 (compile_array_read_opt tenv tmpnum tmps NONE = (tmpnum, tmps, NONE)) ∧
 (compile_array_read_opt tenv tmpnum tmps (SOME p) = let
  (tmpnum, tmps, p) = compile_array_read tenv tmpnum tmps p in
   (tmpnum, tmps, SOME p)) ∧

 (compile_array_read_case_list tenv tmpnum tmps [] = (tmpnum, tmps, [], [])) ∧
 (compile_array_read_case_list tenv tmpnum tmps ((e,p)::ps) = let
  (tmpnum, tmps, newvars1, e) = compile_array_read_exp tenv tmpnum tmps e;
  (tmpnum, tmps, p) = compile_array_read tenv tmpnum tmps p;
  (tmpnum, tmps, newvars2, ps) = compile_array_read_case_list tenv tmpnum tmps ps in
   (tmpnum, tmps, newvars1 ++ newvars2, (e, p) :: ps))
Termination
 WF_REL_TAC `measure compile_array_read_size` \\ rw [compile_array_read_size_def, vprog_size_def]
End

Definition compile_array_read_list_def:
 (compile_array_read_list tenv tmpnum tmps [] = (tmpnum, tmps, [])) ∧
 (compile_array_read_list tenv tmpnum tmps (p::ps) = let
  (tmpnum, tmps, p) = compile_array_read tenv tmpnum tmps p;
  (tmpnum, tmps, ps) = compile_array_read_list tenv tmpnum tmps ps in
   (tmpnum, tmps, p::ps))
End

Definition compile_array_read_module_def:
 compile_array_read_module tmpnum (Module extenv decls ps) =
  let (tmpnum, tmps, ps) = compile_array_read_list decls tmpnum [] ps in
  (tmpnum, Module extenv (decls ++ tmpvardecls tmps) ps)
End

Definition no_array_read_dyn_exp_def:
 (no_array_read_dyn_exp tenv (Const _) <=> T) /\
 (no_array_read_dyn_exp tenv (Var _) <=> T) /\
 (no_array_read_dyn_exp tenv (InputVar _) <=> T) /\
 (no_array_read_dyn_exp tenv (ArrayIndex (Var var) ilen i) <=>
  case (do i <- get_const i; i <- ver2n i; t <- tenv_type tenv var; return (i, t) od) of
    INR (i, VArray_t len) => i < len
  | _ => F) /\
 (no_array_read_dyn_exp tenv (BUOp _ e1) <=>
  no_array_read_dyn_exp tenv e1) /\
 (no_array_read_dyn_exp tenv (BBOp e1 _ e2) <=>
  no_array_read_dyn_exp tenv e1 /\ no_array_read_dyn_exp tenv e2) /\
 (no_array_read_dyn_exp tenv (Arith e1 _ e2) <=>
  no_array_read_dyn_exp tenv e1 /\ no_array_read_dyn_exp tenv e2) /\
 (no_array_read_dyn_exp tenv (Cmp e1 _ e2) <=>
  no_array_read_dyn_exp tenv e1 /\ no_array_read_dyn_exp tenv e2) /\
 (no_array_read_dyn_exp tenv _ <=> F)
End

Definition no_array_read_dyn_def:
 (no_array_read_dyn tenv Skip <=> T) /\
 (no_array_read_dyn tenv (Seq p1 p2) <=> no_array_read_dyn tenv p1 /\ no_array_read_dyn tenv p2) /\
 (no_array_read_dyn tenv (IfElse c tb fb) <=>
  no_array_read_dyn_exp tenv c /\ no_array_read_dyn tenv tb /\ no_array_read_dyn tenv fb) /\
 (no_array_read_dyn tenv (Case _ c cases def) <=>
  no_array_read_dyn_exp tenv c /\
  EVERY (λ(c, e). no_array_read_dyn_exp tenv c /\ no_array_read_dyn tenv e) cases /\
  OPTION_ALL (no_array_read_dyn tenv) def) /\
 (no_array_read_dyn tenv (BlockingAssign _ e) <=> OPTION_ALL (no_array_read_dyn_exp tenv) e) /\
 (no_array_read_dyn tenv (NonBlockingAssign _ e) <=> OPTION_ALL (no_array_read_dyn_exp tenv) e)
Termination
 WF_REL_TAC `measure (vprog_size o SND)` \\ rw [MEM_MAP] \\
 drule_strip MEM_IMP_vprog_size \\ DECIDE_TAC
End
 
(** Preprocess dynamic array write behavior **)

Definition compile_array_write_prog_assn_def:
 compile_array_write_prog_assn tmpnum tmps assn lhsvar lhstlen ilen i rhs =
  let newvar = tmpvar tmpnum;
      caselen = MIN lhstlen (2**ilen);
      p = Seq (BlockingAssign (NoIndexing newvar) rhs)
              (Case (VArray_t ilen) i
                    (GENLIST (\i. let i = (Const $ n2VArray ilen i) in
                                   (i, assn (Indexing lhsvar ilen i) (SOME $ Var newvar))) caselen) 
                    NONE) in
  (SUC tmpnum, (tmpnum, VBool_t) :: tmps, p)
End
   
Definition compile_array_write_def:
 (compile_array_write tenv tmpnum tmps (Seq l r) = let
  (tmpnum, tmps, l) = compile_array_write tenv tmpnum tmps l;
  (tmpnum, tmps, r) = compile_array_write tenv tmpnum tmps r in
   (tmpnum, tmps, Seq l r)) ∧
 (compile_array_write tenv tmpnum tmps (IfElse c l r) = let
  (tmpnum, tmps, l) = compile_array_write tenv tmpnum tmps l;
  (tmpnum, tmps, r) = compile_array_write tenv tmpnum tmps r in
   (tmpnum, tmps, IfElse c l r)) ∧
 (compile_array_write tenv tmpnum tmps (Case t m cs d) = let
  (tmpnum, tmps, cs) = compile_array_write_case_list tenv tmpnum tmps cs;
  (tmpnum, tmps, d) = compile_array_write_opt tenv tmpnum tmps d in
   (tmpnum, tmps, Case t m cs d)) ∧
 (compile_array_write tenv tmpnum tmps (BlockingAssign (Indexing var ilen i) rhs) =
  case decls_type tenv var of
    INR (VArray_t varlen) =>
     (case get_const i of
        INR i' => (tmpnum, tmps, if is_ok_idx_const varlen i' then
                                  BlockingAssign (Indexing var ilen i) rhs
                                 else
                                  Skip) (* <-- dead code *)
      | _ => compile_array_write_prog_assn tmpnum tmps BlockingAssign var varlen ilen i rhs)
  | _ => (tmpnum, tmps, Skip) (* <-- ill-typed program *)) ∧
 (compile_array_write tenv tmpnum tmps (NonBlockingAssign (Indexing var ilen i) rhs) =
  case decls_type tenv var of
    INR (VArray_t varlen) =>
     (case get_const i of
        INR i' => (tmpnum, tmps, if is_ok_idx_const varlen i' then
                                  NonBlockingAssign (Indexing var ilen i) rhs
                                 else
                                  Skip) (* <-- dead code *)
      | _ => compile_array_write_prog_assn tmpnum tmps NonBlockingAssign var varlen ilen i rhs)
  | _ => (tmpnum, tmps, Skip) (* <-- ill-typed program *)) ∧
 (compile_array_write tenv tmpnum tmps p = (tmpnum, tmps, p)) ∧

 (compile_array_write_opt tenv tmpnum tmps NONE = (tmpnum, tmps, NONE)) ∧
 (compile_array_write_opt tenv tmpnum tmps (SOME p) = let
  (tmpnum, tmps, p) = compile_array_write tenv tmpnum tmps p in
   (tmpnum, tmps, SOME p)) ∧

 (compile_array_write_case_list tenv tmpnum tmps [] = (tmpnum, tmps, [])) ∧
 (compile_array_write_case_list tenv tmpnum tmps ((e,p)::ps) = let
  (tmpnum, tmps, p) = compile_array_write tenv tmpnum tmps p;
  (tmpnum, tmps, ps) = compile_array_write_case_list tenv tmpnum tmps ps in
   (tmpnum, tmps, (e, p) :: ps))
Termination
 WF_REL_TAC `measure compile_array_read_size` \\ rw [compile_array_read_size_def, vprog_size_def]
End

Definition compile_array_write_list_def:
 (compile_array_write_list tenv tmpnum tmps [] = (tmpnum, tmps, [])) ∧
 (compile_array_write_list tenv tmpnum tmps (p::ps) = let
  (tmpnum, tmps, p) = compile_array_write tenv tmpnum tmps p;
  (tmpnum, tmps, ps) = compile_array_write_list tenv tmpnum tmps ps in
   (tmpnum, tmps, p::ps))
End

Definition compile_array_write_module_def:
 compile_array_write_module tmpnum (Module extenv decls ps) =
  let (tmpnum, tmps, ps) = compile_array_write_list decls tmpnum [] ps in
  (tmpnum, Module extenv (decls ++ tmpvardecls tmps) ps)
End

Definition no_array_write_dyn_def:
 (no_array_write_dyn tenv Skip <=> T) /\
 (no_array_write_dyn tenv (Seq p1 p2) <=> no_array_write_dyn tenv p1 /\ no_array_write_dyn tenv p2) /\
 (no_array_write_dyn tenv (IfElse _ tb fb) <=> no_array_write_dyn tenv tb /\ no_array_write_dyn tenv fb) /\
 (no_array_write_dyn tenv (Case _ _ cases def) <=>
  EVERY (no_array_write_dyn tenv) (MAP SND cases) /\ OPTION_ALL (no_array_write_dyn tenv) def) /\
 (no_array_write_dyn tenv (BlockingAssign (Indexing var len v) _) <=>
  case (do v <- get_const v; v <- ver2n v; t <- tenv_type tenv var; return (v, t) od) of
    INR (v, VArray_t len) => v < len
  | _ => F) /\
 (no_array_write_dyn tenv (BlockingAssign _ _) <=> T) /\
 (no_array_write_dyn tenv (NonBlockingAssign (Indexing var len v) _) <=>
  case (do v <- get_const v; v <- ver2n v; t <- tenv_type tenv var; return (v, t) od) of
    INR (v, VArray_t len) => v < len
  | _ => F) /\
 (no_array_write_dyn tenv (NonBlockingAssign _ _) <=> T)
Termination
 WF_REL_TAC `measure (vprog_size o SND)` \\ rw [MEM_MAP] \\ rename1 ‘MEM p cases’ \\ Cases_on ‘p’ \\
 drule_strip MEM_IMP_vprog_size \\ DECIDE_TAC
End

(** Preprocess away case-statements into if-statements **)

Definition Case_to_IfElse_eq_def:
 (Case_to_IfElse_eq VBool_t lhs rhs = BBOp lhs Equal rhs) ∧
 (Case_to_IfElse_eq (VArray_t _) lhs rhs = Cmp lhs ArrayEqual rhs)
End

Definition Case_to_IfElse_def:
 (Case_to_IfElse ty lhs [] NONE = Skip) /\
 (Case_to_IfElse ty lhs [] (SOME p) = p) /\
 (Case_to_IfElse ty lhs ((e, p) :: xs) def = IfElse (Case_to_IfElse_eq ty lhs e) p (Case_to_IfElse ty lhs xs def))
End

Definition compile_Case_size_def:
 (compile_Case_size (INL (_, _, p)) = vprog_size p) ∧
 (compile_Case_size (INR (INL (_, _, p))) = vprog3_size p) ∧
 (compile_Case_size (INR (INR (_, _, ps))) = vprog1_size ps)
End

Definition compile_Case_def:
 (compile_Case tmpnum tmps (Seq l r) = let
  (tmpnum, tmps, l) = compile_Case tmpnum tmps l;
  (tmpnum, tmps, r) = compile_Case tmpnum tmps r in
   (tmpnum, tmps, Seq l r)) /\
 (compile_Case tmpnum tmps (IfElse c l r) = let
  (tmpnum, tmps, l) = compile_Case tmpnum tmps l;
  (tmpnum, tmps, r) = compile_Case tmpnum tmps r in
   (tmpnum, tmps, IfElse c l r)) /\
 (compile_Case tmpnum tmps (Case t m cs d) =
  if cs = [] then (* this if is actually required, because m is never evaluated when no cases... *)
   (case d of NONE => (tmpnum, tmps, Skip) | SOME d => compile_Case tmpnum tmps d)
  else let
   (tmpnum, tmps, cs) = compile_Case_case_list tmpnum tmps cs;
   (tmpnum, tmps, d) = compile_Case_opt tmpnum tmps d in
    (SUC tmpnum, (tmpnum, t) :: tmps, Seq (BlockingAssign (NoIndexing $ tmpvar tmpnum) (SOME m))
                                          (Case_to_IfElse t (Var $ tmpvar tmpnum) cs d))) ∧
 (compile_Case tmpnum tmps p = (tmpnum, tmps, p)) ∧

 (compile_Case_opt tmpnum tmps NONE = (tmpnum, tmps, NONE)) ∧
 (compile_Case_opt tmpnum tmps (SOME p) = let
  (tmpnum, tmps, p) = compile_Case tmpnum tmps p in
   (tmpnum, tmps, SOME p)) ∧

 (compile_Case_case_list tmpnum tmps [] = (tmpnum, tmps, [])) ∧
 (compile_Case_case_list tmpnum tmps ((e,p)::ps) = let
  (tmpnum, tmps, p) = compile_Case tmpnum tmps p;
  (tmpnum, tmps, ps) = compile_Case_case_list tmpnum tmps ps in
   (tmpnum, tmps, (e, p) :: ps))
Termination
 WF_REL_TAC `measure compile_Case_size` \\ rw [compile_Case_size_def, vprog_size_def]
End

Definition compile_Case_list_def:
 (compile_Case_list tmpnum tmps [] = (tmpnum, tmps, [])) ∧
 (compile_Case_list tmpnum tmps (p::ps) = let
  (tmpnum, tmps, p) = compile_Case tmpnum tmps p;
  (tmpnum, tmps, ps) = compile_Case_list tmpnum tmps ps in
   (tmpnum, tmps, p::ps))
End

Definition compile_Case_module_def:
 compile_Case_module tmpnum (Module extenv decls ps) =
  let (tmpnum, tmps, ps) = compile_Case_list tmpnum [] ps in
   Module extenv (decls ++ tmpvardecls tmps) ps
End

Definition no_Case_def:
 (no_Case (Seq p1 p2) <=> no_Case p1 /\ no_Case p2) /\
 (no_Case (IfElse c pt pf) <=> no_Case pt /\ no_Case pf) /\
 (no_Case (Case _ _ _ _) <=> F) /\
 (no_Case _ <=> T)
End

(** Everything at once **)

Definition preprocess_def:
 preprocess m = do
  sum_check (tmpvar_check m) TypeError; (* Not really a type-error *)
  (tmpnum, m) <<- compile_array_read_module 0 m;
  (tmpnum, m) <<- compile_array_write_module tmpnum m;
  return $ compile_Case_module tmpnum m
 od
End

Definition preprocessed_def:
 preprocessed tenv p <=> no_array_read_dyn tenv p /\ no_array_write_dyn tenv p /\ no_Case p
End

Theorem EVERY_preprocessed:
 !tenv ps.
 EVERY (preprocessed tenv) ps <=> EVERY (no_array_read_dyn tenv) ps /\
                                  EVERY (no_array_write_dyn tenv) ps /\
                                  EVERY no_Case ps
Proof
 simp [EVERY_MEM, preprocessed_def] \\ metis_tac []
QED

Definition preprocessed_module_def:
 preprocessed_module tenv (Module fextenv decls ps) <=> EVERY (preprocessed tenv) ps
End

val _ = export_theory ();
