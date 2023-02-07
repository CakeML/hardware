open hardwarePreamble;

open bitstringTheory alistTheory;

open verilogTheory verilogMetaTheory verilogTypeTheory sumExtraTheory;

val _ = new_theory "verilogTypeChecker";

infix THEN2;

(** Type utils **)

val assert_type_def = Define `
 assert_type t1 t2 = if t1 = t2 then INR () else INL $ TypeErrorMsg "assert_type: types not equal"`;

val assert_array_type_def = Define ‘
 (assert_array_type VBool_t = INL $ TypeErrorMsg "assert_array_type: expected array type") /\
 (assert_array_type (VArray_t n) = INR ())’;

Theorem assert_array_type_INR:
 !t. assert_array_type t = INR () <=> ?l. t = VArray_t l
Proof
 Cases \\ rw [assert_array_type_def]
QED

val array_type_length_def = Define `
 (array_type_length VBool_t = INL $ TypeErrorMsg "array_type_length: expected array type") /\
 (array_type_length (VArray_t l) = INR l)`;

Theorem array_type_length_INR:
 !t l. array_type_length t = INR l <=> t = VArray_t l
Proof
 Cases \\ rw [array_type_length_def]
QED

Definition sum_the_def:
 (sum_the NONE = INL $ TypeErrorMsg "sum_the: expected value, got NONE") /\
 (sum_the (SOME x) = INR x)
End

Theorem sum_the_INR:
 !x x'. sum_the x = INR x' <=> x = SOME x'
Proof
 Cases \\ rw [sum_the_def]
QED

(** Values **)

(* No longer needs to return a sum value *)
val infer_val_def = Define `
 (infer_val (VBool _) = INR VBool_t) /\
 (infer_val (VArray l) = INR (VArray_t (LENGTH l)))`;

Theorem infer_val_INR:
 !v t. infer_val v = (INR t : error + vertype) <=> vertype_v v t
Proof
 Cases \\ rw [vertype_v_cases, infer_val_def] \\ eq_tac \\ simp []
QED

(*Theorem infer_val_correct:
 !v. vertype_v v (infer_val v)
Proof
 rw [infer_val_INR]
QED*)

(** Expressions **)

Definition infer_var_def:
 (infer_var extenv env (Var var) = sum_alookup env var) ∧
 (infer_var extenv env (InputVar var) = sum_alookup extenv var) ∧
 (infer_var extenv env _ = INL $ TypeErrorMsg "infer_var: expected variable, found non-variable")
End

Definition infer_exp_def:
 (infer_exp extenv env (Const v) = do
  t <- infer_val v;
  return (Const v, t)
 od) /\

 (infer_exp extenv env (Var var) = do
  t <- sum_alookup env var;
  return (Var var, t)
 od) /\

 (infer_exp extenv env (InputVar var) = do
  t <- sum_alookup extenv var;
  return (InputVar var, t)
 od) /\

 (infer_exp extenv env (ArrayIndex var _ i) = do
  var_t <- infer_var extenv env var;
  assert_array_type var_t;
  (i, i_t) <- infer_exp extenv env i;
  i_t_len <- array_type_length i_t;
  return (ArrayIndex var i_t_len i, VBool_t)
 od) /\

 (infer_exp extenv env (ArraySlice var i1 i2) = do
  var_t <- infer_var extenv env var;
  var_t_len <- array_type_length var_t;
  sum_check (i1 < var_t_len) TypeError;
  sum_check (i2 ≤ i1) TypeError;
  return (ArraySlice var i1 i2, VArray_t (i1 - i2 + 1))
 od) /\

 (infer_exp extenv env (BUOp Not e) = do
  (e, e_t) <- infer_exp extenv env e;
  assert_type e_t VBool_t;
  return (BUOp Not e, VBool_t)
 od) /\

 (infer_exp extenv env (BBOp e1 bbop e2) = do
  (e1, e1_t) <- infer_exp extenv env e1;
  assert_type e1_t VBool_t;
  (e2, e2_t) <- infer_exp extenv env e2;
  assert_type e2_t VBool_t;
  return (BBOp e1 bbop e2, VBool_t)
 od) /\

 (infer_exp extenv env (Arith e1 Plus e2) = do
  (e1, e1_t) <- infer_exp extenv env e1;
  e1_t_len <- array_type_length e1_t;
  (e2, e2_t) <- infer_exp extenv env e2;
  e2_t_len <- array_type_length e2_t;
  sum_check (e1_t_len = e2_t_len) (TypeErrorMsg "infer_exp: Addition operands different lengths");
  return (Arith e1 Plus e2, VArray_t e1_t_len)
 od) /\

 (infer_exp extenv env (Cmp e1 ArrayEqual e2) = do
  (e1, e1_t) <- infer_exp extenv env e1;
  e1_t_len <- array_type_length e1_t;
  (e2, e2_t) <- infer_exp extenv env e2;
  e2_t_len <- array_type_length e2_t;
  sum_check (e1_t_len = e2_t_len) (TypeErrorMsg "infer_exp: Array eq. operands different lengths");
  return (Cmp e1 ArrayEqual e2, VBool_t)
 od) /\

 (infer_exp extenv env _ = INL $ TypeErrorMsg "infer_exp: Non-supported operator")
End

Theorem infer_exp_sound:
 !extenv env e e' t.
 infer_exp extenv env e = INR (e', t) ==>
 vertype_exp extenv (alist_to_map env) e' t ∧
 (∀fext s. erun fext s e' = erun fext s e)
Proof
 recInduct (theorem "infer_exp_ind") \\ simp [infer_exp_def, sum_bind_INR] \\
 rpt conj_tac \\ rpt strip_tac'
 >- fs [Once vertype_exp_cases, infer_val_INR]
 >- fs [Once vertype_exp_cases, alist_to_map_alookup, sum_alookup_INR]
 >- fs [Once vertype_exp_cases, sum_alookup_INR]
 >- (Cases_on ‘var’ \\ fs [infer_var_def] \\
     pairarg_tac \\ fs [sum_bind_INR] \\ rveq \\ simp [Once vertype_exp_cases] \\
     fs [assert_array_type_INR, array_type_length_INR, alist_to_map_alookup, sum_alookup_INR, erun_def])
 >- (Cases_on ‘var’ \\ fs [infer_var_def] \\
     fs [sum_alookup_INR, array_type_length_INR, sum_check_INR] \\
     rw [Once vertype_exp_cases, alist_to_map_alookup])
 >- (rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\ simp [Once vertype_exp_cases] \\
     fs [assert_type_def, erun_def] \\ rpt asm_exists_tac)
 >- (rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\ simp [Once vertype_exp_cases] \\
     fs [assert_type_def, erun_def])
 >- (rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\ simp [Once vertype_exp_cases] \\
     fs [array_type_length_INR, sum_check_INR, erun_def])
 >- (rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\ simp [Once vertype_exp_cases] \\
     fs [array_type_length_INR, sum_check_INR, erun_def] \\ asm_exists_tac \\ simp [])
QED

Theorem infer_exp_complete:
 !extenv env e t.
 vertype_exp extenv (alist_to_map env) e t ==> infer_exp extenv env e = INR (e, t)
Proof
 ntac 2 gen_tac \\ ho_match_mp_tac vertype_exp_ind \\ rw [infer_exp_def, sum_bind_INR]
 >- simp [infer_val_INR]
 >- fs [alist_to_map_alookup, sum_alookup_INR]
 >- fs [sum_alookup_INR]
 THEN2 fs [alist_to_map_alookup, sum_alookup_INR, assert_array_type_def, array_type_length_def, infer_var_def]
 THEN2 fs [alist_to_map_alookup, sum_alookup_INR, array_type_length_def, sum_check_def, infer_var_def]
 THEN2 simp [assert_type_def]
 THEN2 simp [array_type_length_def, sum_check_def]
QED

val check_exp_def = Define `
 check_exp extenv env t e = do
  (e, e_t) <- infer_exp extenv env e;
  if e_t = t then return e else INL $ TypeErrorMsg "check_exp: inferred unexpected type"
 od`;

Theorem check_exp_sound:
 !extenv env t e e'.
  check_exp extenv env t e = INR e' ==>
  vertype_exp extenv (alist_to_map env) e' t ∧
  (∀fext s. erun fext s e' = erun fext s e)
Proof
 simp [check_exp_def, sum_bind_INR] \\ rpt strip_tac' \\ pairarg_tac \\ fs [] \\ rveq \\
 drule_strip infer_exp_sound \\ simp []
QED

Theorem check_exp_complete:
 !extenv env e t. vertype_exp extenv (alist_to_map env) e t ==> check_exp extenv env t e = INR e
Proof
 rw [check_exp_def] \\ drule_strip infer_exp_complete \\ simp [sum_bind_def]
QED

(** Statements **)

Definition check_stmt_def:
 (check_stmt extenv env Skip = return Skip) /\

 (check_stmt extenv env (Seq p1 p2) = do
   p1 <- check_stmt extenv env p1;
   p2 <- check_stmt extenv env p2;
   return (Seq p1 p2)
 od) /\

 (check_stmt extenv env (IfElse c pt pf) = do
   c <- check_exp extenv env VBool_t c;
   pt <- check_stmt extenv env pt;
   pf <- check_stmt extenv env pf;
   return (IfElse c pt pf)
  od) /\

 (check_stmt extenv env (Case _ c cases dcase) = do
  (c, ct) <- infer_exp extenv env c;
  cases <- sum_mapM (λ(e, p). do
                               e <- check_exp extenv env ct e;
                               p <- check_stmt extenv env p;
                               return (e, p)
                              od) cases;
  dcase <- sum_option_map (check_stmt extenv env) dcase;
  return (Case ct c cases dcase)
 od) ∧

 (check_stmt extenv env (BlockingAssign (NoIndexing var) rhs) = do
   var_t <- sum_alookup env var;
   rhs <- sum_option_map (check_exp extenv env var_t) rhs;
   return (BlockingAssign (NoIndexing var) rhs)
  od) /\
 (check_stmt extenv env (BlockingAssign (Indexing var _ i) rhs) = do
   var_t <- sum_alookup env var;
   assert_array_type var_t;
   (i, i_t) <- infer_exp extenv env i;
   i_t_len <- array_type_length i_t;
   rhs <- sum_the rhs;
   rhs <- check_exp extenv env VBool_t rhs;
   return (BlockingAssign (Indexing var i_t_len i) (SOME rhs))
  od) /\
 (check_stmt extenv env (BlockingAssign _ rhs) = INL $ TypeErrorMsg "Bad blocking assignment") /\

 (check_stmt extenv env (NonBlockingAssign (NoIndexing var) rhs) = do
   var_t <- sum_alookup env var;
   rhs <- sum_option_map (check_exp extenv env var_t) rhs;
   return (NonBlockingAssign (NoIndexing var) rhs)
  od) /\
 (check_stmt extenv env (NonBlockingAssign (Indexing var _ i) rhs) = do
   var_t <- sum_alookup env var;
   assert_array_type var_t;
   (i, i_t) <- infer_exp extenv env i;
   i_t_len <- array_type_length i_t;
   rhs <- sum_the rhs;
   rhs <- check_exp extenv env VBool_t rhs;
   return (NonBlockingAssign (Indexing var i_t_len i) (SOME rhs))
  od) /\
 (check_stmt extenv env (NonBlockingAssign _ rhs) = INL $ TypeErrorMsg "Bad non-blocking assignment")
Termination
 WF_REL_TAC `measure (vprog_size o (λ(_, _, p). p))` \\ rw [] \\
 drule MEM_IMP_vprog_size \\ DECIDE_TAC
End

Triviality EL_MEM:
 ∀l x n. n < LENGTH l ∧ EL n l = x ⇒ MEM x l
Proof
 metis_tac [MEM_EL]
QED

Triviality check_stmt_writes_Case_lem:
 ∀extenv env ct cases cases'.
 (∀e p. MEM (e,p) cases ⇒ ∀p'. check_stmt extenv env p = INR p' ⇒
                               vwrites p' = vwrites p ∧ vnwrites p' = vnwrites p) ∧
 sum_mapM (λ(e,p).
             do
             e <- check_exp extenv env ct e;
             p <- check_stmt extenv env p;
             INR (e,p)
             od) cases = INR cases' ⇒
 MAP (λ(_,cb). vwrites cb) cases' = MAP (λ(_,cb). vwrites cb) cases ∧
 MAP (λ(_,cb). vnwrites cb) cases' = MAP (λ(_,cb). vnwrites cb) cases
Proof
 ntac 3 gen_tac \\ Induct >- simp [sum_mapM_def] \\
 PairCases \\ Cases \\ simp [sum_mapM_INR, sum_bind_INR] \\ strip_tac \\ rveq \\ simp [] \\
 first_x_assum match_mp_tac \\ metis_tac []
QED

Theorem check_stmt_writes:
 !extenv env p p'.
 check_stmt extenv env p = INR p' ==>
 vwrites p' = vwrites p ∧ vnwrites p' = vnwrites p
Proof
 recInduct check_stmt_ind \\ simp [check_stmt_def, sum_bind_INR] \\ rpt conj_tac \\ rpt strip_tac'
 >- (rpt drule_first \\ rveq \\ simp [vwrites_def, vnwrites_def])
 >- (rpt drule_first \\ rveq \\ simp [vwrites_def, vnwrites_def])
 >- (pairarg_tac \\ fs [sum_bind_INR] \\ rveq \\
     drule_strip check_stmt_writes_Case_lem \\
     Cases_on ‘dcase’ \\ fs [sum_option_map_INR, vwrites_def, vnwrites_def])
 >- rw [vwrites_def, vnwrites_def]
 >- (pairarg_tac \\ fs [sum_bind_INR] \\ rw [vwrites_def, vnwrites_def, evwrites_def])
 >- rw [vwrites_def, vnwrites_def]
 >- (pairarg_tac \\ fs [sum_bind_INR] \\ rw [vwrites_def, vnwrites_def, evwrites_def])
QED

Theorem check_stmt_sound:
 !extenv env p p'.
 check_stmt extenv env p = INR p' ==>
 vertype_stmt extenv (alist_to_map env) p' ∧
 (∀fext s. prun fext s p' = prun fext s p)
Proof
 recInduct check_stmt_ind \\ simp [check_stmt_def, sum_bind_INR] \\ rpt conj_tac \\ rpt strip_tac'
 >- simp [Once vertype_stmt_cases]
 >- (rpt drule_first \\ rveq \\ simp [Once vertype_stmt_cases, prun_def])
 >- (rpt drule_first \\ rveq \\ drule_strip check_exp_sound \\ simp [Once vertype_stmt_cases, prun_def])
 >- (pairarg_tac \\ rveq \\ drule_strip infer_exp_sound \\ fs [sum_bind_INR] \\ rveq \\
    simp [Once vertype_stmt_cases, EVERY_MEM, PULL_EXISTS] \\ rpt strip_tac
    >- (drule_strip sum_mapM_MEM \\ Cases_on ‘y’ \\ fs [sum_bind_INR] \\ rveq \\ drule_first \\
        simp [] \\ drule_strip check_exp_sound)
    >- fs [sum_option_map_INR]
    \\ match_mp_tac prun_Case_cong \\ rpt conj_tac \\ rpt strip_tac'
       >- simp []
       >- drule_strip length_sum_mapM
       >- (drule_strip EL_MEM \\ fs [sum_mapM_EL] \\ drule_first \\ rfs [sum_bind_INR] \\
          drule_first \\ drule_strip check_exp_sound \\ simp [])
       >- fs [sum_option_map_INR]
       >- fs [sum_option_map_INR])
 >- (fs [sum_option_map_INR] \\ rveq \\ TRY (drule_strip check_exp_sound) \\
     simp [prun_def, prun_assn_rhs_def] \\
     fs [Once vertype_stmt_cases, alist_to_map_alookup, sum_alookup_INR])
 >- (pairarg_tac \\
    fs [sum_bind_INR, assert_array_type_INR, array_type_length_INR, sum_the_INR, sum_alookup_INR] \\
    rveq \\ drule_strip infer_exp_sound \\ drule_strip check_exp_sound \\
    simp [prun_def, prun_assn_rhs_def, prun_bassn_def, assn_def] \\
    simp [Once vertype_stmt_cases, alist_to_map_alookup])
 (* Same as the above two, but for non-blocking this time: *)
 >- (fs [sum_option_map_INR] \\ rveq \\ TRY (drule_strip check_exp_sound) \\
     simp [prun_def, prun_assn_rhs_def] \\
     fs [Once vertype_stmt_cases, alist_to_map_alookup, sum_alookup_INR])
 \\ (pairarg_tac \\
    fs [sum_bind_INR, assert_array_type_INR, array_type_length_INR, sum_the_INR, sum_alookup_INR] \\
    rveq \\ drule_strip infer_exp_sound \\ drule_strip check_exp_sound \\
    simp [prun_def, prun_assn_rhs_def, prun_nbassn_def, assn_def] \\
    simp [Once vertype_stmt_cases, alist_to_map_alookup])
QED

Theorem check_stmt_complete:
 ∀extenv env p. vertype_stmt extenv (alist_to_map env) p ⇒ check_stmt extenv env p = INR p
Proof
 ntac 2 gen_tac \\ ho_match_mp_tac vertype_stmt_ind \\ rw [check_stmt_def, sum_bind_INR]
 >- drule_strip check_exp_complete
 >- (drule_strip infer_exp_complete \\ rw [sum_bind_INR]
    >- (Induct_on ‘cases’ \\ rw [sum_mapM_INR] \\ pairarg_tac \\ fs [sum_bind_INR] \\
       drule_strip check_exp_complete)
    \\ Cases_on ‘d’ \\ fs [sum_option_map_def, sum_map_def])
 >- fs [alist_to_map_alookup, sum_alookup_INR, sum_option_map_def]
 >- (drule_strip check_exp_complete \\
     fs [alist_to_map_alookup, sum_alookup_INR, sum_option_map_def, sum_map_def])
 >- (fs [alist_to_map_alookup, sum_alookup_INR, assert_array_type_def] \\
    imp_res_tac infer_exp_complete \\
    simp [array_type_length_def, sum_bind_def, sum_the_def] \\
    drule_strip check_exp_complete \\
    simp [sum_bind_def])
 (* Again duplication for non-blocking cases: *)
 >- fs [alist_to_map_alookup, sum_alookup_INR, sum_option_map_def]
 >- (drule_strip check_exp_complete \\
     fs [alist_to_map_alookup, sum_alookup_INR, sum_option_map_def, sum_map_def])
 \\ fs [alist_to_map_alookup, sum_alookup_INR, assert_array_type_def] \\
    imp_res_tac infer_exp_complete \\
    simp [array_type_length_def, sum_bind_def, sum_the_def] \\
    drule_strip check_exp_complete \\
    simp [sum_bind_def]
QED

(** Modules **)

(*Definition assert_vertype_ok_def:
 (assert_vertype_ok VBool_t = INR ()) /\
 (assert_vertype_ok (VArray_t len) = if len = 0 then INL TypeError else INR ())
End

Theorem assert_vertype_ok_INR:
 !t. assert_vertype_ok t = INR () <=> vertype_ok t
Proof
 Cases \\ rw [assert_vertype_ok_def, vertype_ok_cases]
QED*)

Definition check_decls_def:
 (check_decls env [] = INR env) /\
 (check_decls env ((var, data) :: decls) =
  case ALOOKUP env var of
    SOME _ => INL $ TypeErrorMsg "check_decls: Duplicate variables"
  | NONE =>
     case data.init of
       NONE => check_decls (SNOC (var, data.type) env) decls
     | SOME v => do
                  vty <- infer_val v;
                  if data.type = vty then
                    check_decls (SNOC (var, data.type) env) decls
                   else
                    INL $ TypeErrorMsg "check_decls: bad init value"
                 od)
End

Theorem check_decls_sound:
 !decls env env'.
 check_decls env decls = INR env' /\
 ALL_DISTINCT (MAP FST env) ==>
 env' = env ++ (MAP (λ(var, data). (var, data.type)) decls) /\
 ALL_DISTINCT (MAP FST env') /\
 EVERY (λ(var,data). OPTION_ALL (λv. vertype_v v data.type) data.init) decls
Proof
 Induct \\ TRY PairCases \\ simp [check_decls_def] \\
 rpt gen_tac \\ every_case_tac \\ simp [sum_bind_INR] \\ rpt strip_tac' \\
 every_case_tac \\ fs [] \\
 drule_first \\ (impl_tac >- fs [SNOC_APPEND, ALL_DISTINCT_APPEND, ALOOKUP_NONE]) \\ strip_tac \\
 fs [infer_val_INR]
QED

(* This proof is very ugly for some reason? *)
(*Theorem check_decls_complete:
 !decls env.
 EVERY (λ(t,var,v). OPTION_ALL (λv. vertype_v v t) v) decls ∧
 ALL_DISTINCT (MAP (λ(t, var, v). var) decls) ∧
 (∀var t. ALOOKUP env var = SOME t ⇒ ALOOKUP (MAP (λ(ty,var,v). (var,ty)) decls) var = NONE) ⇒
 ∃env'. check_decls env decls = INR env'
Proof
 Induct \\ TRY PairCases \\ rw [check_decls_def] \\ every_case_tac \\ fs []
 >- (first_x_assum match_mp_tac \\ simp [SNOC_APPEND, ALOOKUP_APPEND] \\
    rpt gen_tac \\ rpt TOP_CASE_TAC \\ fs []
    >- (simp [GSYM not_MEM_decls_ALOOKUP_NONE])
    \\ drule_first \\ every_case_tac \\ fs [])
 >- (drule_first \\ every_case_tac \\ fs [])
 >- (fs [GSYM infer_val_INR, sum_bind_def] \\ first_x_assum match_mp_tac \\
    rw [SNOC_APPEND, ALOOKUP_APPEND]
    >- rfs [not_MEM_decls_ALOOKUP_NONE]
    \\ fs [CaseEq"option"] \\ drule_first \\ rfs [])
 \\ drule_first \\ fs []
QED*)

Definition typecheck_def:
 typecheck m = do
  (* A little overkill to build a new decls -- called env here -- after decls representation changed *)
  env <- check_decls [] m.decls;
  ffs <- sum_mapM (check_stmt m.fextty env) m.ffs;
  combs <- sum_mapM (check_stmt m.fextty env) m.combs;
  return $ m with <| ffs := ffs; combs := combs |>
 od
End

Theorem sum_mapM_check_stmt_sound:
 !ps ps' extenv env.
 sum_mapM (check_stmt extenv env) ps = INR ps' ==>
 EVERY (vertype_stmt extenv (alist_to_map env)) ps' ∧
 (∀i. i < LENGTH ps ⇒ ∀fext s. prun fext s (EL i ps') = prun fext s (EL i ps))
Proof
 rw [EVERY_EL, sum_mapM_EL] \\ drule_first \\ drule_strip check_stmt_sound \\ simp []
QED

Triviality FST_as_lambda:
 FST = λ(p1, p2). p1
Proof
 rw [FUN_EQ_THM] \\ pairarg_tac \\ rw []
QED

Theorem typecheck_sound:
 !m m'.
  typecheck m = INR m' ==>
  m'.fextty = m.fextty /\ m'.decls = m.decls /\
  vertype_prog m' /\
  (!fext fbits n. run fext fbits m' n = run fext fbits m n)
Proof
 simp [typecheck_def, sum_bind_INR] \\ rpt strip_tac' \\ rveq \\
 imp_res_tac sum_mapM_check_stmt_sound \\
 drule_strip check_decls_sound \\ impl_tac >- simp [] \\ strip_tac \\ rveq \\ fs [] \\ conj_tac
 >- (simp [vertype_prog_def] \\ rpt conj_tac
     >- fs [MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD, FST_as_lambda]
     \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rpt strip_tac \\
        irule vertype_stmt_cong \\ asm_exists_any_tac \\ simp [Ev_from_decls_def])
 \\ rw [run_def] \\ pairarg_tac \\ simp [] \\ match_mp_tac mrun_cong \\
    imp_res_tac length_sum_mapM \\ simp [LIST_REL_EL_EQN]
QED

(*Theorem sum_mapM_check_stmt_complete:
 !ps extenv env.
 EVERY (vertype_stmt extenv (alist_to_map env)) ps ⇒ sum_mapM (check_stmt extenv env) ps = INR ps
Proof
 rw [EVERY_EL, sum_mapM_EL] \\ drule_first \\ drule_strip check_stmt_complete
QED

Theorem typecheck_complete:
 ∀m. vertype_prog (K NONE) m ⇒ typecheck m = INR m
Proof
 Cases \\ rw [typecheck_def] \\
 drule_strip vertype_prog_decls_all_distinct \\
 drule_strip vertype_prog_decls_wt \\
 drule_strip check_decls_complete \\ disch_then (qspec_then ‘[]’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
 simp [sum_bind_def] \\
 drule_strip check_decls_sound \\ simp [] \\ strip_tac \\ rveq \\
 drule_strip vertype_prog_consume_decls \\ fs [Ev_from_decls_def, update_append_K_NONE] \\ drule_first \\
 qpat_x_assum ‘vertype_prog _ (Module _ [] _)’ (assume_tac o SIMP_RULE (srw_ss()) [Once vertype_prog_cases]) \\
 drule_strip sum_mapM_check_stmt_complete \\
 simp [sum_bind_def]
QED*)

(* Other properties *)

Theorem sum_mapM_check_stmt_writes:
 ∀extenv env ps ps'.
 sum_mapM (check_stmt extenv env) ps = INR ps' ⇒
 MAP vwrites ps' = MAP vwrites ps ∧
 MAP vnwrites ps' = MAP vnwrites ps
Proof
 ntac 2 gen_tac \\ Induct \\ simp [sum_mapM_INR] \\ rpt strip_tac' \\
 drule_strip check_stmt_writes \\ simp []
QED

Theorem typecheck_module_ok:
 ∀m m'. typecheck m = INR m' ∧ module_ok m ⇒ module_ok m'
Proof
 simp [typecheck_def, module_ok_def, writes_overlap_ok_def, writes_ok_def, sum_bind_INR] \\ rpt strip_tac' \\
 imp_res_tac sum_mapM_check_stmt_writes \\ rw []
QED

Theorem typecheck_vwrites_comb:
 ∀m m'. typecheck m = INR m' ⇒
 ∀var. MEM var (FLAT (MAP vwrites m'.combs)) ⇔ MEM var (FLAT (MAP vwrites m.combs))
Proof
 rw [typecheck_def, sum_bind_INR] \\ imp_res_tac sum_mapM_check_stmt_writes \\ rw []
QED

val _ = export_theory ();
