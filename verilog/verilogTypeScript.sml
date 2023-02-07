open hardwarePreamble;

open bitstringTheory;

open verilogTheory sumExtraTheory;

val _ = new_theory "verilogType";

Inductive vertype_v:
 (vertype_v (VBool v) VBool_t) /\
 (i = LENGTH vs (*/\ i <> 0*) ==> vertype_v (VArray vs) (VArray_t i))
End

val vertype_fext_def = Define `
 vertype_fext extenv fext <=>
 !var t. sum_alookup extenv var = INR t ==> !n. ?v. fext n var = INR v /\ vertype_v v t`;

val vertype_fext_n_def = Define `
 vertype_fext_n extenv fext <=>
 !var t. sum_alookup extenv var = INR t ==> ?v. fext var = INR v /\ vertype_v v t`;

Theorem vertype_fext_vertype_fext_n:
 !extenv fext. vertype_fext extenv fext <=> (!n. vertype_fext_n extenv (fext n))
Proof
 rw [vertype_fext_def, vertype_fext_n_def] \\ eq_tac \\ rw []
QED

(* Soundness of dynamic environment w.r.t. static environment *)
Definition vertype_list_def:
 vertype_list tenv l <=> !var v. ALOOKUP l var = SOME v ==> ?t. tenv var = SOME t /\ vertype_v v t
End

Definition vertype_env_def:
 vertype_env tenv env <=>
 (!var v. get_var env var = INR v ==> ?t. tenv var = SOME t /\ vertype_v v t) /\
 (!var v. get_nbq_var env var = INR v ==> ?t. tenv var = SOME t /\ vertype_v v t)
End

Definition vertype_list_filled_def:
 vertype_list_filled tenv l ⇔
 ∀var t. tenv var = SOME t ⇒ ∃v. ALOOKUP l var = SOME v ∧ vertype_v v t
End

Definition vertype_env_filled_def:
 vertype_env_filled tenv env ⇔
 ∀var t. tenv var = SOME t ⇒ ∃v. get_var env var = INR v ∧ vertype_v v t
End

(* Util thm useful for when you do not want to unfold vertype_env *)
Theorem vertype_env_get_var:
 !env tenv var v.
 get_var env var = INR v /\ vertype_env tenv env ==> 
 ∃t. tenv var = SOME t ∧ vertype_v v t
Proof
 rw [vertype_env_def] \\ drule_first
QED

Theorem vertype_env_get_use_nbq_var:
 !b env tenv var v.
 get_use_nbq_var env b var = INR v /\ vertype_env tenv env ==> 
 ∃t. tenv var = SOME t ∧ vertype_v v t
Proof
 Cases \\ rw [get_use_nbq_var_def, vertype_env_def] \\ every_case_tac \\ drule_first \\ fs [] \\ rfs []
QED

Theorem vertype_env_get_var_type:
 !env tenv var v t. get_var env var = INR v /\ tenv var = SOME t /\ vertype_env tenv env ==> vertype_v v t
Proof
 rw [vertype_env_def] \\ drule_first \\ rfs []
QED

Theorem vertype_env_get_use_nbq_var_type:
 !b env tenv var v t.
 get_use_nbq_var env b var = INR v /\ tenv var = SOME t /\ vertype_env tenv env ==> vertype_v v t
Proof
 rw [get_use_nbq_var_def, vertype_env_def] \\ every_case_tac \\ drule_first \\ rfs []
QED

Inductive vertype_exp:
 (vertype_v v t ==> vertype_exp extenv env (Const v) t) /\

 (env var = SOME t ==> vertype_exp extenv env (Var var) t) /\

 (ALOOKUP extenv var = SOME t ==> vertype_exp extenv env (InputVar var) t) /\

 (env var = SOME (VArray_t l1) /\ vertype_exp extenv env i (VArray_t ilen) ==>
  vertype_exp extenv env (ArrayIndex (Var var) ilen i) VBool_t) /\

 (ALOOKUP extenv var = SOME (VArray_t l1) /\ vertype_exp extenv env i (VArray_t ilen) ==>
  vertype_exp extenv env (ArrayIndex (InputVar var) ilen i) VBool_t) /\

 (env var = SOME (VArray_t l) /\ i1 < l ∧ i2 ≤ i1 ∧ i3 = i1 - i2 + 1 ==>
  vertype_exp extenv env (ArraySlice (Var var) i1 i2) (VArray_t i3)) ∧

 (ALOOKUP extenv var = SOME (VArray_t l) /\ i1 < l ∧ i2 ≤ i1 ∧ i3 = i1 - i2 + 1 ==>
  vertype_exp extenv env (ArraySlice (InputVar var) i1 i2) (VArray_t i3)) ∧

 (vertype_exp extenv env e VBool_t ==>
  vertype_exp extenv env (BUOp Not e) VBool_t) ∧

 (vertype_exp extenv env e1 VBool_t /\ vertype_exp extenv env e2 VBool_t ==>
  vertype_exp extenv env (BBOp e1 bbop e2) VBool_t) ∧

 (vertype_exp extenv env e1 (VArray_t n) /\ vertype_exp extenv env e2 (VArray_t n) ==>
  vertype_exp extenv env (Arith e1 Plus e2) (VArray_t n)) ∧

 (vertype_exp extenv env e1 (VArray_t n) /\ vertype_exp extenv env e2 (VArray_t n) ==>
  vertype_exp extenv env (Cmp e1 ArrayEqual e2) VBool_t)
End

Inductive vertype_stmt:
 (vertype_stmt extenv env Skip) /\

 (vertype_stmt extenv env p1 /\ vertype_stmt extenv env p2 ==>
  vertype_stmt extenv env (Seq p1 p2)) /\

 (vertype_exp extenv env c VBool_t /\ vertype_stmt extenv env pt /\ vertype_stmt extenv env pf ==>
  vertype_stmt extenv env (IfElse c pt pf)) /\

 (vertype_exp extenv env e t /\
  EVERY (λ(e, p). vertype_exp extenv env e t /\ vertype_stmt extenv env p) cases /\
  OPTION_ALL (vertype_stmt extenv env) d ==>
  vertype_stmt extenv env (Case t e cases d)) /\

 (env var = SOME t ==> vertype_stmt extenv env (BlockingAssign (NoIndexing var) NONE)) /\
 (env var = SOME t /\ vertype_exp extenv env e t ==> vertype_stmt extenv env (BlockingAssign (NoIndexing var) (SOME e))) /\
 (* Only include X assignment for non-indexing: *)
 (*(env var = SOME (VArray_t l) /\ vertype_exp extenv env i (VArray_t ilen) ==>
  vertype_stmt extenv env (BlockingAssign (Indexing var ilen i) NONE)) /\*)
 (env var = SOME (VArray_t l) /\ vertype_exp extenv env i (VArray_t ilen) /\ vertype_exp extenv env e VBool_t ==>
  vertype_stmt extenv env (BlockingAssign (Indexing var ilen i) (SOME e))) /\

 (* Note: Same rules as BlockingAssign *)
 (env var = SOME t ==> vertype_stmt extenv env (NonBlockingAssign (NoIndexing var) NONE)) /\
 (env var = SOME t /\ vertype_exp extenv env e t ==> vertype_stmt extenv env (NonBlockingAssign (NoIndexing var) (SOME e))) /\
 (*(env var = SOME (VArray_t l) /\ vertype_exp extenv env i (VArray_t ilen) ==>
  vertype_stmt extenv env (NonBlockingAssign (Indexing var ilen i) NONE)) /\*)
 (env var = SOME (VArray_t l) /\ vertype_exp extenv env i (VArray_t ilen) /\ vertype_exp extenv env e VBool_t ==>
  vertype_stmt extenv env (NonBlockingAssign (Indexing var ilen i) (SOME e)))
End

(*Inductive vertype_prog:
 (env var = NONE /\ vertype_prog ((var =+ SOME ty) env) (Module extenv ds cs ps mem) ==>
  vertype_prog env (Module extenv ((ty, var, Store NONE)::ds) cs ps mem)) /\

 (vertype_v v ty /\ env var = NONE /\ vertype_prog ((var =+ SOME ty) env) (Module extenv ds cs ps mem) ==>
  vertype_prog env (Module extenv ((ty, var, Store (SOME v))::ds) cs ps mem)) /\

 (m.decls = [] ∧ EVERY (vertype_stmt m.fextty env) m.ffs ∧ EVERY (vertype_stmt m.fextty env) m.combs ==>
  vertype_prog env m)
End*)

(** Some vertype_prog properties **)

(* Convert between type env formats *)

val alist_to_map_def = Define `
 alist_to_map x = FOLDR (λ(k,v) f. (k =+ SOME v) f) (K NONE) x`

Theorem alist_to_map_cons:
 !k1 k2 v env. alist_to_map ((k1, v)::env) k2 = if k1 = k2 then SOME v else alist_to_map env k2
Proof
 rw [alist_to_map_def] \\ EVAL_TAC \\ simp []
QED

Theorem alist_to_map_nil:
 alist_to_map [] = K NONE
Proof
 EVAL_TAC
QED

Theorem alist_to_map_alookup:
 !env k. alist_to_map env k = ALOOKUP env k
Proof
 Induct >- simp [alist_to_map_def] \\ Cases \\ simp [alist_to_map_cons]
QED

Theorem alist_to_map_snoc:
 !k v l. ~MEM k (MAP FST l) ==> alist_to_map (SNOC (k, v) l) = (alist_to_map l)⦇k ↦ SOME v⦈
Proof
 rw [FUN_EQ_THM, alist_to_map_alookup, SNOC_APPEND, alistTheory.ALOOKUP_APPEND] \\ rw [] \\ TOP_CASE_TAC \\
 fs [combinTheory.UPDATE_APPLY, alist_to_map_alookup] \\
 drule_strip alistTheory.ALOOKUP_MEM \\ fs [MEM_MAP] \\ first_x_assum (qspec_then ‘(k, x)’ strip_assume_tac) \\ fs []
QED

Definition Ev_from_decls_def:
 Ev_from_decls decls = alist_to_map $ MAP (λ(var, data). (var, data.type)) decls
End

Definition Ev_covers_decls_def:
 Ev_covers_decls Ev decls <=> (!var data. MEM (var, data) decls ==> Ev var = SOME data.type)
End

(* Temporary definition... *)
Definition vertype_prog_def:
 vertype_prog m ⇔
 ALL_DISTINCT (MAP FST m.decls) ∧
 EVERY (λ(var, data). OPTION_ALL (λv. vertype_v v data.type) data.init) m.decls ∧
 EVERY (vertype_stmt m.fextty (Ev_from_decls m.decls)) m.ffs ∧
 EVERY (vertype_stmt m.fextty (Ev_from_decls m.decls)) m.combs
End

Theorem Ev_from_decls_decls_type:
 ∀decls var t. Ev_from_decls decls var = SOME t ⇔ decls_type decls var = INR t
Proof
 rw [Ev_from_decls_def, decls_type_def, alist_to_map_alookup, sum_alookup_INR] \\ TOP_CASE_TAC \\
 simp [alistTheory.ALOOKUP_MAP]
QED

Theorem Ev_from_decls_nil:
 Ev_from_decls [] = K NONE
Proof
 EVAL_TAC
QED

Theorem Ev_from_decls_cons:
 ∀decls var data. Ev_from_decls ((var, data)::decls) = (Ev_from_decls decls)⦇var ↦ SOME data.type⦈
Proof
 rw [Ev_from_decls_def, alist_to_map_def]
QED

Theorem Ev_covers_decls_cons:
 !Ev var data decls.
 Ev_covers_decls Ev ((var, data)::decls) <=> Ev var = SOME data.type /\ Ev_covers_decls Ev decls
Proof
 rw [Ev_covers_decls_def] \\ metis_tac []
QED

Theorem Ev_covers_decls_Ev_from_decls:
 !decls. ALL_DISTINCT (MAP FST decls) ==> Ev_covers_decls (Ev_from_decls decls) decls
Proof
 Induct \\ TRY PairCases \\ fs [Ev_from_decls_def, Ev_covers_decls_def] \\ rpt strip_tac \\ rveq \\
 fs [alist_to_map_cons, MEM_MAP] \\ first_x_assum (qspec_then ‘(var, data)’ strip_assume_tac) \\ gs []
QED

(*Theorem vertype_prog_decls_not_in_env:
 !decls env fextenv cs ps mem var t.
 vertype_prog env (Module fextenv decls cs ps mem) /\ env var = SOME t ==>
 ~MEM var (MAP (λ(t,var,v). var) decls)
Proof
 Induct \\ simp [Once vertype_prog_cases] \\ rpt strip_tac' \\ rveq \\ Cases_on ‘var = var'’ \\ fs [] \\
 first_x_assum match_mp_tac \\ asm_exists_tac \\ simp [combinTheory.APPLY_UPDATE_THM]
QED

Theorem vertype_prog_decls_all_distinct:
 !decls env fextenv cs ps mem.
 vertype_prog env (Module fextenv decls cs ps mem) ==> ALL_DISTINCT (MAP (λ(t, var, v). var) decls)
Proof
 Induct \\ simp [Once vertype_prog_cases] \\ rpt strip_tac' \\ rveq \\ drule_first \\ simp [] \\
 drule_strip vertype_prog_decls_not_in_env \\ simp [combinTheory.APPLY_UPDATE_THM]
QED

Definition var_spec_all_def:
 (var_spec_all P (Store vopt) ⇔ OPTION_ALL P vopt) ∧
 (var_spec_all P NoStore ⇔ T)
End

Triviality vertype_prog_decls_wt_lem:
 ∀env m.
 vertype_prog env m ⇒
 case m of Module extenv decls cs ps mem => EVERY (λ(t,var,v). var_spec_all (λv. vertype_v v t) v) decls
Proof
 ho_match_mp_tac vertype_prog_ind \\ rw [var_spec_all_def]
QED

Theorem vertype_prog_decls_wt:
 ∀env extenv decls cs ps mem.
 vertype_prog env (Module extenv decls cs ps mem) ⇒
 EVERY (λ(t,var,v). var_spec_all (λv. vertype_v v t) v) decls
Proof
 rpt strip_tac \\ drule_strip vertype_prog_decls_wt_lem \\ fs []
QED

Definition update_append_def:
 update_append f g k = case g k of
                         NONE => f k
                       | SOME v => SOME v
End

Theorem update_append_K_NONE:
 (∀f. update_append (K NONE) f = f) ∧ (∀f. update_append f (K NONE) = f)
Proof
 rw [FUN_EQ_THM, update_append_def] \\ CASE_TAC
QED

Theorem not_MEM_decls_ALOOKUP_NONE:
 ∀var decls. ¬MEM var (MAP (λ(t,var,v). var) decls) ⇔ ALOOKUP (MAP (λ(ty,var,v). (var,ty)) decls) var = NONE
Proof
 simp [alistTheory.ALOOKUP_NONE, MAP_MAP_o] \\ rw [MEM_MAP] \\ eq_tac \\ rpt strip_tac \\ pairarg_tac \\
 qexists_tac ‘y’ \\ fs []
QED

Theorem update_append_move_one_to_left:
 ∀decls env var ty.
 ¬MEM var (MAP (λ(t,var,v). var) decls) ⇒
 update_append env (Ev_from_decls decls)⦇var ↦ SOME ty⦈ = update_append env⦇var ↦ SOME ty⦈ (Ev_from_decls decls)
Proof
 rw [Ev_from_decls_def, FUN_EQ_THM, update_append_def, combinTheory.APPLY_UPDATE_THM] \\
 rw [alist_to_map_alookup] \\ fs [not_MEM_decls_ALOOKUP_NONE]
QED
        
Theorem vertype_prog_consume_decls:
 ∀decls extenv cs ps mem env.
 vertype_prog env (Module extenv decls cs ps mem) ⇒
 vertype_prog (update_append env (Ev_from_decls decls)) (Module extenv [] cs ps mem)
Proof
 Induct
 >- simp [Ev_from_decls_def, alist_to_map_nil, update_append_K_NONE]
 \\ PairCases \\ rpt strip_tac' \\ drule_strip vertype_prog_decls_all_distinct \\
    qpat_x_assum ‘vertype_prog _ _’ mp_tac \\
    simp [Once vertype_prog_cases, Ev_from_decls_cons] \\ rpt strip_tac \\
    drule_first \\ fs [update_append_move_one_to_left]
QED

Theorem vertype_prog_consume_decls_K_NONE:
 ∀decls extenv cs ps mem.
 vertype_prog (K NONE) (Module extenv decls cs ps mem) ⇒
 vertype_prog (Ev_from_decls decls) (Module extenv [] cs ps mem)
Proof
 rpt strip_tac \\ drule_strip vertype_prog_consume_decls \\ fs [Ev_from_decls_nil, update_append_K_NONE]
QED

Theorem vertype_prog_decls_cons:
 ∀env extenv t var v decls cs ps mem.
 vertype_prog env (Module extenv ((t,var,v)::decls) cs ps mem) ⇔
 var_spec_all (λv. vertype_v v t) v ∧
 env var = NONE ∧
 vertype_prog env⦇var ↦ SOME t⦈ (Module extenv decls cs ps mem)
Proof
 simp [Once vertype_prog_cases] \\ rpt strip_tac \\ eq_tac \\ strip_tac \\ rveq \\ simp [var_spec_all_def] \\
 Cases_on ‘v’ \\ fs [var_spec_all_def] \\ Cases_on ‘o'’ \\ fs [var_spec_all_def]
QED

Triviality vertype_prog_alt_lem:
 ∀decls extenv cs ps mem env.
 ALL_DISTINCT (MAP (λ(t,var,v). var) decls) ∧
 EVERY (λ(t,var,v). var_spec_all (λv. vertype_v v t) v) decls ∧
 (∀var t. env var = SOME t ⇒ ~MEM var (MAP (λ(t,var,v). var) decls)) ⇒
 vertype_prog env (Module extenv decls cs ps mem) =
 vertype_prog (update_append env (Ev_from_decls decls)) (Module extenv [] cs ps mem)
Proof
 Induct \\ TRY PairCases \\
 simp [Ev_from_decls_nil, update_append_K_NONE, 
       Ev_from_decls_cons, update_append_move_one_to_left, vertype_prog_decls_cons] \\
 rpt strip_tac \\ Cases_on ‘env h1’
 >- (simp [] \\ first_x_assum match_mp_tac \\ rw [combinTheory.APPLY_UPDATE_THM] \\ simp [])
 \\ drule_first \\ fs []
QED

(* Actually usable version of vertype_prog! *)
Theorem vertype_prog_alt:
 ∀extenv decls cs ps mem.
 vertype_prog (K NONE) (Module extenv decls cs ps mem) ⇔
 ALL_DISTINCT (MAP (λ(t,var,v). var) decls) ∧
 EVERY (λ(t,var,v). var_spec_all (λv. vertype_v v t) v) decls ∧
 EVERY (vertype_stmt extenv (Ev_from_decls decls)) cs ∧
 EVERY (vertype_stmt extenv (Ev_from_decls decls)) ps
Proof
 rpt strip_tac \\ eq_tac \\ strip_tac
 >- (drule_strip vertype_prog_decls_all_distinct \\
    drule vertype_prog_consume_decls \\ simp [update_append_K_NONE, Once vertype_prog_cases] \\ strip_tac \\
    drule_strip vertype_prog_decls_wt)
 \\ dep_rewrite.DEP_ONCE_REWRITE_TAC [vertype_prog_alt_lem] \\ simp [update_append_K_NONE] \\
    simp [Once vertype_prog_cases]
QED*)

(** Some properties **)

Theorem vertype_list_nil:
 ∀tenv. vertype_list tenv []
Proof
 simp [vertype_list_def]
QED

Theorem vertype_env_vertype_list:
 !tenv vs. vertype_env tenv vs <=> vertype_list tenv vs.vars /\ vertype_list tenv vs.nbq
Proof
 rw [vertype_env_def, vertype_list_def, get_var_sum_alookup, get_nbq_var_sum_alookup, sum_alookup_INR]
QED

Theorem vertype_env_filled_vertype_list_filled:
 !tenv vs. vertype_env_filled tenv vs ⇔ vertype_list_filled tenv vs.vars
Proof
 rw [vertype_env_filled_def, vertype_list_filled_def, get_var_sum_alookup, sum_alookup_INR]
QED

Theorem vertype_stmt_BlockingAssign_vertype_exp_rhs:
 ∀extenv tenv wc rhs.
 vertype_stmt extenv tenv (BlockingAssign wc rhs) ⇒ ∃t. OPTION_ALL (λe. vertype_exp extenv tenv e t) rhs
Proof
 rw [Once vertype_stmt_cases] \\ simp [] \\ asm_exists_tac
QED

Theorem vertype_stmt_NonBlockingAssign_vertype_exp_rhs:
 ∀extenv tenv wc rhs.
 vertype_stmt extenv tenv (NonBlockingAssign wc rhs) ⇒ ∃t. OPTION_ALL (λe. vertype_exp extenv tenv e t) rhs
Proof
 rw [Once vertype_stmt_cases] \\ simp [] \\ asm_exists_tac
QED

Theorem vertype_v_deterministic:
 ∀v t t'. vertype_v v t ∧ vertype_v v t' ⇒ t' = t
Proof
 rw [vertype_v_cases]
QED

Theorem vertype_exp_deterministic:
 ∀extenv tenv t' e t. vertype_exp extenv tenv e t ⇒ vertype_exp extenv tenv e t' ⇒ t' = t
Proof
 ntac 3 gen_tac \\ ho_match_mp_tac vertype_exp_ind \\ rpt conj_tac \\ rpt strip_tac'
 >- (fs [Once vertype_exp_cases] \\ metis_tac [vertype_v_deterministic])
 >- fs [Once vertype_exp_cases]
 >- fs [Once vertype_exp_cases]
 >- fs [Once vertype_exp_cases]
 >- fs [Once vertype_exp_cases]
 >- fs [Once vertype_exp_cases]
 >- fs [Once vertype_exp_cases]
 >- fs [Once vertype_exp_cases]
 >- fs [Once vertype_exp_cases]
 >- (pop_assum mp_tac \\ simp [Once vertype_exp_cases] \\ metis_tac [])
 >- (pop_assum mp_tac \\ simp [Once vertype_exp_cases] \\ metis_tac [])
QED

(** Can always extend type env **)

Theorem vertype_list_cong:
 !tenv1 tenv2 env.
 vertype_list tenv1 env ∧ (!var t. tenv1 var = SOME t ⇒ tenv2 var = SOME t) ⇒ vertype_list tenv2 env
Proof
 rw [vertype_list_def] \\ rpt drule_first \\ simp []
QED

Theorem vertype_list_extend:
 !tenv1 tenv2 env.
 vertype_list (alist_to_map tenv1) env ⇒ vertype_list (alist_to_map (tenv1 ++ tenv2)) env
Proof
 rpt strip_tac \\ irule vertype_list_cong \\ asm_exists_any_tac \\
 simp [alist_to_map_alookup, alistTheory.ALOOKUP_APPEND]
QED

Theorem vertype_list_extend_Ev_from_decls:
 ∀tenv1 tenv2 env.
 vertype_list (Ev_from_decls tenv1) env ⇒ vertype_list (Ev_from_decls (tenv1 ⧺ tenv2)) env
Proof
 simp [Ev_from_decls_def, vertype_list_extend]
QED

Theorem vertype_env_extend:
 !tenv1 tenv2 env.
 vertype_env (alist_to_map tenv1) env ⇒ vertype_env (alist_to_map (tenv1 ++ tenv2)) env
Proof
 simp [vertype_env_vertype_list] \\ rpt strip_tac' \\ imp_res_tac vertype_list_extend \\ simp []
QED

Theorem vertype_env_extend_Ev_from_decls:
 !tenv1 tenv2 env.
 vertype_env (Ev_from_decls tenv1) env ⇒ vertype_env (Ev_from_decls (tenv1 ++ tenv2)) env
Proof
 simp [Ev_from_decls_def, vertype_env_extend]
QED

Theorem vertype_exp_cong:
 !extenv tenv1 e t.
 vertype_exp extenv tenv1 e t ==>
 !tenv2. (!var t. tenv1 var = SOME t ==> tenv2 var = SOME t) ==>
 vertype_exp extenv tenv2 e t
Proof
 ntac 2 gen_tac \\ ho_match_mp_tac vertype_exp_ind \\
 rpt conj_tac \\ rpt strip_tac' \\ simp [Once vertype_exp_cases] \\
 rpt drule_first \\ rpt asm_exists_tac
QED

Theorem vertype_exp_extend:
 !extenv tenv1 tenv2 e t.
 vertype_exp extenv (alist_to_map tenv1) e t ==> vertype_exp extenv (alist_to_map (tenv1 ++ tenv2)) e t
Proof
 rpt strip_tac \\ irule vertype_exp_cong \\ asm_exists_any_tac \\ rpt strip_tac \\
 fs [alist_to_map_alookup, alistTheory.ALOOKUP_APPEND]
QED
     
Theorem vertype_stmt_cong:
 !extenv tenv1 p.
 vertype_stmt extenv tenv1 p ==>
 !tenv2. (!var t. tenv1 var = SOME t ==> tenv2 var = SOME t) ==>
 vertype_stmt extenv tenv2 p
Proof
 ntac 2 gen_tac \\ ho_match_mp_tac vertype_stmt_ind \\
 rpt conj_tac \\ rpt strip_tac' \\ simp [Once vertype_stmt_cases]
 >- drule_strip vertype_exp_cong
 >- (drule_strip vertype_exp_cong \\ asm_exists_tac \\ conj_tac
    >- (fs [EVERY_MEM] \\ PairCases \\ rpt strip_tac \\ drule_first \\ fs [] \\ drule_strip vertype_exp_cong)
    \\ Cases_on ‘d’ \\ fs [])
 >- metis_tac []
 >- metis_tac [vertype_exp_cong]
 >- (first_assum drule \\ strip_tac \\ asm_exists_tac \\ metis_tac [vertype_exp_cong])
 >- metis_tac []
 >- metis_tac [vertype_exp_cong]
 \\ first_assum drule \\ strip_tac \\ asm_exists_tac \\ metis_tac [vertype_exp_cong]
QED

Theorem vertype_stmt_extend:
 !extenv tenv1 tenv2 p.
 vertype_stmt extenv (alist_to_map tenv1) p ==> vertype_stmt extenv (alist_to_map (tenv1 ++ tenv2)) p
Proof
 rpt strip_tac \\ irule vertype_stmt_cong \\ asm_exists_any_tac \\ rpt strip_tac \\
 fs [alist_to_map_alookup, alistTheory.ALOOKUP_APPEND]
QED

(** More things **)

(* len = 0 check needed to handle empty list (as both [] and [F] are interpreted as zero elsewhere) *)
val n2VArray_def = Define ‘
 n2VArray len n = if len = 0 then VArray [] else VArray (zero_extend len (n2v n))’;

Theorem vertype_v_n2VArray:
 !n len. n < 2**len ==> vertype_v (n2VArray len n) (VArray_t len)
Proof
 rw [vertype_v_cases, n2VArray_def] \\ dep_rewrite.DEP_REWRITE_TAC [length_zero_extend] \\ rw [length_n2v] \\
 ‘n <= 2 ** len - 1’ by decide_tac \\ ‘0 < n’ by decide_tac \\ drule_strip bitTheory.LOG2_LE_MONO \\ rfs [log2_twoexp_sub1, bitTheory.LOG2_def]
QED

Triviality pad_left_dropWhile:
 !l x. PAD_LEFT x (LENGTH l) (dropWhile ($<=> x) l) = l
Proof
 Induct \\ fs [PAD_LEFT] \\ rw [] \\
 dep_rewrite.DEP_REWRITE_TAC [DECIDE “!x y. y <= x ==> SUC x - y = SUC (x - y)”] \\
 simp [LENGTH_dropWhile_LESS_EQ, GENLIST_CONS]
QED

Triviality genlist_k_append:
 !l x. GENLIST (K x) l ++ [x] = GENLIST (K x) (SUC l)
Proof
 simp [GENLIST]
QED

Triviality every_eq_genlist:
 !l x. EVERY ($<=> x) l <=> l = GENLIST (K x) (LENGTH l)
Proof
 Induct \\ rw [GENLIST_CONS] \\ metis_tac []
QED

Triviality length_dropWhile_suc:
 !l P. LENGTH (dropWhile P l) <> SUC (LENGTH l)
Proof
 rpt gen_tac \\ qspecl_then [‘P’, ‘l’] mp_tac LENGTH_dropWhile_LESS_EQ \\ decide_tac
QED

Triviality length_dropWhile_suc_lt:
 !l P. LENGTH (dropWhile P l) < SUC (LENGTH l)
Proof
 rpt gen_tac \\ qspecl_then [‘P’, ‘l’] mp_tac LENGTH_dropWhile_LESS_EQ \\ decide_tac
QED

Theorem n2VArray_v2n:
 !l. n2VArray (LENGTH l) (v2n l) = VArray l
Proof
 rw [n2VArray_def, n2v_v2n, bitstringTheory.zero_extend_def, pad_left_dropWhile] \\
 Cases_on ‘l’ \\ fs [PAD_LEFT, genlist_k_append, GENLIST_CONS, every_eq_genlist]
QED

Theorem ver2n_n2VArray:
 !bs n. ver2n (VArray bs) = INR n ==> n2VArray (LENGTH bs) n = VArray bs
Proof
 rw [n2VArray_def, ver2n_def, ver2v_def, sum_map_def] \\ rw [n2v_v2n]
 >- (simp [bitstringTheory.zero_extend_def, PAD_LEFT, genlist_k_append] \\ fs [arithmeticTheory.ADD1, every_eq_genlist] \\
    Cases_on ‘bs’ \\ fs [arithmeticTheory.ADD1])
 >- rw [bitstringTheory.zero_extend_def, pad_left_dropWhile]
QED

Theorem n2VArray_ver2n:
 !bs n. n < 2 ** LENGTH bs /\ n2VArray (LENGTH bs) n = VArray bs ==> ver2n (VArray bs) = INR n
Proof
 rw [n2VArray_def, ver2n_def, ver2v_def, sum_map_def]
 >- (EVAL_TAC \\ decide_tac)
 >- (first_assum (once_rewrite_tac o sing o GSYM) \\ simp [v2n_zero_extend])
QED

(** Mostly old messy runtime type system and same shape things below here,
    used in the translator (should move this to separate theory...) **)

(*
val has_type_bool = has_type_rules |> CONJUNCT1;
val has_type_array_base = has_type_rules |> CONJUNCT2 |> CONJUNCT1;
val has_type_array_step = has_type_rules |> CONJUNCT2 |> CONJUNCT2;

val has_type_cases_imp = has_type_cases |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL;
*)

val BOOL_def = Define `
  BOOL (b:bool) v <=> v = VBool b`;

val WORD_def = Define `
  WORD (w:'a word) v <=> v = w2ver w`;

(* Arrays are in reverse order as we only have packed arrays in "reverse order"
   in this formalization *)
val WORD_ARRAY_def = Define `
  WORD_ARRAY pred (arr:'a word -> 'b) v <=>
   case v of
       VBool _ => F
     | VArray vs => LENGTH vs = dimword(:'a) /\
                    !i. ?w. sum_revEL (w2n i) vs = INR w /\ pred (arr i) w`;


val var_has_value_def = Define `
 var_has_value (env:envT) var P = ?v. ALOOKUP env var = SOME v /\ P v`;

val var_has_type_def = Define `
 var_has_type env var ty = ?v. ALOOKUP env var = SOME v /\ vertype_v v ty`;

(* Old var_has_type definition, used in translator, but should probably be replaced *)
val var_has_type_old_def = Define `
 var_has_type_old env var P = ?hrep. var_has_value env var (P hrep)`;

val nbq_var_has_type_def = Define `
 nbq_var_has_type s var ty = !v. get_nbq_var s var = INR v ==> vertype_v v ty`;

(* List version of var_has_type and nbq_var_has_type *)
val vars_has_type_def = Define `
 (vars_has_type env [] = T) /\
 (vars_has_type env ((v, ty) :: xs) = (var_has_type env v ty /\ vars_has_type env xs))`;

val nbq_vars_has_type_def = Define `
 (nbq_vars_has_type env [] = T) /\
 (nbq_vars_has_type env ((v, ty) :: xs) = (nbq_var_has_type env v ty /\ nbq_vars_has_type env xs))`;

(** Various lemmas **)

val BOOL_eq = Q.store_thm("BOOL_eq",
 `!f1 f2 v.
   BOOL f1 v /\
   BOOL f2 v ==>
   f1 = f2`,
 rw [BOOL_def]);

val WORD_eq = Q.store_thm("WORD_eq",
 `!f1 f2 v.
   WORD f1 v /\
   WORD f2 v ==>
   f1 = f2`,
 rw [WORD_def] \\ fs [w2ver_bij]);

(*val WORD_ARRAY_BOOL_eq = Q.store_thm("WORD_ARRAY_BOOL_eq",
 `!f1 f2 v.
   WORD_ARRAY BOOL f1 v /\
   WORD_ARRAY BOOL f2 v ==>
   f1 = f2`,
 rw [WORD_ARRAY_def, BOOL_def] \\ every_case_tac \\ fs [] \\
 match_mp_tac EQ_EXT \\ gen_tac \\
 last_x_assum (qspec_then `x` assume_tac) \\
 fs [w2ver_bij]);

val WORD_ARRAY_WORD_eq = Q.store_thm("WORD_ARRAY_WORD_eq",
 `!f1 f2 v.
   WORD_ARRAY WORD f1 v /\
   WORD_ARRAY WORD f2 v ==>
   f1 = f2`,
 rw [WORD_ARRAY_def, WORD_def] \\ every_case_tac \\ fs [] \\
 match_mp_tac EQ_EXT \\ gen_tac \\
 last_x_assum (qspec_then `x` assume_tac) \\
 fs [w2ver_bij]);

val WORD_ARRAY_WORD_ARRAY_WORD_eq = Q.store_thm("WORD_ARRAY_WORD_ARRAY_WORD_eq",
 `!f1 f2 v.
   WORD_ARRAY (WORD_ARRAY WORD) f1 v /\
   WORD_ARRAY (WORD_ARRAY WORD) f2 v ==>
   f1 = f2`,
 rw [WORD_ARRAY_def, WORD_def] \\ every_case_tac \\ fs [] \\
 rpt (match_mp_tac EQ_EXT \\ gen_tac) \\
 rpt (first_x_assum (qspec_then `x` strip_assume_tac)) \\
 every_case_tac \\ fs [] \\
 rpt (first_x_assum (qspec_then `x'` assume_tac)) \\
 fs [w2ver_bij]);*)

val WORD_verlength = Q.store_thm("WORD_verlength",
 `!w v. WORD (w:'a word) v ==> verlength v = dimindex(:'a)`,
 rw [WORD_def, w2ver_def, verlength_def]);

(*val vars_has_type_append = Q.store_thm("vars_has_type_append",
 `!vs tys1 tys2. vars_has_type vs (tys1 ++ tys2) <=> vars_has_type vs tys1 /\ vars_has_type vs tys2`,
 Induct_on `tys1` >- rw [vars_has_type_def] \\ Cases_on `h` \\ rw [vars_has_type_def] \\ eq_tac \\ simp []);

val same_shape_refl_help = Q.prove(
 `!v1 v2. v1 = v2 ==> same_shape v1 v2`,
 recInduct same_shape_ind \\ rw [same_shape_def]);

val same_shape_refl = Q.store_thm("same_shape_refl",
 `!v. same_shape v v`,
 rw [same_shape_refl_help]);

val same_shape_sym = Q.store_thm("same_shape_sym",
 `!v1 v2. same_shape v1 v2 = same_shape v2 v1`,
 recInduct same_shape_ind \\ rw [same_shape_def] \\ metis_tac []);

val same_shape_trans = Q.store_thm("same_shape_trans",
 `!v1 v2 v3. same_shape v1 v2 /\ same_shape v2 v3 ==> same_shape v1 v3`,
 recInduct same_shape_ind \\ rw [same_shape_def] \\ Cases_on `v3` \\ fs [same_shape_def] \\
 Cases_on `l` \\ fs [same_shape_def]);

val WORD_ver2n = Q.store_thm("WORD_ver2n",
 `!w v. WORD w v ==> ver2n v = INR (w2n w)`,
 rw [WORD_def, ver2n_def, ver2v_def, w2ver_def, sum_mapM_VBool, sum_map_def, v2n_w2v]);

val EXP_n_lt_2n = Q.store_thm("EXP_n_lt_2n",
 `!n. n < 2 ** n`,
 Induct \\ rw [arithmeticTheory.EXP]);

val same_shape_VArray_from_v = Q.store_thm("same_shape_VArray_from_v",
 `!v1 v2. LENGTH v1 = LENGTH v2 ==> same_shape (VArray (MAP VBool v1)) (VArray (MAP VBool v2))`,
 Induct \\ rw [same_shape_def] \\ Cases_on `v2` \\ fs [same_shape_def]);

val same_shape_LENGTH = Q.store_thm("same_shape_LENGTH",
 `!xs ys. same_shape (VArray xs) (VArray ys) ==> LENGTH xs = LENGTH ys`,
 Induct \\ Cases_on `ys` \\ rw [same_shape_def]);

val same_shape_snoc = Q.store_thm("same_shape_snoc",
 `!xs x ys y.
   same_shape (VArray xs) (VArray ys) /\ same_shape x y ==>
   same_shape (VArray (xs ++ [x])) (VArray (ys ++ [y]))`,
 Induct \\ Cases_on `ys` \\ rw [same_shape_def]);

val same_shape_VArray_cong = Q.store_thm("same_shape_VArray_cong",
 `!l l'.
   (!n. n < LENGTH l ==> ?ln l'n. sum_revEL n l = INR ln /\ sum_revEL n l' = INR l'n /\
                                  same_shape ln l'n) /\
   LENGTH l = LENGTH l' ==>
   same_shape (VArray l) (VArray l')`,
 Induct \\ Cases_on `l'` \\ rw [same_shape_def]
 >- (first_x_assum (qspec_then `LENGTH l` mp_tac) \\ impl_tac >- DECIDE_TAC \\ fs [sum_revEL_LENGTH])
 \\ first_x_assum match_mp_tac \\ rpt strip_tac \\ fs [] \\
    first_x_assum (qspec_then `n` mp_tac) \\ impl_tac >- DECIDE_TAC \\ metis_tac [sum_revEL_INR_LENGTH]);

val same_shape_VArray_cong2 = Q.store_thm("same_shape_VArray_cong2",
 `!l l'.
   same_shape (VArray l) (VArray l') <=>
   (!n ln l'n. n < LENGTH l /\ EL n l = ln /\ EL n l' = l'n ==> same_shape ln l'n) /\
   LENGTH l = LENGTH l'`,
 Induct \\ Cases_on `l'` \\ rw [same_shape_def] \\ eq_tac \\ rw []
 >- (Cases_on `n` \\ fs [])
 >- (first_x_assum (qspec_then `0` mp_tac) \\ simp [])
 \\ first_x_assum (qspec_then `SUC n` mp_tac) \\ simp []);

val same_shape_VArray_sum_revEL_cong = Q.store_thm("same_shape_VArray_sum_revEL_cong",
 `!l l' n.
   (!(i:'a word). ?lsub. LENGTH lsub = n /\ sum_revEL (w2n i) l = INR (VArray (MAP VBool lsub))) /\
   (!(i:'a word). ?l'sub. LENGTH l'sub = n /\ sum_revEL (w2n i) l' = INR (VArray (MAP VBool l'sub))) /\
   LENGTH l = dimword (:'a) /\
   LENGTH l' = dimword (:'a) ==>
   same_shape (VArray l) (VArray l')`,
 rpt strip_tac \\ match_mp_tac same_shape_VArray_cong \\ rpt strip_tac \\ fs [] \\
 rpt (first_x_assum (qspec_then `n2w n':'a word` assume_tac)) \\
 fs [w2n_n2w] \\ rpt strip_tac \\
 `n' < dimword (:'a)` by metis_tac [dimword_def, EXP_n_lt_2n, arithmeticTheory.LESS_TRANS] \\
 fs [arithmeticTheory.LESS_MOD] \\ match_mp_tac same_shape_VArray_from_v \\ fs []);

val same_shape_append = Q.store_thm("same_shape_append",
 `!xs1 xs2 ys1 ys2.
   same_shape (VArray xs1) (VArray xs2) /\ same_shape (VArray ys1) (VArray ys2) ==>
   same_shape (VArray (xs1 ++ ys1)) (VArray (xs2 ++ ys2))`,
 rw [same_shape_VArray_cong2] \\ rw [EL_APPEND_EQN]);

val same_shape_VArray_MAP_VBool = Q.store_thm("same_shape_VArray_MAP_VBool",
`!l1 l2. LENGTH l1 = LENGTH l2 ==> same_shape (VArray (MAP VBool l1)) (VArray (MAP VBool l2))`,
 Induct \\ rw [same_shape_def] \\ Cases_on `l2` \\ fs [same_shape_def]);

val same_shape_w2ver = Q.store_thm("same_shape_w2ver",
 `!(w1:'a word) (w2:'a word). same_shape (w2ver w1) (w2ver w2)`,
 rw [w2ver_def, same_shape_VArray_from_v]);

val same_shape_BOOL = Q.store_thm("same_shape_BOOL",
 `!b1 v1 b2 v2. BOOL b1 v1 /\ BOOL b2 v2 ==> same_shape v1 v2`,
 rw [BOOL_def, same_shape_def]);

val same_shape_WORD = Q.store_thm("same_shape_WORD",
 `!w1 v1 w2 v2. WORD (w1:'a word) v1 /\ WORD (w2:'a word) v2 ==> same_shape v1 v2`,
 rw [WORD_def, w2ver_def, same_shape_VArray_from_v]);

val same_shape_WORD_ARRAY_BOOL = Q.store_thm("same_shape_WORD_ARRAY_BOOL",
 `!(w1:'a word -> bool) v1 (w2:'a word -> bool) v2.
   WORD_ARRAY BOOL w1 v1 /\ WORD_ARRAY BOOL w2 v2 ==> same_shape v1 v2`,
 rw [WORD_ARRAY_def, BOOL_def] \\ every_case_tac \\ fs [] \\
 match_mp_tac same_shape_VArray_cong \\ rw [] \\
 rpt (first_x_assum (qspec_then `n2w n` assume_tac)) \\
 rfs [arithmeticTheory.LESS_MOD, same_shape_def]);

val same_shape_WORD_ARRAY_WORD = Q.store_thm("same_shape_WORD_ARRAY_WORD",
 `!(w1:'a word -> 'b word) v1 (w2:'a word -> 'b word) v2.
   WORD_ARRAY WORD w1 v1 /\ WORD_ARRAY WORD w2 v2 ==> same_shape v1 v2`,
 rw [WORD_ARRAY_def, WORD_def, w2ver_def] \\

 every_case_tac \\ fs [] \\
 match_mp_tac same_shape_VArray_cong \\ rw [] \\
 rpt (first_x_assum (qspec_then `n2w n` assume_tac)) \\
 rfs [arithmeticTheory.LESS_MOD] \\

 match_mp_tac same_shape_VArray_MAP_VBool \\
 simp [length_w2v]);

val same_shape_WORD_ARRAY_WORD_ARRAY_WORD = Q.store_thm("same_shape_WORD_ARRAY_WORD_ARRAY_WORD",
 `!(w1:'a word -> 'b word -> 'c word) v1 (w2:'a word -> 'b word -> 'c word) v2.
   WORD_ARRAY (WORD_ARRAY WORD) w1 v1 /\ WORD_ARRAY (WORD_ARRAY WORD) w2 v2 ==> same_shape v1 v2`,
 rw [WORD_ARRAY_def, WORD_def, w2ver_def] \\

 (* First level *)
 every_case_tac \\ fs [] \\
 match_mp_tac same_shape_VArray_cong \\ rw [] \\
 rpt (first_x_assum (qspec_then `n2w n` assume_tac)) \\
 rfs [arithmeticTheory.LESS_MOD] \\

 (* Second level *)
 every_case_tac \\ fs [] \\
 match_mp_tac same_shape_VArray_cong \\ rw [] \\
 rpt (first_x_assum (qspec_then `n2w n'` assume_tac)) \\
 rfs [arithmeticTheory.LESS_MOD] \\

 match_mp_tac same_shape_VArray_MAP_VBool \\
 simp [length_w2v]);

(** Has value/type thms **)

(* var_has_value_imp_var_has_type *)

val has_type_VArray_not_VBool_t = Q.store_thm("has_type_VArray_not_VBool_t",
 `!vs. ~has_type (VArray vs) VBool_t`,
 gen_tac \\ once_rewrite_tac [has_type_cases] \\ strip_tac \\ fs []);

val has_type_VBool_not_VArray_t = Q.store_thm("has_type_VBool_not_VArray_t",
 `!b is. ~has_type (VBool b) (VArray_t is)`,
 rpt gen_tac \\ once_rewrite_tac [has_type_cases] \\ strip_tac \\ fs []);

val has_type_VArray_tl = Q.store_thm("has_type_VArray_tl",
 `!y ys.
   has_type (VArray (y::ys)) (VArray_t [SUC (LENGTH ys)]) ==>
   has_type (VArray ys) (VArray_t [LENGTH ys])`,
 rewrite_tac [Once has_type_cases] \\ rw [] \\ match_mp_tac has_type_array_base \\ simp []);

val var_has_value_var_has_type_BOOL = Q.store_thm("var_has_value_var_has_type_BOOL",
 `!var b env.
   var_has_value env var (BOOL b) ==> var_has_type env var VBool_t`,
 rw [var_has_value_def, var_has_type_def, BOOL_def, has_type_rules]);

val var_has_type_old_var_has_type_BOOL = Q.store_thm("var_has_type_old_var_has_type_BOOL",
 `!var env.
   var_has_type_old env var BOOL <=> var_has_type env var VBool_t`,
 rw [var_has_type_old_def] \\ eq_tac
 >- rw [var_has_value_var_has_type_BOOL]
 \\ rw [var_has_type_def, Once has_type_cases, var_has_value_def, BOOL_def] \\ rw []);

val has_type_w2ver = Q.store_thm("has_type_w2ver",
 `!(w:'a word). has_type (w2ver w) (VArray_t [dimindex (:'a)])`,
 rw [w2ver_def] \\ match_mp_tac has_type_array_base \\ rw [MEM_MAP] \\ simp [has_type_rules]);

val var_has_value_var_has_type_WORD = Q.store_thm("var_has_value_var_has_type_WORD",
 `!var (w:'a word) env.
   var_has_value env var (WORD w) ==> var_has_type env var (VArray_t [dimindex (:'a)])`,
 rw [var_has_value_def, var_has_type_def, WORD_def, has_type_w2ver]);

val var_has_type_old_var_has_type_WORD_help = Q.prove(
 `!vs. (!v. MEM v vs ==> has_type v VBool_t) ==> ?bs. vs = MAP VBool bs`,
 Induct \\ rw [] \\ reverse (Cases_on `h`)
 >- (pop_assum (qspec_then `VArray l` mp_tac) \\ simp [has_type_VArray_not_VBool_t]) \\
 last_x_assum mp_tac \\ impl_tac >- simp [] \\ strip_tac \\ qexists_tac `b::bs` \\
 simp []);

val var_has_type_old_var_has_type_WORD = Q.store_thm("var_has_type_old_var_has_type_WORD",
 `!var env.
   var_has_type_old env var (WORD:'a word -> value -> bool) <=>
   var_has_type env var (VArray_t [dimindex (:'a)])`,
 rw [var_has_type_old_def] \\ eq_tac
 >- rw [var_has_value_var_has_type_WORD]
 \\ rw [var_has_type_def, Once has_type_cases, var_has_value_def, WORD_def] \\ rw [w2ver_def] \\
    drule_strip var_has_type_old_var_has_type_WORD_help \\
    qexists_tac `v2w bs` \\ match_mp_tac MAP_CONG \\ simp [w2v_v2w]);

val var_has_value_var_has_type_WORD_ARRAY_help = Q.prove(
 `!P (w:'a word -> 'b) v l.
   (!(i:'a word). sum_revEL (w2n i) l = INR (P (w i))) /\
   LENGTH l = dimword (:'a) /\
   MEM v l ==>
   ?(w':'b). v = P w'`,
 simp [MEM_EL, sum_revEL_def] \\ rpt strip_tac \\ rveq \\
 first_x_assum (qspec_then `n2w (LENGTH l - n - 1)` assume_tac) \\
 fs [] \\ `(LENGTH l - (n + 1)) MOD dimword (:'a) = (LENGTH l - (n + 1))` by fs [] \\
 fs [] \\ FULL_CASE_TAC \\ fs [] \\ fs [sum_EL_EL] \\
 `LENGTH l − (LENGTH l − (n + 1) + 1) = n` by DECIDE_TAC \\ fs [] \\
 metis_tac []);

(* In need of cleanup *)
val var_has_type_old_var_has_type_WORD_ARRAY_BOOL = Q.store_thm("var_has_type_old_var_has_type_WORD_ARRAY_BOOL",
 `!var env.
   var_has_type_old env var (WORD_ARRAY BOOL : ('a word -> bool) -> value -> bool) <=>
   var_has_type env var (VArray_t [dimword (:'a)])`,
 rw [var_has_type_old_def] \\ eq_tac
 >- (rw [var_has_value_def, var_has_type_def, WORD_ARRAY_def, BOOL_def] \\ every_case_tac \\ fs [] \\
    match_mp_tac has_type_array_base \\ rw [] \\
    drule_strip var_has_value_var_has_type_WORD_ARRAY_help \\
    simp [has_type_bool])
 \\ rw [var_has_type_def, Once has_type_cases, var_has_value_def, WORD_ARRAY_def, BOOL_def] \\
    asm_exists_tac \\ simp [] \\
    qexists_tac `(\i. OUTR (ver2bool (EL (LENGTH vs − (w2n i + 1)) vs)))` \\
    rw [sum_revEL_def]

    >-
    (simp [sum_EL_EL] \\ fs [MEM_EL] \\
    Cases_on `EL (LENGTH vs − (w2n i + 1)) vs` >- simp [ver2bool_def] \\
    first_x_assum (qspec_then `EL (LENGTH vs − (w2n i + 1)) vs` mp_tac) \\
    rw [] >- (qexists_tac `LENGTH vs − (w2n i + 1)` \\ simp []) \\
    simp [has_type_VArray_not_VBool_t])

    \\ metis_tac [w2n_lt]);

val var_has_value_var_has_type_WORD_ARRAY = Q.store_thm("var_has_value_var_has_type_WORD_ARRAY",
 `!var (w:'a word -> 'b word) env.
   var_has_value env var (WORD_ARRAY WORD w) ==>
   var_has_type env var (VArray_t [dimword (:'a); dimindex(:'b)])`,
 rw [var_has_value_def, var_has_type_def, WORD_ARRAY_def, WORD_def] \\
 FULL_CASE_TAC \\ fs [] \\
 match_mp_tac has_type_array_step \\
 simp [dimword_def] \\ rpt strip_tac \\ drule var_has_value_var_has_type_WORD_ARRAY_help \\
 rpt (disch_then drule) \\ strip_tac \\ rveq \\ simp [has_type_w2ver]);

(* In need of cleanup *)
val var_has_type_old_var_has_type_WORD_ARRAY = Q.store_thm("var_has_type_old_var_has_type_WORD_ARRAY",
 `!var env.
   var_has_type_old env var (WORD_ARRAY WORD:('a word -> 'b word) -> value -> bool) <=>
   var_has_type env var (VArray_t [dimword (:'a); dimindex (:'b)])`,
 rw [var_has_type_old_def] \\ eq_tac
 >- rw [var_has_value_var_has_type_WORD_ARRAY]
 \\ rw [var_has_type_def, Once has_type_cases, var_has_value_def, WORD_ARRAY_def, WORD_def] \\
    asm_exists_tac \\ simp [] \\
    qexists_tac `(\i. OUTR (ver2w (EL (LENGTH vs − (w2n i + 1)) vs)))` \\
    rw [sum_revEL_def]

    >-
    (simp [sum_EL_EL] \\ simp [w2ver_def, ver2w_def] \\

    fs [MEM_EL] \\ first_x_assum (qspec_then `EL (LENGTH vs − (w2n i + 1)) vs` mp_tac) \\
    impl_tac >- (qexists_tac `LENGTH vs − (w2n i + 1)` \\ simp []) \\
    strip_tac \\ drule_strip has_type_cases_imp \\ fs [has_type_rules] \\
    simp [ver2v_def] \\ drule_strip var_has_type_old_var_has_type_WORD_help \\
    match_mp_tac MAP_CONG \\ rw [sum_mapM_VBool, sum_map_def, w2v_v2w])

    \\ metis_tac [w2n_lt]);

(* In need of cleanup *)
val var_has_type_old_var_has_type_WORD_ARRAY_WORD_ARRAY = Q.store_thm("var_has_type_old_var_has_type_WORD_ARRAY_WORD_ARRAY",
 `!var env.
   var_has_type_old env var (WORD_ARRAY (WORD_ARRAY WORD):('a word -> 'b word -> 'c word) -> value -> bool) <=>
   var_has_type env var (VArray_t [dimword (:'a); dimword (:'b); dimindex (:'c)])`,
 rw [var_has_type_old_def] \\ eq_tac
 >- (rw [var_has_value_def, var_has_type_def, WORD_ARRAY_def, WORD_def] \\ every_case_tac \\ fs [] \\
    
    match_mp_tac has_type_array_step \\ rw [] \\
    fs [MEM_sum_revEL] \\ first_x_assum (qspec_then `n2w n` strip_assume_tac) \\ rfs [] \\
    FULL_CASE_TAC \\ fs [] \\ rveq \\
    
    match_mp_tac has_type_array_step \\ rw [] \\

    drule_strip var_has_value_var_has_type_WORD_ARRAY_help \\
    simp [has_type_w2ver])

 \\ rw [var_has_type_def, Once has_type_cases, var_has_value_def, WORD_ARRAY_def, WORD_def] \\
    asm_exists_tac \\ simp [] \\
    qexists_tac `(\i j. let outer = EL (LENGTH vs − (w2n i + 1)) vs;
                            outer = OUTR (get_VArray_data outer) in
                            OUTR (ver2w (EL (LENGTH outer - (w2n j + 1)) outer)))` \\
    rw [sum_revEL_def]

    >-
    (simp [sum_EL_EL] \\ simp [w2ver_def, ver2w_def] \\

    fs [MEM_EL] \\ first_x_assum (qspec_then `EL (LENGTH vs − (w2n i + 1)) vs` mp_tac) \\
    impl_tac >- (qexists_tac `LENGTH vs − (w2n i + 1)` \\ simp []) \\
    strip_tac \\ drule_strip has_type_cases_imp \\ fs [has_type_rules] \\
    simp [get_VArray_data_def] \\

    gen_tac \\ conj_tac >- metis_tac [w2n_lt] \\
    fs [MEM_EL] \\ first_x_assum (qspec_then `EL (LENGTH vs' − (w2n i' + 1)) vs'` mp_tac) \\
    impl_tac >- (qexists_tac `LENGTH vs' − (w2n i' + 1)` \\ simp [] \\ metis_tac [DIMWORD_GT_0]) \\
    strip_tac \\ drule_strip has_type_cases_imp \\ fs [has_type_rules] \\
    simp [ver2v_def] \\ drule_strip var_has_type_old_var_has_type_WORD_help \\
    match_mp_tac MAP_CONG \\ rw [sum_mapM_VBool, sum_map_def, w2v_v2w])

    \\ metis_tac [w2n_lt]);

val var_has_type_get_var = Q.store_thm("var_has_type_get_var",
 `!s name ty. var_has_type s.vars name ty ==> ?v. get_var s name = INR v`,
 rw [var_has_type_def, var_has_value_def, get_var_def] \\ TOP_CASE_TAC);

(* Can be generalized *)
val has_type_same_shape_help = Q.store_thm("has_type_same_shape_help",
 `!v. (!v'. same_shape v' v ==> has_type v' VBool_t) <=> has_type v VBool_t`,
 Cases \\ eq_tac \\ rpt strip_tac \\ TRY (Cases_on `v'`) \\ fs [has_type_rules, same_shape_def]
 >- (pop_assum (qspec_then `VArray l` mp_tac) \\ simp [same_shape_refl])
 \\ fs [has_type_VArray_not_VBool_t]);

val same_shape_has_type' = Q.prove(
 `!v ty. has_type v ty ==> !v'. same_shape v' v ==> has_type v' ty`,
 ho_match_mp_tac has_type_ind \\ rw [] \\ Cases_on `v'` \\ fs [same_shape_def]
 >- simp [has_type_bool] \\

 fs [same_shape_VArray_cong2, MEM_EL] \\
 TRY (match_mp_tac has_type_array_base) \\
 TRY (match_mp_tac has_type_array_step) \\
 rw [] \\
 first_x_assum irule \\ metis_tac [MEM_EL]);

val same_shape_has_type = Q.store_thm("same_shape_has_type",
 `!v v' ty. same_shape v' v /\ has_type v ty ==> has_type v' ty`,
 metis_tac [same_shape_has_type']);

val has_type_same_shape'_lem1 = Q.prove(
 `!vs vs'.
   (∀v'. MEM v' vs ⇒ ∀v. has_type v VBool_t ⇒ same_shape v' v) /\
   LENGTH vs = LENGTH vs' /\
   (∀v. MEM v vs' ⇒ has_type v VBool_t)
   ==>
   same_shape (VArray vs) (VArray vs')`,
 Induct >- rw [same_shape_def] \\ Cases_on `vs'` \\ fs [same_shape_def]);

val has_type_same_shape' = Q.prove(
 `!v' ty. has_type v' ty ==> !v. has_type v ty ==> same_shape v' v`,
 ho_match_mp_tac has_type_ind \\ rw []

 >- (Cases_on `v'` >- simp [same_shape_def] \\ fs [has_type_VArray_not_VBool_t])

 >- (drule_strip has_type_cases_imp \\ fs [has_type_rules] \\
    simp [same_shape_def, has_type_same_shape'_lem1])

 \\ drule_strip has_type_cases_imp \\ fs [has_type_rules] \\ rveq \\
    rw [same_shape_VArray_cong2] \\ metis_tac [MEM_EL]);

val has_type_same_shape = Q.store_thm("has_type_same_shape",
 `!v v' ty. has_type v' ty /\ has_type v ty ==> same_shape v' v`,
 metis_tac [has_type_same_shape']);
*)

val _ = export_theory ();
