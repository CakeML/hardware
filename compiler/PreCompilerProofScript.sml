open hardwarePreamble;

open sumExtraTheory verilogTheory verilogMetaTheory verilogTypeTheory PreCompilerTheory;

val _ = new_theory "PreCompilerProof";

infix THEN2;
infix THEN3;
infix THEN4;
infix THEN5;
infix THEN6;

(* Semantics properties *)

(* Special (simpler) case because full case not needed here *)
Theorem prun_Case_append:
 !l1 l2 fext s e v t.
 erun fext s e = INR v /\
 EVERY (ISR o erun fext s) (MAP FST l1) (* <-- strictly speaking only needed for l2 case *) ==>
 prun fext s (Case t e (l1 ++ l2) NONE) =
 if EXISTS (\cond. erun fext s cond = INR v) (MAP FST l1) then
  prun fext s (Case t e l1 NONE)
 else
  prun fext s (Case t e l2 NONE)
Proof
 Induct >- simp [] \\ PairCases \\ simp [prun_def, sum_bind_def] \\ rpt strip_tac \\
 fs [ISR_exists, sum_bind_def] \\ IF_CASES_TAC \\ simp []
QED

Theorem prun_Case_GENLIST:
 !len fext s e bs i f t.
 erun fext s e = INR (VArray bs) /\
 ver2n (VArray bs) = INR i /\
 i < len ==>
 prun fext s (Case t e (GENLIST (\i. (Const (n2VArray (LENGTH bs) i), f i)) len) NONE) = prun fext s (f i)
Proof
 (* Probably proof messy for no good reason: *)
 Induct >- simp [] \\ rw [GENLIST, SNOC_APPEND] \\

 drule_strip prun_Case_append \\ disch_then (dep_rewrite.DEP_REWRITE_TAC o sing) \\
 conj_tac >- simp [EVERY_MAP, EVERY_GENLIST, erun_def] \\ simp [EXISTS_MAP, EXISTS_GENLIST] \\

 simp [erun_def] \\ reverse (Cases_on ‘i = len’) >- (‘i < len’ by fs [] \\ rw [] \\ metis_tac [ver2n_n2VArray]) \\

 reverse (rw []) \\ drule_strip ver2n_n2VArray >- simp [prun_def, sum_bind_def, erun_def] \\

 drule_strip ver2n_lt \\ ‘i' < 2 ** LENGTH bs’ by fs [] \\ imp_res_tac n2VArray_ver2n \\ fs []
QED

Theorem prun_Case_GENLIST_other_case:
 !len fext s e bs i f t.
 erun fext s e = INR (VArray bs) /\
 ver2n (VArray bs) = INR i /\
 ~(i < len) ==>
 prun fext s (Case t e (GENLIST (\i. (Const (n2VArray (LENGTH bs) i), f i)) len) NONE) = INR s
Proof
 (* Probably proof messy for no good reason: *)
 rewrite_tac [DECIDE “∀(i:num) len. ~(i < len) ⇔ len ≤ i”] \\
 Induct >- simp [prun_def] \\ rw [GENLIST, SNOC_APPEND] \\

 drule_strip prun_Case_append \\ disch_then (dep_rewrite.DEP_REWRITE_TAC o sing) \\
 conj_tac >- simp [EVERY_MAP, EVERY_GENLIST, erun_def] \\ simp [EXISTS_MAP, EXISTS_GENLIST] \\

 rw [prun_def, sum_bind_def, erun_def] \\ fs [n2VArray_def] \\ every_case_tac
 >- fs [EVAL “ver2n (VArray [])”] \\
 fs [ver2n_def, ver2v_def, sum_map_INR] \\ rveq \\ fs [v2n_zero_extend]
QED

Theorem prun_Case_GENLIST_gen:
 !len fext s e bs i f t.
 erun fext s e = INR (VArray bs) ==>
 prun fext s (Case t e (GENLIST (\i. (Const (n2VArray (LENGTH bs) i), f i)) len) NONE) =
 if v2n bs < len then
  prun fext s (f (v2n bs))
 else
  INR s
Proof
 rw []
 >- (drule_strip prun_Case_GENLIST \\ simp [ver2n_def, ver2v_def, sum_map_def])
 >- (drule_strip prun_Case_GENLIST_other_case \\ simp [ver2n_def, ver2v_def, sum_map_def])
QED

(* Temporary names *)

Theorem tmpvar_bij:
 ∀x y. tmpvar x = tmpvar y ⇔ x = y
Proof
 simp [tmpvar_def]
QED

Theorem is_tmpvar_tmpvar:
 ∀n. is_tmpvar (tmpvar n)
Proof
 rw [is_tmpvar_def, tmpvar_def]
QED

Theorem run_decls_tmpvardecls:
 ∀tmps l h fbits fbits' vs vs'.
 run_decls fbits (tmpvardecls tmps) vs = (fbits, vs') ⇒
 (∀var. ~is_tmpvar var ⇒ sum_alookup vs' var = sum_alookup vs var)
Proof
 Induct \\ TRY PairCases \\ fs [tmpvardecls_def, run_decls_def] \\ rpt strip_tac \\ drule_first \\
 rw [sum_alookup_cons] \\ fs [is_tmpvar_tmpvar]
QED

Triviality tmpvar_check_run_decls_lem:
 ∀decls fbits fbits' vs vs'.
 EVERY not_tmpvar_decl decls ∧
 run_decls fbits decls vs = (fbits',vs') ∧
 (∀var v. sum_alookup vs var = INR v ⇒ ¬is_tmpvar var) ⇒
 ∀var v. sum_alookup vs' var = INR v ⇒ ¬is_tmpvar var
Proof
 Induct \\ TRY PairCases \\ simp [run_decls_def] \\ rpt strip_tac' \\ every_case_tac
 >| [pairarg_tac \\ fs [], ALL_TAC] \\
 drule_last \\ disch_then irule \\ rw [sum_alookup_cons] \\ strip_tac \\ fs [not_tmpvar_decl_def]
QED

Theorem tmpvar_check_run_decls:
 !m fbits fbits' vs vs'.
 tmpvar_check m ∧
 run_decls fbits m.decls vs = (fbits', vs') ∧
 (∀var v. sum_alookup vs var = INR v ⇒ ~is_tmpvar var) ⇒
 (∀var v. sum_alookup vs' var = INR v ⇒ ~is_tmpvar var)
Proof
 metis_tac [tmpvar_check_def, tmpvar_check_run_decls_lem]
QED

Theorem tmpvar_check_correct:
 ∀m. tmpvar_check m ⇒ fresh_tmpvar_decls 0 m.decls
Proof
 rw [tmpvar_check_def, EVERY_MEM, fresh_tmpvar_decls_def, decls_type_INL, alistTheory.ALOOKUP_NONE, MEM_MAP] \\
 strip_tac \\ drule_first \\ Cases_on ‘y’ \\ gvs [not_tmpvar_decl_def, is_tmpvar_tmpvar]
QED

Theorem tenv_type_Ev_from_decls_decls_type:
 ∀decls var. tenv_type (Ev_from_decls decls) var = decls_type decls var
Proof
 rw [tenv_type_def, Ev_from_decls_def, decls_type_sum_alookup, alist_to_map_alookup] \\
 CASE_TAC \\ fs [sum_alookup_INL, GSYM sum_alookup_INR]
QED

Theorem tmpvars_extend_refl[simp]:
 ∀tmps. tmpvars_extend tmps tmps
Proof
 simp [tmpvars_extend_def]
QED

Theorem tmpvars_extend_trans:
 ∀tmps1 tmps2 tmps3. tmpvars_extend tmps2 tmps1 ∧ tmpvars_extend tmps3 tmps2 ⇒ tmpvars_extend tmps3 tmps1
Proof
 simp [tmpvars_extend_def]
QED

Theorem tmpvars_range_alt_FST:
 ∀l h tmps. tmpvars_range l h tmps ⇔ EVERY ((λk. l ≤ k ∧ k < h) o FST) tmps
Proof
 rw [tmpvars_range_def, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]
QED

Theorem EVERY_FST_ALOOKUP:
 ∀l k x P. EVERY (P ∘ FST) l ∧ ALOOKUP l k = SOME x ⇒ P k
Proof
 rw [EVERY_MEM] \\ drule_strip alistTheory.ALOOKUP_MEM \\ drule_first \\ fs []
QED

Theorem tmpvars_range_tmpvars_extend:
 ∀tmpnumstart tmpnum tmps ty.
 tmpvars_range tmpnumstart tmpnum tmps ⇒ tmpvars_extend ((tmpnum,ty)::tmps) tmps
Proof
 rw [tmpvars_range_alt_FST, tmpvars_extend_def, sum_alookup_cons, sum_alookup_INR] \\
 drule_strip EVERY_FST_ALOOKUP \\ fs []
QED

Theorem tmpvars_distinct_tmpvars_range:
 ∀tmpnumstart tmpnum tmps ty.
 tmpvars_distinct tmps ∧ tmpvars_range tmpnumstart tmpnum tmps ⇒
 tmpvars_distinct ((tmpnum,ty)::tmps)
Proof
 rw [tmpvars_distinct_def, tmpvars_range_def, EVERY_MEM] \\ strip_tac \\ fs [MEM_MAP] \\ drule_first \\
 pairarg_tac \\ fs []
QED

Theorem tmpvars_range_lt:
 ∀l h h' tmps. tmpvars_range l h tmps ∧ h ≤ h' ⇒ tmpvars_range l h' tmps
Proof
 rw [tmpvars_range_def] \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ Cases \\ rw []
QED

Theorem tmpvars_range_cons:
 ∀tmpnumstart tmpnum tmps ty.
 tmpvars_range tmpnumstart tmpnum tmps ∧ tmpnumstart ≤ tmpnum ⇒
 tmpvars_range tmpnumstart (SUC tmpnum) ((tmpnum,ty)::tmps)
Proof
 rw [tmpvars_range_def] \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ Cases \\ rw []
QED

Triviality alookup_tmpvardecls_shape:
 ∀tmps var t. ALOOKUP (MAP (λ(i,t). (tmpvar i,t)) tmps) var = SOME t ⇒ ∃n. var = tmpvar n
Proof
 Induct \\ TRY PairCases \\ rw [tmpvardecls_def] \\ metis_tac []
QED

Theorem ALOOKUP_MAP_tmpvar:
 ∀l k v. ALOOKUP (MAP (λ(k, v). (tmpvar k, v)) l) (tmpvar k) = ALOOKUP l k
Proof
 Induct \\ TRY PairCases \\ rw [] \\ fs [tmpvar_def]
QED

Theorem vertype_exp_extend_Ev_from_decls:
 ∀extenv l1 l2 e ty.
 vertype_exp extenv (Ev_from_decls l1) e ty ⇒ vertype_exp extenv (Ev_from_decls (l1 ++ l2)) e ty
Proof
 rw [Ev_from_decls_def, vertype_exp_extend]
QED

Theorem vertype_stmt_extend_Ev_from_decls:
 ∀extenv l1 l2 e.
 vertype_stmt extenv (Ev_from_decls l1) e ⇒ vertype_stmt extenv (Ev_from_decls (l1 ++ l2)) e
Proof
 rw [Ev_from_decls_def, vertype_stmt_extend]
QED

Theorem EVERY_vertype_stmt_extend_Ev_from_decls:
 ∀extenv l1 l2 ps.
 EVERY (vertype_stmt extenv (Ev_from_decls l1)) ps ⇒ EVERY (vertype_stmt extenv (Ev_from_decls (l1 ++ l2))) ps
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ simp [vertype_stmt_extend_Ev_from_decls]
QED

Theorem vertype_exp_extend_tmpvardecls:
 ∀extenv decls tmps1 tmps2 e t.
 vertype_exp extenv (Ev_from_decls (decls ⧺ tmpvardecls tmps1)) e t ∧ tmpvars_extend tmps2 tmps1 ⇒
 vertype_exp extenv (Ev_from_decls (decls ⧺ tmpvardecls tmps2)) e t
Proof
 rpt strip_tac \\ irule vertype_exp_cong \\ asm_exists_any_tac \\
 simp [Ev_from_decls_def, alist_to_map_alookup, alistTheory.ALOOKUP_APPEND] \\
 rpt gen_tac \\ TOP_CASE_TAC \\
 simp [tmpvardecls_def, MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] \\
 strip_tac \\ drule_strip alookup_tmpvardecls_shape \\ fs [ALOOKUP_MAP_tmpvar, tmpvars_extend_def, sum_alookup_INR]
QED

Theorem vertype_stmt_extend_tmpvardecls:
 ∀extenv decls tmps1 tmps2 s.
 vertype_stmt extenv (Ev_from_decls (decls ⧺ tmpvardecls tmps1)) s ∧ tmpvars_extend tmps2 tmps1 ⇒
 vertype_stmt extenv (Ev_from_decls (decls ⧺ tmpvardecls tmps2)) s
Proof
 rpt strip_tac \\ irule vertype_stmt_cong \\ asm_exists_any_tac \\
 simp [Ev_from_decls_def, alist_to_map_alookup, alistTheory.ALOOKUP_APPEND] \\
 rpt gen_tac \\ TOP_CASE_TAC \\
 simp [tmpvardecls_def, MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] \\
 strip_tac \\ drule_strip alookup_tmpvardecls_shape \\ fs [ALOOKUP_MAP_tmpvar, tmpvars_extend_def, sum_alookup_INR]
QED

Theorem vertype_env_cong:
 ∀tenv1 tenv2 env.
 vertype_env tenv1 env ∧ (∀var t. tenv1 var = SOME t ⇒ tenv2 var = SOME t) ⇒ vertype_env tenv2 env
Proof
 rw [vertype_env_def] \\ rpt drule_first \\ rpt asm_exists_tac
QED

Theorem decls_type_tmpvardecls:
 ∀tmps var. decls_type (tmpvardecls tmps) var = sum_alookup (MAP (λ(i,t). (tmpvar i, t)) tmps) var
Proof
 rw [decls_type_sum_alookup] \\ f_equals_tac \\ simp [tmpvardecls_def, MAP_MAP_o] \\
 match_mp_tac MAP_CONG \\ simp [] \\ Cases \\ simp []
QED

Theorem tmpvars_extend_decls_type:
 ∀tmps1 tmps2 var t.
 tmpvars_extend tmps2 tmps1 ∧ decls_type (tmpvardecls tmps1) var = INR t ⇒
 decls_type (tmpvardecls tmps2) var = INR t
Proof
 simp [decls_type_tmpvardecls] \\ Induct \\ TRY PairCases \\ rw [tmpvars_extend_def, sum_alookup_cons] \\
 fs [sum_alookup_INR, ALOOKUP_MAP_tmpvar] \\
 drule_strip alookup_tmpvardecls_shape \\ fs [tmpvar_bij, ALOOKUP_MAP_tmpvar] \\
 first_x_assum (qspecl_then [‘n’, ‘t’] mp_tac) \\ simp [sum_alookup_INR]
QED

Theorem vertype_env_extend_tmpvardecls:
 ∀decls tmps1 tmps2 env.
 vertype_env (Ev_from_decls (decls ⧺ tmpvardecls tmps1)) env ∧ tmpvars_extend tmps2 tmps1 ⇒
 vertype_env (Ev_from_decls (decls ⧺ tmpvardecls tmps2)) env
Proof
 rpt strip_tac \\ match_mp_tac vertype_env_cong \\ asm_exists_tac \\
 rpt gen_tac \\ simp [Ev_from_decls_decls_type, decls_type_append] \\ TOP_CASE_TAC \\
 strip_tac \\ drule_strip tmpvars_extend_decls_type
QED

(** Array preprocessing infrastructure **)

val array_rel_def = Define ‘
 array_rel s s' <=>
  s'.fbits = s.fbits /\ (* <-- tmps are init to zero just to keep fbits in sync... (X instead of zero would make more sense) *)
  (!var v. get_var s var = INR v ==> get_var s' var = INR v) /\
  (!var. get_nbq_var s' var = get_nbq_var s var)’;

Theorem array_rel_refl:
 ∀s. array_rel s s
Proof
 rw [array_rel_def]
QED

Theorem array_rel_trans:
 ∀s1 s2 s3. array_rel s1 s2 ∧ array_rel s2 s3 ⇒ array_rel s1 s3
Proof
 simp [array_rel_def]
QED

Theorem array_rel_get_var:
 ∀s1 s2 var v. get_var s1 var = INR v ∧ array_rel s1 s2 ⇒ get_var s2 var = INR v
Proof
 simp [array_rel_def]
QED

Theorem array_rel_set_var:
 !s1 s2 var v. array_rel s1 s2 ==> array_rel (set_var s1 var v) (set_var s2 var v)
Proof
 rw [array_rel_def, set_var_fbits, get_var_cleanup] \\ rw [] \\ fs []
QED

Theorem array_rel_set_nbq_var:
 !s1 s2 var v. array_rel s1 s2 ==> array_rel (set_nbq_var s1 var v) (set_nbq_var s2 var v)
Proof
 rw [array_rel_def, set_nbq_var_fbits, get_var_cleanup] \\ rw [] \\ fs []
QED

Theorem array_rel_erun:
 !e fext s1 s2 v. erun fext s1 e = INR v /\ array_rel s1 s2 ==> erun fext s2 e = INR v
Proof
 rw [array_rel_def] \\ drule_strip erun_cong_INR
QED

Theorem array_rel_nd_reset:
 !v v' s1 s1' s2. nd_reset s1 v = (s1', v') /\ array_rel s1 s2 ==> ?s2'. nd_reset s2 v = (s2', v') /\ array_rel s1' s2'
Proof
 Cases \\ simp [nd_reset_def]
 >- (rw [oracleTheory.oracle_bit_def, array_rel_def] \\ fs [get_var_fbits, get_nbq_var_fbits])
 \\ rpt strip_tac \\ rpt (pairarg_tac \\ fs []) \\ rw []
  >- (match_mp_tac oracleTheory.oracle_bits_cong \\ rpt asm_exists_any_tac \\ fs [array_rel_def, oracleTheory.init_seq_eq_def])
  \\ imp_res_tac oracleTheory.oracle_bits_correct \\ rveq \\ fs [array_rel_def, get_var_fbits, get_nbq_var_fbits]
QED

Theorem array_rel_prun_assn_rhs:
 !fext s1 s1' s2 lhs rhs v.
 prun_assn_rhs fext s1 lhs rhs = INR (s1', v) /\ array_rel s1 s2 ==> ?s2'. prun_assn_rhs fext s2 lhs rhs = INR (s2', v) /\ array_rel s1' s2'
Proof
 Cases_on ‘rhs’ \\ rw [prun_assn_rhs_def]
 >- (Cases_on ‘lhs’ \\ fs [prun_assn_lhs_prev_def, sum_map_INR] \\ drule_strip array_rel_nd_reset \\ fs [array_rel_def] \\ drule_first \\ simp [])
 \\ fs [sum_map_INR] \\ drule_strip array_rel_erun \\ simp []
QED

Theorem array_rel_assn:
 !fext s1 s2 use_nbq lhs name v v'. assn fext s1 use_nbq lhs v = INR (name, v') /\ array_rel s1 s2 ==> assn fext s2 use_nbq lhs v = INR (name, v')
Proof
 rw [array_rel_def] \\ drule_strip assn_cong_INR
QED

Theorem array_rel_prun_bassn:
 ∀fext s1 s1' s2 wc v.
 prun_bassn fext s1 wc v = INR s1' ∧ array_rel s1 s2 ⇒
 ∃s2'. prun_bassn fext s2 wc v = INR s2' ∧ array_rel s1' s2'
Proof
 rw [prun_bassn_def, sum_for_INR] \\ Cases_on ‘v'’ \\ drule_strip array_rel_assn \\ simp [] \\
 drule_strip array_rel_set_var \\ simp []
QED

Theorem array_rel_prun_nbassn:
 ∀fext s1 s1' s2 wc v.
 prun_nbassn fext s1 wc v = INR s1' ∧ array_rel s1 s2 ⇒
 ∃s2'. prun_nbassn fext s2 wc v = INR s2' ∧ array_rel s1' s2'
Proof
 rw [prun_nbassn_def, sum_for_INR] \\ Cases_on ‘v'’ \\ drule_strip array_rel_assn \\ simp [] \\
 drule_strip array_rel_set_nbq_var \\ simp []
QED

(* No prun_cong_INR in verilogMetaTheory currently... but this could be moved to that theory... *)
Theorem array_rel_prun:
 !fext s1 p s1' s2. prun fext s1 p = INR s1' /\ array_rel s1 s2 ==> ?s2'. prun fext s2 p = INR s2' /\ array_rel s1' s2'
Proof
 recInduct prun_ind \\ rpt conj_tac
 >- (rw [prun_def] \\ simp [])
 >- (rw [prun_Seq] \\ metis_tac [])
 >- (rw [prun_IfElse] \\ drule_strip array_rel_erun \\ metis_tac [])
 >- (rw [prun_Case] \\ imp_res_tac array_rel_erun \\ metis_tac [])
 >- rw [prun_def]
 >- (rw [prun_def] \\ simp [])
 >- (rw [prun_def, sum_bind_INR] \\ pairarg_tac \\ rveq \\ drule_strip array_rel_prun_assn_rhs \\ fs [] \\
     drule_strip array_rel_prun_bassn \\ simp [])
 >- (rw [prun_def, sum_bind_INR] \\ pairarg_tac \\ rveq \\ drule_strip array_rel_prun_assn_rhs \\ fs [] \\
     drule_strip array_rel_prun_nbassn \\ simp [])
QED

Definition array_rel_prun_def:
 array_rel_prun extenv decls p p' ⇔
 ∀fext s1 s1' s2.
 prun fext s1 p = INR s1' ∧ array_rel s1 s2 ∧
 vertype_env (Ev_from_decls decls) s1 ∧
 vertype_fext_n extenv fext ⇒
 ∃s2'. prun fext s2 p' = INR s2' ∧ array_rel s1' s2'
End

Theorem array_rel_prun_refl:
 ∀extenv decls p. array_rel_prun extenv decls p p
Proof
 rw [array_rel_prun_def] \\ drule_strip array_rel_prun \\ simp []
QED

Theorem array_rel_pruns:
 !ps fext s1 s1' s2.
 sum_foldM (prun fext) s1 ps = INR s1' /\ array_rel s1 s2 ==>
 ?s2'. sum_foldM (prun fext) s2 ps = INR s2' /\ array_rel s1' s2'
Proof
 Induct \\ fs [sum_foldM_INR] \\ metis_tac [array_rel_prun]
QED

Definition array_rel_filled_prun_def:
 array_rel_filled_prun extenv decls p p' ⇔
 ∀fext s1 s1' s2.
 prun fext s1 p = INR s1' ∧ array_rel s1 s2 ∧
 vertype_env (Ev_from_decls decls) s1 ∧
 vertype_env_filled (Ev_from_decls decls) s1 ∧
 vertype_fext_n extenv fext ⇒
 ∃s2'. prun fext s2 p' = INR s2' ∧ array_rel s1' s2'
End

(** Preprocess dynamic array read behavior proof **)

Theorem mem_alookup:
 ∀l k v. MEM (k, v) l ⇒ ∃v'. ALOOKUP l k = SOME v'
Proof
 rpt strip_tac \\ Cases_on ‘ALOOKUP l k’ \\ fs [alistTheory.ALOOKUP_NONE, MEM_MAP] \\
 first_x_assum (qspec_then ‘(k, v)’ mp_tac) \\ simp []
QED

Theorem mem_map_alookup:
 ∀l k. MEM k (MAP FST l) ⇒ ∃v. ALOOKUP l k = SOME v
Proof
 rw [MEM_MAP] \\ PairCases_on ‘y’ \\ drule_strip mem_alookup \\ simp []
QED

Theorem decls_type_extend_tmpvardecls:
 ∀var t decls tmps tmps'.
 decls_type (decls ++ tmpvardecls tmps) var = INR t ∧ tmpvars_extend tmps' tmps ⇒
 decls_type (decls ++ tmpvardecls tmps') var = INR t
Proof
 simp [decls_type_append] \\ rpt gen_tac \\ CASE_TAC \\ rpt strip_tac \\
 drule_strip tmpvars_extend_decls_type
QED

Definition tmpvarwrites_def:
 tmpvarwrites tmps = set (MAP (tmpvar o FST) tmps)
End

Definition newvars_inv_def:
 newvars_inv extenv decls newvars tmps ⇔
 EVERY (λ(tmpnum,varlen,var,ilen,idx).
        decls_type (decls ++ tmpvardecls tmps) (tmpvar tmpnum) = INR VBool_t ∧
        (case var of
         | Var var => decls_type decls var = INR (VArray_t varlen)
         | InputVar var => sum_alookup extenv var = INR (VArray_t varlen)
         | _ => F) ∧
        no_array_read_dyn_exp (Ev_from_decls decls) extenv idx ∧
        vertype_exp extenv (Ev_from_decls decls) idx (VArray_t ilen)) newvars
End

Theorem vertype_exp_wt_array_no_crash:
 ∀fext extenv tenv s n e t.
 vertype_exp extenv tenv e t ⇒
 t = VArray_t n ∧
 vertype_env tenv s ∧
 vertype_fext_n extenv fext ∧
 vertype_env_filled tenv s ⇒
 ∃v. erun fext s e = INR v ∧ vertype_v v t
Proof
 ntac 5 gen_tac \\ ho_match_mp_tac vertype_exp_ind \\ rw [erun_def]
 >- simp []
 >- fs [erun_get_var_def, vertype_env_filled_def]
 >- fs [erun_get_var_def, vertype_fext_n_def, sum_alookup_INR]
 THEN2 (fs [erun_get_var_def, vertype_env_filled_def, vertype_fext_n_def, sum_alookup_INR] \\
        drule_first \\ fs [vertype_v_cases, sum_bind_def, get_array_slice_def])
 >- (rpt drule_first \\
     fs [sum_bind_def, sum_map_def, vertype_v_cases, ver_mapVArray_def, ver2n_def, ver2v_def,
         erun_arith_def, n2ver_def, v2ver_def, ver_liftVArray_def, ver_fixwidth_fixwidth])
QED

Theorem newvars_inv_runtime_lengths:
 ∀extenv decls newvars tmps fext s.
 newvars_inv extenv decls newvars tmps ∧
 vertype_env (Ev_from_decls decls) s ∧
 vertype_fext_n extenv fext ∧
 vertype_env_filled (Ev_from_decls decls) s ⇒
 EVERY (λ(tmpnum,varlen,var,ilen,idx).
        (∃bs. erun fext s var = INR (VArray bs) ∧ LENGTH bs = varlen) ∧
        ∃bs. erun fext s idx = INR (VArray bs) ∧ LENGTH bs = ilen)
       newvars
Proof
 rw [newvars_inv_def] \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ PairCases \\ rw []
 >- (qspecl_then [‘fext’, ‘extenv’, ‘Ev_from_decls decls’, ‘s’, ‘x1’, ‘x2’, ‘VArray_t x1’]
                 mp_tac vertype_exp_wt_array_no_crash \\
     Cases_on ‘x2’ \\ fs [sum_alookup_INR] \\
     simp [Once vertype_exp_cases, Ev_from_decls_decls_type,
           erun_def, erun_get_var_def, vertype_v_cases] \\ strip_tac \\ simp [])
 >- (drule_strip (SIMP_RULE (srw_ss()) [AND_IMP_INTRO] vertype_exp_wt_array_no_crash) \\
     fs [vertype_v_cases])
QED

Theorem newvars_subset_tmpvars_extend:
 ∀newvars tmps tmps'.
 set (MAP FST newvars) ⊆ set (MAP FST tmps) ∧ tmpvars_extend tmps' tmps ⇒
 set (MAP FST newvars) ⊆ set (MAP FST tmps')
Proof
 rw [tmpvars_extend_def, sum_alookup_INR, pred_setTheory.SUBSET_DEF] \\ drule_first \\
 drule_strip mem_map_alookup \\ drule_first \\ drule_strip alistTheory.ALOOKUP_MEM \\
 simp [MEM_MAP] \\ asm_exists_any_tac \\ simp []
QED

Theorem newvars_inv_newvars_append:
 ∀extenv decls newvars1 newvars2 tmps.
 newvars_inv extenv decls (newvars1 ⧺ newvars2) tmps ⇔
 newvars_inv extenv decls newvars1 tmps ∧ newvars_inv extenv decls newvars2 tmps
Proof
 simp [newvars_inv_def]
QED

Theorem newvars_inv_tmpvars_extend:
 ∀extenv decls newvars tmps tmps'.
 newvars_inv extenv decls newvars tmps ∧ tmpvars_extend tmps' tmps ⇒
 newvars_inv extenv decls newvars tmps'
Proof
 rw [newvars_inv_def] \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ PairCases \\ rw [] \\
 metis_tac [decls_type_extend_tmpvardecls, vertype_exp_extend_tmpvardecls]
QED

Theorem newvars_tmps_subset_tmpvarwrites:
 ∀newvars tmps.
 set (MAP FST newvars) ⊆ set (MAP FST tmps) ⇒ set (MAP (tmpvar o FST) newvars) ⊆ tmpvarwrites tmps
Proof
 simp [tmpvarwrites_def, LIST_TO_SET_MAP, pred_setTheory.IMAGE_COMPOSE]
QED

Triviality vertype_exp_array_no_array_read_dyn_exp_lem:
 ∀extenv tenv len e t. vertype_exp extenv tenv e t ⇒ t = (VArray_t len) ⇒ no_array_read_dyn_exp tenv extenv e
Proof
 ntac 3 gen_tac \\ ho_match_mp_tac vertype_exp_ind \\ simp [no_array_read_dyn_exp_def]
QED

Theorem vertype_exp_array_no_array_read_dyn_exp:
 ∀extenv tenv len e. vertype_exp extenv tenv e (VArray_t len) ⇒ no_array_read_dyn_exp tenv extenv e
Proof
 metis_tac [vertype_exp_array_no_array_read_dyn_exp_lem]
QED

Theorem v2n_MAP_KF:
 ∀l. v2n (MAP (K F) l) = 0
Proof
 Induct \\ TRY (pop_assum mp_tac) \\ EVAL_TAC \\ simp [bitstringTheory.bitify_reverse_map] \\
 EVAL_TAC \\ simp [numposrepTheory.l2n_APPEND]
QED

Definition array_read_exp_rel_def:
 array_read_exp_rel extenv decls newvars e e' ⇔
 ∀fext s1 s2 v.
 erun fext s1 e = INR v ∧ array_rel s1 s2 ∧
 vertype_env (Ev_from_decls decls) s1 ∧
 vertype_fext_n extenv fext ∧
 EVERY (λ(tmpnum,varlen,var,ilen,idx).
        ∀v. erun fext s1 (ArrayIndex var ilen idx) = INR v ⇒
            get_var s2 (tmpvar tmpnum) = INR v) newvars ⇒
 erun fext s2 e' = INR v
End

val compile_array_read_exp_unchanged_tac =
 simp [compile_array_read_exp_def] \\ rw [no_array_read_dyn_exp_def]
 >- (match_mp_tac vertype_exp_extend_Ev_from_decls \\ asm_exists_tac)
 >- simp [newvars_inv_def]
 \\ drule_strip array_rel_erun \\ asm_exists_tac;

Theorem compile_array_read_exp_correct:
 ∀e decls tmpnum tmps tmpnum' tmps' newvars e' extenv t tmpnumstart.
 compile_array_read_exp decls extenv tmpnum tmps e = (tmpnum', tmps', newvars, e') ∧
 vertype_exp extenv (Ev_from_decls decls) e t ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ⇒
 tmpnum ≤ tmpnum' ∧
 tmpvars_extend tmps' tmps ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧

 no_array_read_dyn_exp (Ev_from_decls decls) extenv e' ∧
 vertype_exp extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) e' t ∧

 newvars_inv extenv decls newvars tmps' ∧
 set (MAP FST newvars) ⊆ set (MAP FST tmps') ∧
 EVERY (λn. tmpnum ≤ n ∧ n < tmpnum') (MAP FST newvars) ∧ (* <-- needed for induction step for binops *)
 ALL_DISTINCT (MAP FST newvars) ∧

 array_read_exp_rel extenv decls newvars e e'
Proof
 rewrite_tac [array_read_exp_rel_def] \\ Induct
 >- (* Const *) compile_array_read_exp_unchanged_tac
 >- (* Var *) compile_array_read_exp_unchanged_tac
 >- (* InputVar *) compile_array_read_exp_unchanged_tac
 >- (* ArrayIndex *)
 (rpt strip_tac' \\
  qpat_x_assum ‘vertype_exp _ _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_exp_cases]) \\

  (ntac 2 (last_x_assum kall_tac) \\
  fs [compile_array_read_exp_def, get_var_type_impl_def, Ev_from_decls_decls_type, GSYM sum_alookup_INR] \\ rveq \\
  last_x_assum mp_tac \\ TOP_CASE_TAC
  >- (rpt strip_tac' \\ rveq \\ simp [] \\
      conj_asm1_tac >- (match_mp_tac tmpvars_range_tmpvars_extend \\ asm_exists_tac) \\
      rpt conj_tac
      >- (match_mp_tac tmpvars_distinct_tmpvars_range \\ rpt asm_exists_tac)
      >- (match_mp_tac tmpvars_range_cons \\ simp [])
      >- simp [no_array_read_dyn_exp_def]
      >- (simp [Once vertype_exp_cases, Ev_from_decls_decls_type, decls_type_append] \\
          fs [fresh_tmpvar_decls_def, decls_type_tmpvardecls, sum_alookup_cons])
      >- (fs [newvars_inv_def] \\ rpt strip_tac
          >- fs [decls_type_append, fresh_tmpvar_decls_def, decls_type_tmpvardecls, sum_alookup_cons]
          >- drule_strip vertype_exp_array_no_array_read_dyn_exp
          \\ fs [Ev_from_decls_def, vertype_exp_extend])
      \\ simp [erun_def, erun_get_var_def, sum_bind_INR, get_array_index_INR] \\ rpt strip_tac' \\
         drule_strip vertype_exp_erun \\ fs [vertype_env_def] \\ drule_first \\
         fs [Ev_from_decls_decls_type] \\ rveq \\ fs [vertype_v_cases] \\ fs []) \\
  rpt strip_tac' \\ rveq \\ fs [get_const_INR] \\ rpt conj_tac
  >- (fs [Once vertype_exp_cases, vertype_v_cases] \\
      simp [is_ok_idx_const_def] \\ IF_CASES_TAC
      >- simp [no_array_read_dyn_exp_def, get_const_def, sum_bind_def, sum_map_def, ver2n_def, ver2v_def,
               tenv_type_Ev_from_decls_decls_type, get_var_type_def]
      \\ simp [no_array_read_dyn_exp_def])
  >- (IF_CASES_TAC
      >- (simp [Once vertype_exp_cases, Ev_from_decls_decls_type, decls_type_append] \\
          fs [Ev_from_decls_def, vertype_exp_extend, sum_alookup_INR])
      \\ simp [Once vertype_exp_cases, vertype_v_cases]) 
  >- simp [newvars_inv_def] \\
  simp [erun_def, erun_get_var_def, sum_bind_INR, get_array_index_INR] \\ rpt strip_tac' \\
  rveq \\ fs [vertype_env_def, vertype_fext_n_def] \\ drule_first \\
  fs [Ev_from_decls_decls_type, vertype_v_cases, ver2n_INR] \\ rveq \\
  simp [is_ok_idx_const_def, erun_def, erun_get_var_def] \\
  fs [array_rel_def, erun_def] \\ TRY drule_first \\
  simp [sum_bind_def, ver2n_def, ver2v_def, sum_map_def, get_array_index_def, erun_get_var_def, sum_revEL_revEL]))
 >- (* ArraySlice *) compile_array_read_exp_unchanged_tac \\
 rpt strip_tac' \\
 qpat_x_assum ‘vertype_exp _ _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_exp_cases])
 >- (* BUOp *)
 (qpat_x_assum ‘compile_array_read_exp _ _ _ _ _ = _’
               (mp_tac o SIMP_RULE (srw_ss()) [compile_array_read_exp_def,LET_THM]) \\
  pairarg_tac \\ drule_first \\ rw [] \\ simp []
  >- simp [no_array_read_dyn_exp_def]
  >- simp [Once vertype_exp_cases]
  \\ fs [erun_def, sum_bind_INR, ver_liftVBool_INR] \\ TRY strip_tac \\ rveq \\ rpt drule_first)
 \\ (* Binops *)
 (qpat_x_assum ‘compile_array_read_exp _ _ _ _ _ = _’
               (mp_tac o SIMP_RULE (srw_ss()) [compile_array_read_exp_def,LET_THM]) \\
  pairarg_tac \\ drule_first \\
  asm_rewrite_tac [] \\ CONV_TAC (DEPTH_CONV PairedLambda.PAIRED_BETA_CONV) \\
  pairarg_tac \\ drule_first \\ impl_tac >- simp [] \\ rw [] \\ simp []
  >- metis_tac [tmpvars_extend_trans]
  >- simp [no_array_read_dyn_exp_def]
  >- (simp [Once vertype_exp_cases] \\ TRY asm_exists_any_tac \\
      match_mp_tac vertype_exp_extend_tmpvardecls \\ rpt asm_exists_tac)
  >- (simp [newvars_inv_newvars_append] \\ match_mp_tac newvars_inv_tmpvars_extend \\ rpt asm_exists_tac)
  >- (match_mp_tac newvars_subset_tmpvars_extend \\ rpt asm_exists_tac)
  >- (conj_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [])
  >- (simp [ALL_DISTINCT_APPEND] \\ rpt strip_tac \\ fs [EVERY_MEM] \\ rpt drule_first \\ fs [])
  \\ fs [erun_def, sum_bind_INR, CaseEq"value"] \\ rveq \\ rpt drule_first \\ simp [])
QED

Theorem compile_array_read_exp_opt_correct:
 ∀e decls tmpnum tmps tmpnum' tmps' newvars e' extenv t tmpnumstart.
 compile_array_read_exp_opt decls extenv tmpnum tmps e = (tmpnum', tmps', newvars, e') ∧
 OPTION_ALL (λe. vertype_exp extenv (Ev_from_decls decls) e t) e ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ⇒
 tmpnum ≤ tmpnum' ∧
 tmpvars_extend tmps' tmps ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧

 OPTION_ALL (no_array_read_dyn_exp (Ev_from_decls decls) extenv) e' ∧
 OPTION_ALL (λe. vertype_exp extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) e t) e' ∧

 newvars_inv extenv decls newvars tmps' ∧
 set (MAP FST newvars) ⊆ set (MAP FST tmps') ∧
 EVERY (λn. tmpnum ≤ n ∧ n < tmpnum') (MAP FST newvars) ∧
 ALL_DISTINCT (MAP FST newvars) ∧

 OPTREL (array_read_exp_rel extenv decls newvars) e e'
Proof
 Cases \\ simp [compile_array_read_exp_opt_def] >- simp [newvars_inv_def] \\
 rpt strip_tac' \\ pairarg_tac \\ drule_strip compile_array_read_exp_correct \\ fs [] \\ rw []
QED

Theorem mem_flat_genlist_sing:
 ∀n x y. MEM x (FLAT (GENLIST (λi. [y]) n)) ⇒ x = y
Proof
 Induct \\ simp [GENLIST, rich_listTheory.FLAT_SNOC] \\ metis_tac []
QED

Theorem mem_flat_genlist_nil:
 ∀n x. ~MEM x (FLAT (GENLIST (λi. []) n))
Proof
 Induct \\ simp [GENLIST, rich_listTheory.FLAT_SNOC]
QED

Theorem vwrites_compile_array_read_newvars:
 ∀newvars p.
 set (vwrites (compile_array_read_newvars newvars p)) ⊆
 set (vwrites p) ∪ set (MAP (tmpvar o FST) newvars)
Proof
 Induct \\ TRY PairCases \\ simp [compile_array_read_newvars_def] \\
 fs [vwrites_def, evwrites_def, MAP_GENLIST, combinTheory.o_DEF] \\ rw []
 >- (rw [pred_setTheory.SUBSET_DEF] \\ drule_strip mem_flat_genlist_sing \\ simp [])
 \\ fs [pred_setTheory.SUBSET_DEF] \\ metis_tac []
QED

Theorem vwrites_compile_array_read_newvars_preserve_lem:
 ∀newvars p p'.
 set (vwrites p) ⊆ set (vwrites p') ⇒
 set (vwrites p) ⊆ set (vwrites (compile_array_read_newvars newvars p'))
Proof
 Induct \\ TRY PairCases \\ simp [compile_array_read_newvars_def] \\
 fs [vwrites_def, evwrites_def, MAP_GENLIST, combinTheory.o_DEF, pred_setTheory.SUBSET_DEF] \\
 metis_tac []
QED

Theorem vnwrites_compile_array_read_newvars:
 ∀newvars p. vnwrites (compile_array_read_newvars newvars p) = vnwrites p
Proof
 Induct \\ TRY PairCases \\ simp [compile_array_read_newvars_def] \\
 simp [vnwrites_def, MAP_GENLIST, combinTheory.o_DEF, FLAT_EQ_NIL, EVERY_GENLIST]
QED

(* TODO: Name collision... precondition can maybe be made more general *)
Triviality ver2n_n2VArray_lem:
 ∀n len. n < 2 ** len ⇒ ver2n (n2VArray len n) = INR n
Proof
 rw [ver2n_def, n2VArray_def, ver2v_def] >- (EVAL_TAC \\ decide_tac) \\
 simp [sum_map_def, v2n_zero_extend]
QED

Theorem no_array_read_dyn_compile_array_read_newvars:
 ∀extenv tmps newvars decls p.
 newvars_inv extenv decls newvars tmps ⇒
 no_array_read_dyn (Ev_from_decls decls) extenv (compile_array_read_newvars newvars p) =
 no_array_read_dyn (Ev_from_decls decls) extenv p
Proof
 ntac 2 gen_tac \\ Induct \\ TRY PairCases \\ fs [compile_array_read_newvars_def, newvars_inv_def] \\
 rpt gen_tac \\ TOP_CASE_TAC \\ simp [] \\
 rw [no_array_read_dyn_def, EVERY_GENLIST, no_array_read_dyn_exp_def, get_var_type_def,
     get_const_def, sum_bind_def, ver2n_n2VArray_lem, tenv_type_Ev_from_decls_decls_type]
QED

Theorem vertype_stmt_compile_array_read_newvars:
 ∀extenv newvars decls p tmps.
 vertype_stmt extenv (Ev_from_decls (decls ⧺ tmpvardecls tmps)) p ∧
 newvars_inv extenv decls newvars tmps ∧
 set (MAP FST newvars) ⊆ set (MAP FST tmps) ⇒
 vertype_stmt extenv (Ev_from_decls (decls ⧺ tmpvardecls tmps)) (compile_array_read_newvars newvars p)
Proof
 gen_tac \\ Induct \\ TRY PairCases \\ rw [compile_array_read_newvars_def] \\
 simp [Once vertype_stmt_cases] \\ simp [Once vertype_stmt_cases] \\ fs [newvars_inv_def] \\
 rpt strip_tac >- fs [Ev_from_decls_def, vertype_exp_extend] \\
 rw [EVERY_GENLIST] >- simp [Once vertype_exp_cases, vertype_v_n2VArray] \\
 simp [Once vertype_stmt_cases] \\
 fs [newvars_inv_def, Ev_from_decls_def, alist_to_map_alookup, decls_type_sum_alookup, sum_alookup_INR] \\
 every_case_tac \\ fs [] \\
 simp [Once vertype_exp_cases] \\
 simp [alist_to_map_alookup, alistTheory.ALOOKUP_APPEND] \\
 simp [Once vertype_exp_cases, vertype_v_n2VArray]
QED

Triviality tmpnums_from_newvars_not_in_decls:
 ∀tmps : (num # vertype) list.
 decls_type decls var = INR (VArray_t varlen) ∧
 MEM tmpnum (MAP FST tmps) ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_range tmpnumstart tmpnum' tmps ⇒
 tmpvar tmpnum ≠ var
Proof
 rw [fresh_tmpvar_decls_def, tmpvars_range_def, decls_type_sum_alookup, EVERY_MEM, MEM_MAP] \\
 drule_first \\ pairarg_tac \\ fs [] \\ drule_first \\ strip_tac \\ rveq \\ fs []
QED

Theorem tmpvarwrites_tmpvars_extend:
 ∀tmps tmps' w.
 w ∈ tmpvarwrites tmps' ∧ tmpvars_extend tmps tmps' ⇒ w ∈ tmpvarwrites tmps
Proof
 rw [tmpvars_extend_def, tmpvarwrites_def, sum_alookup_INR, MEM_MAP] \\ PairCases_on ‘y’ \\
 drule_strip mem_alookup \\ drule_first \\ drule_strip alistTheory.ALOOKUP_MEM \\
 asm_exists_any_tac \\ simp []
QED

Triviality erun_erun_get_var_HACK1:
 newvars_inv ignore1 ignore2 ((ignore3,ignore4,e,ignore5,ignore6)::ignore7) ignore8 ∧
 erun fext s e = INR v ⇒
 erun_get_var fext s e = INR v
Proof
 rw [newvars_inv_def] \\ every_case_tac \\ fs [erun_def]
QED

Triviality erun_erun_get_var_HACK2:
 erun_get_var fext s e = INR v ∧
 erun fext s e = INR v' ⇒
 v = v' 
Proof
 Cases_on ‘e’ \\ rw [erun_get_var_def, erun_def] \\ fs []
QED

Theorem prun_compile_array_read_newvars:
 ∀s s1 tmpnumstart tmpnum extenv tmps decls fext newvars p.
 newvars_inv extenv decls newvars tmps ∧
 ALL_DISTINCT (MAP FST newvars) ∧
 set (MAP FST newvars) ⊆ set (MAP FST tmps) ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 array_rel s1 s ∧
 vertype_env (Ev_from_decls decls) s1 ∧
 EVERY (λ(tmpnum,varlen,var,ilen,idx).
        (∃bs. erun fext s1 var = INR (VArray bs) ∧ LENGTH bs = varlen) ∧
        ∃bs. erun fext s1 idx = INR (VArray bs) ∧
               LENGTH bs = ilen (*∧ ver2n (VArray bs) = INR i ∧ i < varlen*)) newvars ⇒
 ∃s'. prun fext s (compile_array_read_newvars newvars p) = prun fext s' p ∧
      array_rel s1 s' ∧
      EVERY (λ(tmpnum,varlen,var,ilen,idx).
             ∀v. erun fext s1 (ArrayIndex var ilen idx) = INR v ⇒
                 get_var s' (tmpvar tmpnum) = INR v) newvars ∧
      (∀n. ~MEM n (MAP FST newvars) ⇒ get_var s' (tmpvar n) = get_var s (tmpvar n))
Proof
 rpt gen_tac \\ qid_spec_tac ‘s’ \\ Induct_on ‘newvars’ \\
 TRY PairCases \\ simp [compile_array_read_newvars_def] \\ rpt strip_tac
 >- (qexists_tac ‘s’ \\ simp []) \\
 fs [prun_def] \\ rveq \\ dep_rewrite.DEP_REWRITE_TAC [prun_Case_GENLIST_gen] \\
 conj_tac >- drule_strip array_rel_erun \\
 simp [bitstringTheory.v2n_lt] \\ reverse IF_CASES_TAC
 >- (fs [sum_bind_def, newvars_inv_def] \\ drule_first \\ simp [] \\
     qexists_tac ‘s'’ \\ every_case_tac \\ fs [] \\
     fs [erun_def, erun_get_var_def, sum_bind_def, sum_map_def,
         ver2n_VArray, get_array_index_def, sum_revEL_def]) \\
 rev_drule_strip array_rel_erun \\
 drule_strip erun_erun_get_var_HACK1 \\
 CONV_TAC (STRIP_QUANT_CONV (RATOR_CONV (SIMP_CONV (srw_ss()) [prun_def, prun_assn_rhs_def, erun_def]))) \\
 simp [erun_get_var_def, ver2n_n2VArray_lem, bitstringTheory.v2n_lt, get_array_index_def,
       sum_bind_def, sum_map_def, sum_for_def, sum_revEL_revEL, prun_bassn_def, assn_def] \\
 qmatch_goalsub_abbrev_tac ‘prun fext s' _’ \\
 first_x_assum (qspec_then ‘s'’ mp_tac) \\ unabbrev_all_tac \\
 impl_tac >- (fs [newvars_inv_def] \\
              fs [array_rel_def, tmpvars_range_def, EVERY_MEM, MEM_MAP, set_var_fbits, get_var_cleanup] \\
              rw [] \\ drule_first \\ fs [vertype_env_def, fresh_tmpvar_decls_def] \\
              rpt drule_first \\ pairarg_tac \\ fs [] \\ rveq \\ drule_first \\
              fs [Ev_from_decls_def, alist_to_map_alookup, decls_type_sum_alookup, sum_alookup_INL]) \\
 strip_tac \\ simp [] \\ qexists_tac ‘s'’ \\ rw []
 >- (fs [erun_def, sum_bind_INR, get_var_set_var, get_array_index_INR] \\
     drule_strip erun_erun_get_var_HACK2 \\ gvs [ver2n_INR])
 \\ simp [get_var_set_var, tmpvar_bij]
QED

Triviality LIST_REL_subset_pair_vwrites:
 ∀newwrites ps ps'.
 LIST_REL (λ(_, p) (_, p'). set (vwrites p') ⊆ set (vwrites p) ∪ newwrites) ps ps' ⇒
 set (FLAT (MAP (λ(_, p). vwrites p) ps')) ⊆ set (FLAT (MAP (λ(_, p). vwrites p) ps)) ∪ newwrites
Proof
 gen_tac \\ ho_match_mp_tac LIST_REL_ind \\ simp [] \\ rpt strip_tac' \\ rpt (pairarg_tac \\ fs []) \\
 fs [pred_setTheory.SUBSET_DEF] \\ metis_tac []
QED

Triviality OPTREL_subset_vwrites:
 ∀newwrites p p'.
 OPTREL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ newwrites) p p' ⇒
 set (case p' of NONE => [] | SOME p => vwrites p) ⊆ set (case p of NONE => [] | SOME p => vwrites p) ∪ newwrites
Proof
 gen_tac \\ Cases \\ Cases \\ simp []
QED

Triviality LIST_REL_preserve_pair_vwrites:
 ∀ps ps'.
 LIST_REL (λ(_, p) (_, p'). set (vwrites p) ⊆ set (vwrites p')) ps ps' ⇒
 set (FLAT (MAP (λ(_, p). vwrites p) ps)) ⊆ set (FLAT (MAP (λ(_, p). vwrites p) ps'))
Proof
 ho_match_mp_tac LIST_REL_ind \\ simp [] \\ rpt strip_tac' \\ rpt (pairarg_tac \\ fs []) \\
 fs [pred_setTheory.SUBSET_DEF] \\ metis_tac []
QED

Triviality OPTREL_preserve_vwrites:
 ∀p p'.
 OPTREL (λp p'. set (vwrites p) ⊆ set (vwrites p')) p p' ⇒
 set (case p of NONE => [] | SOME p => vwrites p) ⊆ set (case p' of NONE => [] | SOME p => vwrites p)
Proof
 Cases \\ Cases \\ simp []
QED

Triviality LIST_REL_pair_vnwrites:
 ∀ps ps'.
 LIST_REL (λ(_, p) (_, p'). vnwrites p' = vnwrites p) ps ps' ⇒
 MAP (λ(_, p). vnwrites p) ps' = MAP (λ(_, p). vnwrites p) ps
Proof
 ho_match_mp_tac LIST_REL_ind \\ rw [] \\ rpt (pairarg_tac \\ fs [])
QED

Triviality OPTREL_vnwrites:
 ∀p p'.
 OPTREL (λp p'. vnwrites p' = vnwrites p) p p' ⇒
 (case p' of NONE => [] | SOME p => vnwrites p) = (case p of NONE => [] | SOME p => vnwrites p)
Proof
 Cases \\ Cases \\ simp []
QED

Theorem compile_array_read_newvars_append:
 ∀newvars newvars' p.
 compile_array_read_newvars (newvars ++ newvars') p =
 compile_array_read_newvars newvars (compile_array_read_newvars newvars' p)
Proof
 Induct \\ TRY PairCases \\ simp [compile_array_read_newvars_def]
QED

Theorem prun_Case_cong_array_read:
 ∀t m m' ps ps' d d' s1 s1' s2 fext extenv (decls : declty)
  (newvars1 newvars2 : (num # num # exp # num # exp) list).
 prun fext s1 (Case t m ps d) = INR s1' ∧
 array_rel s1 s2 ∧
 vertype_env (Ev_from_decls decls) s1 ∧
 vertype_env_filled (Ev_from_decls decls) s1 ∧
 vertype_fext_n extenv fext ∧
 EVERY (λ(tmpnum,varlen,var,ilen,idx).
        ∀v. erun fext s1 (ArrayIndex var ilen idx) = INR v ⇒
            get_var s2 (tmpvar tmpnum) = INR v) (newvars2 ++ newvars1) ∧
 array_read_exp_rel extenv decls newvars1 m m' ∧
 LIST_REL (array_read_exp_rel extenv decls newvars2) (MAP FST ps) (MAP FST ps') ∧
 LIST_REL (array_rel_filled_prun extenv decls) (MAP SND ps) (MAP SND ps') ∧
 OPTREL (array_rel_filled_prun extenv decls) d d' ⇒
 ∃s2'. prun fext s2 (Case t m' ps' d') = INR s2' ∧ array_rel s1' s2'
Proof
 Induct_on ‘ps’ \\ Cases_on ‘ps'’ \\ simp []
 >- (Cases_on ‘d’ \\ Cases_on ‘d'’ \\ simp [prun_def, array_rel_filled_prun_def] \\
     rpt strip_tac \\ drule_first \\ simp []) \\
 PairCases \\ PairCases_on ‘h’ \\
 rw [prun_def, sum_bind_INR] \\
 qpat_x_assum ‘array_read_exp_rel _ _ _ _ _’ mp_tac \\
 qpat_assum ‘array_read_exp_rel _ _ _ _ _’ mp_tac \\
 simp_tac (srw_ss()) [array_read_exp_rel_def] \\ rpt (disch_then drule_strip) \\ simp [] \\
 IF_CASES_TAC \\ fs []
 >- (fs [array_rel_filled_prun_def] \\ drule_first \\ simp [])
 \\ metis_tac []
QED

Theorem array_read_exp_rel_prun_assn_rhs:
 ∀rhs rhs' extenv decls newvars s1 s1' s2 fext wc v.
 OPTREL (array_read_exp_rel extenv decls newvars) rhs rhs' ∧
 array_rel s1 s2 ∧
 vertype_env (Ev_from_decls decls) s1 ∧
 vertype_fext_n extenv fext ∧
 EVERY (λ(tmpnum,varlen,var,ilen,idx).
        ∀v. erun fext s1 (ArrayIndex var ilen idx) = INR v ⇒
            get_var s2 (tmpvar tmpnum) = INR v) newvars ∧
 prun_assn_rhs fext s1 wc rhs = INR (s1', v)  ⇒
 ∃s2'. prun_assn_rhs fext s2 wc rhs' = INR (s2', v) ∧ array_rel s1' s2'
Proof
 Cases \\ Cases \\ rw [prun_assn_rhs_def]
 >- (Cases_on ‘wc’ \\ fs [prun_assn_lhs_prev_def, sum_map_INR] \\
     drule_strip array_rel_nd_reset \\
     fs [array_rel_def] \\ drule_first \\ simp [])
 \\ fs [array_read_exp_rel_def, sum_map_INR] \\ rveq \\ drule_first
QED

val vwrites_compile_array_read_newvars_subset_trans_lem =
 pred_setTheory.SUBSET_TRANS
 |> REWRITE_RULE [GSYM AND_IMP_INTRO]
 |> flip MATCH_MP (SPEC_ALL vwrites_compile_array_read_newvars)
 |> GEN_ALL;

Theorem compile_array_read_correct:
 (!decls extenv tmpnum tmps p tmpnumstart tmpnum' tmps' p'.
 compile_array_read decls extenv tmpnum tmps p = (tmpnum', tmps', p') ∧
 vertype_stmt extenv (Ev_from_decls decls) p ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ⇒
 tmpnum ≤ tmpnum' ∧
 set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps' ∧
 set (vwrites p) ⊆ set (vwrites p') ∧
 vnwrites p' = vnwrites p ∧
 no_array_read_dyn (Ev_from_decls decls) extenv p' ∧
 vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) p' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧
 array_rel_filled_prun extenv decls p p')
 ∧
 (!decls extenv tmpnum tmps p tmpnumstart tmpnum' tmps' p'.
 compile_array_read_opt decls extenv tmpnum tmps p = (tmpnum', tmps', p') ∧
 OPTION_ALL (vertype_stmt extenv (Ev_from_decls decls)) p ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ⇒
 tmpnum ≤ tmpnum' ∧
 OPTREL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps') p p' ∧
 OPTREL (λp p'. set (vwrites p) ⊆ set (vwrites p')) p p' ∧
 OPTREL (λp p'. vnwrites p' = vnwrites p) p p' ∧
 OPTION_ALL (no_array_read_dyn (Ev_from_decls decls) extenv) p' ∧
 OPTION_ALL (vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps'))) p' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧
 OPTREL (array_rel_filled_prun extenv decls) p p')
 ∧
 (!decls extenv tmpnum tmps ps tmpnumstart tmpnum' tmps' ps' newvars t.
 compile_array_read_case_list decls extenv tmpnum tmps ps = (tmpnum', tmps', newvars, ps') ∧
 EVERY (λ(e, p). vertype_exp extenv (Ev_from_decls decls) e t ∧
                 vertype_stmt extenv (Ev_from_decls decls) p) ps ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ⇒
 tmpnum ≤ tmpnum' ∧
 LIST_REL (λ(_, p) (_, p'). set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps') ps ps' ∧
 LIST_REL (λ(_, p) (_, p'). set (vwrites p) ⊆ set (vwrites p')) ps ps' ∧
 LIST_REL (λ(_, p) (_, p'). vnwrites p' = vnwrites p) ps ps' ∧
 EVERY (λ(e, p). no_array_read_dyn_exp (Ev_from_decls decls) extenv e ∧
                 no_array_read_dyn (Ev_from_decls decls) extenv p) ps' ∧
 EVERY (λ(e, p). vertype_exp extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) e t ∧
                 vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) p) ps' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧

 newvars_inv extenv decls newvars tmps' ∧
 set (MAP FST newvars) ⊆ set (MAP FST tmps') ∧
 EVERY (λn. tmpnum ≤ n ∧ n < tmpnum') (MAP FST newvars) ∧
 ALL_DISTINCT (MAP FST newvars) ∧

 LIST_REL (array_read_exp_rel extenv decls newvars) (MAP FST ps) (MAP FST ps') ∧
 LIST_REL (array_rel_filled_prun extenv decls) (MAP SND ps) (MAP SND ps'))
Proof
 ho_match_mp_tac compile_array_read_ind \\ rewrite_tac [compile_array_read_def] \\
 rpt conj_tac \\ rpt gen_tac
 >- (* Skip *)
 (rpt strip_tac' \\ fs [] \\ rveq \\
  simp [no_array_read_dyn_def, Once vertype_stmt_cases, array_rel_filled_prun_def, prun_def])

 >- (* Seq *)
 (rpt disch_tac \\ rpt gen_tac \\ simp_tac (srw_ss()) [LET_THM] \\
  rpt (pairarg_tac \\ asm_rewrite_tac [] \\ simp_tac (srw_ss()) []) \\ rpt strip_tac' \\ rveq \\
  qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
  last_x_assum strip_assume_tac \\ drule_first \\
  qpat_x_assum ‘compile_array_read _ _ _ _ p = _’ (assume_tac o GSYM) \\
  drule_first \\ simp [] \\ strip_tac \\ rpt strip_tac
  THEN2 (fs [vwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
  >- simp [vnwrites_def]
  >- simp [no_array_read_dyn_def]
  >- (simp [Once vertype_stmt_cases] \\ match_mp_tac vertype_stmt_extend_tmpvardecls \\ rpt asm_exists_tac)
  >- metis_tac [tmpvars_extend_trans]
  >- (fs [array_rel_filled_prun_def, prun_def, sum_bind_INR] \\ rpt strip_tac \\
      drule_last \\ drule_first \\ impl_tac >- metis_tac [vertype_stmt_prun] \\ simp []))

 >- (* IfElse *)
 (rpt disch_tac \\ rpt gen_tac \\ simp_tac (srw_ss()) [LET_THM] \\
  rpt (pairarg_tac \\ asm_rewrite_tac [] \\ simp_tac (srw_ss()) []) \\ rpt strip_tac' \\ rveq \\
  qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
  drule_strip (REWRITE_RULE [array_read_exp_rel_def] compile_array_read_exp_correct) \\
  qpat_x_assum ‘compile_array_read_exp _ _ _ _ _ = _’ (assume_tac o SYM) \\
  last_x_assum strip_assume_tac \\
  drule_first \\ impl_tac >- decide_tac \\ strip_tac \\
  qpat_x_assum ‘compile_array_read _ _ _ _ p = _’ (assume_tac o SYM) \\
  drule_first \\ impl_tac >- decide_tac \\ strip_tac \\ rw []
  >- (match_mp_tac vwrites_compile_array_read_newvars_subset_trans_lem \\
      rw [pred_setTheory.UNION_SUBSET]
      >- (fs [vwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
      \\ drule_strip newvars_tmps_subset_tmpvarwrites \\
         fs [pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
  >- (irule vwrites_compile_array_read_newvars_preserve_lem \\ fs [vwrites_def] \\ fs [pred_setTheory.SUBSET_DEF])
  >- simp [vnwrites_compile_array_read_newvars, vnwrites_def]
  >- (dep_rewrite.DEP_REWRITE_TAC [no_array_read_dyn_compile_array_read_newvars] \\ simp [no_array_read_dyn_def] \\ asm_exists_tac)
  >- (match_mp_tac vertype_stmt_compile_array_read_newvars \\ rw [Once vertype_stmt_cases]
      >- (match_mp_tac vertype_exp_extend_tmpvardecls \\ asm_exists_tac \\ metis_tac [tmpvars_extend_trans])
      >- (match_mp_tac vertype_stmt_extend_tmpvardecls \\ asm_exists_tac \\ simp [])
      >- (match_mp_tac newvars_inv_tmpvars_extend \\ asm_exists_tac \\ metis_tac [tmpvars_extend_trans])
      >- (match_mp_tac newvars_subset_tmpvars_extend \\ asm_exists_tac \\ metis_tac [tmpvars_extend_trans]))
  >- metis_tac [tmpvars_extend_trans] \\
  fs [array_rel_filled_prun_def, prun_def, sum_bind_INR] \\ rpt strip_tac \\
  drule_strip newvars_inv_runtime_lengths \\
  drule_strip prun_compile_array_read_newvars \\
  first_x_assum (qspec_then ‘IfElse c' l' r'’ strip_assume_tac) \\
  drule_last \\
  simp [prun_def] \\
  fs [get_VBool_data_INR, get_VBool_data_def, sum_bind_def] \\
  IF_CASES_TAC \\ fs [array_rel_filled_prun_def] \\ metis_tac [])

 >- (* Case *)
 (rpt strip_tac' \\
  qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
  qpat_x_assum ‘LET _ _ = _’ mp_tac \\
  rewrite_tac [LET_THM] \\ pairarg_tac \\ drule_strip compile_array_read_exp_correct \\

  asm_rewrite_tac [] \\ CONV_TAC (DEPTH_CONV PairedLambda.PAIRED_BETA_CONV) \\
  pairarg_tac \\ qpat_x_assum ‘compile_array_read_exp _ _ _ _ _ = _’ (assume_tac o SYM) \\
  drule_first \\ impl_tac >- simp [] \\ strip_tac \\

  asm_rewrite_tac [] \\ CONV_TAC (DEPTH_CONV PairedLambda.PAIRED_BETA_CONV) \\
  pairarg_tac \\ qpat_x_assum ‘compile_array_read_case_list _ _ _ _ _ = _’ (assume_tac o SYM) \\
  drule_first \\ impl_tac >- simp [] \\ strip_tac \\

  rw [] \\ simp []
  >- (match_mp_tac vwrites_compile_array_read_newvars_subset_trans_lem \\
      reverse (rw [pred_setTheory.UNION_SUBSET])
      >- (drule_strip newvars_tmps_subset_tmpvarwrites \\ fs [pred_setTheory.SUBSET_DEF] \\
          metis_tac [tmpvarwrites_tmpvars_extend]) \\
      match_mp_tac vwrites_compile_array_read_newvars_subset_trans_lem \\
      rw [pred_setTheory.UNION_SUBSET]
      >- (drule_strip OPTREL_subset_vwrites \\ drule_strip LIST_REL_subset_pair_vwrites \\
          fs [vwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
      >- (imp_res_tac newvars_tmps_subset_tmpvarwrites \\ fs [pred_setTheory.SUBSET_DEF] \\
          metis_tac [tmpvarwrites_tmpvars_extend]))
  >- (rpt (match_mp_tac vwrites_compile_array_read_newvars_preserve_lem) \\
      drule_strip OPTREL_preserve_vwrites \\ drule_strip LIST_REL_preserve_pair_vwrites \\
      fs [vwrites_def] \\ fs [pred_setTheory.INSERT_DEF, pred_setTheory.SUBSET_DEF])
  >- (drule_strip OPTREL_vnwrites \\ drule_strip LIST_REL_pair_vnwrites \\
      simp [vnwrites_compile_array_read_newvars, vnwrites_def])
  >- (dep_rewrite.DEP_REWRITE_TAC [no_array_read_dyn_compile_array_read_newvars] \\
      simp [PULL_EXISTS] \\ rpt asm_exists_tac \\
      asm_simp_tac (srw_ss()++boolSimps.ETA_ss) [no_array_read_dyn_def])
  >- (match_mp_tac vertype_stmt_compile_array_read_newvars \\
      reverse (rpt conj_tac)
      >- metis_tac [newvars_subset_tmpvars_extend]
      >- metis_tac [newvars_inv_tmpvars_extend] \\
      match_mp_tac vertype_stmt_compile_array_read_newvars \\
      reverse (rpt conj_tac)
      >- metis_tac [newvars_subset_tmpvars_extend]
      >- metis_tac [newvars_inv_tmpvars_extend] \\
      simp [Once vertype_stmt_cases] \\
      conj_tac >- metis_tac [vertype_exp_extend_tmpvardecls] \\
      irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ PairCases \\ simp [] \\
      metis_tac [vertype_exp_extend_tmpvardecls, vertype_stmt_extend_tmpvardecls])
  >- metis_tac [tmpvars_extend_trans] \\
  simp [array_rel_filled_prun_def] \\ rpt strip_tac' \\
  simp [GSYM compile_array_read_newvars_append] \\
  qspecl_then [‘s2’, ‘s1’, ‘tmpnumstart’, ‘tmpnum'³'’, ‘extenv’, ‘tmps'³'’, ‘decls’, ‘fext’,
               ‘newvars2 ++ newvars1’, ‘Case t m' cs' d'’]
              mp_tac prun_compile_array_read_newvars \\
  impl_tac >- (simp [] \\ rpt conj_tac
  >- (simp [newvars_inv_newvars_append] \\ metis_tac [newvars_inv_tmpvars_extend])
  >- (simp [ALL_DISTINCT_APPEND] \\ rpt strip_tac \\ fs [EVERY_MEM] \\ rpt drule_first \\ fs [])
  >- (simp [] \\ metis_tac [newvars_subset_tmpvars_extend])
  >- drule_strip newvars_inv_runtime_lengths
  >- (match_mp_tac newvars_inv_runtime_lengths \\ rpt asm_exists_tac)) \\
  strip_tac \\ simp [] \\
  drule_strip prun_Case_cong_array_read \\ simp [])

 THEN2 (* BlockingAssign and NonBlockingAssign *)
 (simp [] \\ strip_tac \\
  TRY (drule_strip vertype_stmt_BlockingAssign_vertype_exp_rhs) \\
  TRY (drule_strip vertype_stmt_NonBlockingAssign_vertype_exp_rhs) \\
  pairarg_tac \\ drule_strip compile_array_read_exp_opt_correct \\ fs [] \\ rveq \\ rpt conj_tac \\ simp []
  >- (match_mp_tac vwrites_compile_array_read_newvars_subset_trans_lem \\ rw [pred_setTheory.UNION_SUBSET]
      >- simp [vwrites_def]
      \\ drule_strip newvars_tmps_subset_tmpvarwrites \\ fs [pred_setTheory.SUBSET_DEF])
  >- (match_mp_tac vwrites_compile_array_read_newvars_preserve_lem \\ simp [vwrites_def])
  >- simp [vnwrites_compile_array_read_newvars, vnwrites_def]
  >- (drule_strip no_array_read_dyn_compile_array_read_newvars \\ simp [no_array_read_dyn_def])
  >- (match_mp_tac vertype_stmt_compile_array_read_newvars \\
      Cases_on ‘rhs’ \\ Cases_on ‘rhs'’ \\ fs [Once vertype_stmt_cases] \\
      fs [Ev_from_decls_def, alist_to_map_alookup, alistTheory.ALOOKUP_APPEND] \\
      metis_tac [vertype_exp_extend, vertype_exp_deterministic]) \\
  simp [array_rel_filled_prun_def] \\ rpt strip_tac' \\
  drule_strip newvars_inv_runtime_lengths \\
  drule_strip prun_compile_array_read_newvars \\
  qmatch_goalsub_abbrev_tac ‘compile_array_read_newvars _ e’ \\
  first_x_assum (qspec_then ‘e’ strip_assume_tac) \\
  unabbrev_all_tac \\ fs [prun_def, sum_bind_INR] \\
  rename1 ‘prun_assn_rhs _ _ _ rhs = INR v’ \\ PairCases_on ‘v’ \\ fs [] \\
  drule_strip array_read_exp_rel_prun_assn_rhs \\
  TRY (drule_strip array_rel_prun_bassn) \\
  TRY (drule_strip array_rel_prun_nbassn) \\
  simp [])

 >- (* NONE *)
 (rw [] \\ simp [])

 >- (* SOME *)
 (simp [] \\ rpt strip_tac' \\ pairarg_tac \\ drule_first \\ fs [] \\ rveq \\ simp [])

 >- (* list base *)
 (rw [] \\ simp [newvars_inv_def])

 >- (* list step *)
 (strip_tac \\ simp_tac (srw_ss()) [] \\ rpt strip_tac' \\
  qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\
  drule_strip compile_array_read_exp_correct \\
  asm_rewrite_tac [] \\
  qpat_x_assum ‘compile_array_read_exp _ _ _ _ _ = _’ (assume_tac o SYM) \\
  simp_tac (srw_ss()) [] \\ pairarg_tac \\
  drule_first \\ impl_tac >- simp [] \\ strip_tac \\
  asm_rewrite_tac [] \\
  qpat_x_assum ‘compile_array_read _ _ _ _ _ = _’ (assume_tac o SYM) \\
  simp_tac (srw_ss()) [] \\ pairarg_tac \\
  drule_first \\ impl_tac >- simp [] \\ rw [] \\ simp []
  >- (fs [pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
  >- (conj_tac
      >- (match_mp_tac vertype_exp_extend_tmpvardecls \\ asm_exists_tac \\ metis_tac [tmpvars_extend_trans])
      >- (match_mp_tac vertype_stmt_extend_tmpvardecls \\ rpt asm_exists_tac))
  >- metis_tac [tmpvars_extend_trans]
  >- (simp [newvars_inv_newvars_append] \\ metis_tac [newvars_inv_tmpvars_extend])
  >- metis_tac [newvars_subset_tmpvars_extend]
  >- (conj_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [])
  >- (simp [ALL_DISTINCT_APPEND] \\ rpt strip_tac \\ fs [EVERY_MEM] \\ rpt drule_first \\ fs []) \\
  conj_tac
  >- (fs [array_read_exp_rel_def] \\ rpt strip_tac \\ drule_first)
  \\ irule LIST_REL_mono \\ asm_exists_any_tac \\ rw [array_read_exp_rel_def] \\ drule_first)
QED

Theorem writes_ok_tl:
 ∀p ps. writes_ok (p::ps) ⇒ writes_ok ps
Proof
 simp [writes_ok_def] \\ metis_tac []
QED

Theorem writes_ok_set:
 ∀ps. writes_ok ps ⇔ DISJOINT (set (FLAT (MAP vwrites ps))) (set (FLAT (MAP vnwrites ps)))
Proof
 simp [pred_setTheory.DISJOINT_ALT, writes_ok_def] \\ metis_tac []
QED

Theorem vertype_stmt_vnwrites_decls_type:
 ∀extenv decls var p.
 vertype_stmt extenv (Ev_from_decls decls) p ⇒ MEM var (vnwrites p) ⇒ ∃t. decls_type decls var = INR t
Proof
 ntac 3 gen_tac \\ ho_match_mp_tac vertype_stmt_ind \\ simp [vnwrites_def, evwrites_def] \\
 rpt conj_tac \\ rpt strip_tac'
 THEN4 metis_tac []
 >- (fs [EVERY_MEM, MEM_FLAT, MEM_MAP] \\ pairarg_tac \\ drule_first \\ rveq \\ fs [])
 >- (every_case_tac \\ fs [])
 \\ fs [Ev_from_decls_def, alist_to_map_alookup, decls_type_sum_alookup, sum_alookup_INR]
QED

Triviality vertype_stmt_vnwrites_tmpvarwrites:
 ∀extenv decls p tmpnumstart tmpnum tmps.
 vertype_stmt extenv (Ev_from_decls decls) p ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_range tmpnumstart tmpnum tmps ⇒
 DISJOINT (set (vnwrites p)) (tmpvarwrites tmps)
Proof
 rw [pred_setTheory.DISJOINT_ALT, fresh_tmpvar_decls_def, tmpvars_range_def] \\
 drule_strip vertype_stmt_vnwrites_decls_type \\
 strip_tac \\ fs [tmpvarwrites_def, MEM_MAP, EVERY_MEM] \\ drule_first \\ pairarg_tac \\ fs [] \\ rveq \\
 drule_first \\ fs []
QED

Triviality LIST_REL_vnwrites:
 ∀ps ps'. LIST_REL (λp p'. vnwrites p' = vnwrites p) ps ps' ⇒ MAP vnwrites ps' = MAP vnwrites ps
Proof
 ho_match_mp_tac LIST_REL_ind \\ simp []
QED

Triviality LIST_REL_vwrites:
 ∀newwrites ps ps'.
 LIST_REL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ newwrites) ps ps' ⇒
 set (FLAT (MAP vwrites ps')) ⊆ set (FLAT (MAP vwrites ps)) ∪ newwrites
Proof
 gen_tac \\ ho_match_mp_tac LIST_REL_ind \\ simp [pred_setTheory.SUBSET_DEF] \\ metis_tac []
QED

Triviality EVERY_vnwrites_disjoint:
 ∀ps newwrites.
 EVERY (λp. DISJOINT (set (vnwrites p)) newwrites) ps ⇒ DISJOINT (set (FLAT (MAP vnwrites ps))) newwrites
Proof
 Induct \\ simp []
QED

Theorem writes_ok_read_lem:
 ∀ps ps' newwrites.
 writes_ok ps ∧
 LIST_REL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ newwrites) ps ps' ∧
 LIST_REL (λp p'. vnwrites p' = vnwrites p) ps ps' ∧
 EVERY (λp. DISJOINT (set (vnwrites p)) newwrites) ps ⇒
 writes_ok ps'
Proof
 rewrite_tac [writes_ok_set] \\ rpt strip_tac \\
 drule_strip LIST_REL_vnwrites \\ fs [] \\
 drule_strip LIST_REL_vwrites \\
 drule_strip EVERY_vnwrites_disjoint \\
 fs [pred_setTheory.DISJOINT_ALT, pred_setTheory.SUBSET_DEF] \\ metis_tac []
QED

Theorem compile_array_read_list_correct:
 !ps ps' decls extenv tmpnum tmpnum' tmpnumstart tmps tmps'.
 compile_array_read_list decls extenv tmpnum tmps ps = (tmpnum', tmps', ps') ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 EVERY (vertype_stmt extenv (Ev_from_decls decls)) ps ∧
 writes_ok ps ∧
 tmpnumstart ≤ tmpnum ⇒
 tmpnum ≤ tmpnum' ∧
 LIST_REL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps') ps ps' ∧
 LIST_REL (λp p'. set (vwrites p) ⊆ set (vwrites p')) ps ps' ∧
 LIST_REL (λp p'. vnwrites p' = vnwrites p) ps ps' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧
 EVERY (vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps'))) ps' ∧
 EVERY (no_array_read_dyn (Ev_from_decls decls) extenv) ps' ∧
 writes_ok ps' ∧
 (!fext s1 s1' s2.
  sum_foldM (prun fext) s1 ps = INR s1' ∧ array_rel s1 s2 ∧
  vertype_env (Ev_from_decls decls) s1 ∧
  vertype_env_filled (Ev_from_decls decls) s1 ∧
  vertype_fext_n extenv fext ⇒
  ?s2'. sum_foldM (prun fext) s2 ps' = INR s2' /\
        array_rel s1' s2')
Proof
 Induct \\ simp_tac bool_ss [compile_array_read_list_def, LET_THM] >- simp [sum_foldM_def] \\
 rpt gen_tac \\
 rpt (pairarg_tac \\ asm_rewrite_tac [] \\ CONV_TAC (DEPTH_CONV PairedLambda.PAIRED_BETA_CONV)) \\
 rpt strip_tac' \\ fs [] \\ rveq \\

 drule_strip (CONJUNCT1 compile_array_read_correct) \\
 drule_strip writes_ok_tl \\ drule_first \\ simp [] \\ rpt strip_tac' \\
 conj_asm1_tac
 >- (fs [pred_setTheory.SUBSET_DEF] \\ rpt strip_tac \\ drule_first \\ simp [] \\
     drule_strip tmpvarwrites_tmpvars_extend \\ simp []) \\
 rpt strip_tac
 >- metis_tac [tmpvars_extend_trans]
 >- metis_tac [vertype_stmt_extend_tmpvardecls]
 >- (match_mp_tac writes_ok_read_lem \\ qexistsl_tac [‘h::ps’, ‘tmpvarwrites tmps'’] \\
     fs [EVERY_MEM] \\ metis_tac [vertype_stmt_vnwrites_tmpvarwrites]) \\
 fs [sum_foldM_INR, array_rel_filled_prun_def] \\ drule_last \\ drule_first \\ metis_tac [vertype_stmt_prun]
QED

(** Preprocess dynamic array write behavior proof **)

Theorem prun_code_for_BlockingAssign_Indexing_write:
 !s e fext ie i oldvar tmpvar_ bs b t.
 erun fext s e = INR (VArray ie) /\
 ver2n (VArray ie) = INR i /\
 i < LENGTH bs /\
 get_use_nbq_var s F oldvar = INR (VArray bs) /\
 get_var s tmpvar_ = INR (VBool b) ==>
 ?s'. prun fext s (Case t e (GENLIST (λi. (Const (n2VArray (LENGTH ie) i),
                                           BlockingAssign
                                           (Indexing oldvar (LENGTH ie) (Const (n2VArray (LENGTH ie) i)))
                                           (SOME (Var tmpvar_))))
                            (MIN (LENGTH bs) (2**(LENGTH ie))))
                            NONE) = INR s' /\
      s'.fbits = s.fbits /\
      (!var. get_var s' var = if var = oldvar then INR (VArray $ revLUPDATE b i bs) else get_var s var) ∧
      (∀var. get_nbq_var s' var = get_nbq_var s var)
Proof
 rpt strip_tac \\ dep_rewrite.DEP_REWRITE_TAC [prun_Case_GENLIST] \\ conj_tac >- simp [ver2n_lt] \\
 simp [prun_def, prun_assn_rhs_def, erun_def, erun_get_var_def, sum_map_def, sum_bind_def,
       prun_bassn_def, assn_def, ver2n_n2VArray, get_VArray_data_def, get_VBool_data_def,
       prun_set_var_index_def] \\
 simp [set_index_LUPDATE, sum_for_def, sum_map_def] \\
 rw [set_var_fbits, get_var_cleanup, revLUPDATE_def]
QED

Theorem prun_code_for_NonBlockingAssign_Indexing_write:
 !s e fext ie i oldvar tmpvar_ bs b t.
 erun fext s e = INR (VArray ie) /\
 ver2n (VArray ie) = INR i /\
 i < LENGTH bs /\
 get_use_nbq_var s T oldvar = INR (VArray bs) /\
 get_var s tmpvar_ = INR (VBool b) ==>
 ?s'. prun fext s (Case t e (GENLIST (λi. (Const (n2VArray (LENGTH ie) i),
                                           NonBlockingAssign
                                           (Indexing oldvar (LENGTH ie) (Const (n2VArray (LENGTH ie) i)))
                                           (SOME (Var tmpvar_))))
                            (MIN (LENGTH bs) (2**(LENGTH ie))))
                            NONE) = INR s' /\
      s'.fbits = s.fbits /\
      (!var. get_nbq_var s' var = if var = oldvar then INR (VArray $ revLUPDATE b i bs) else get_nbq_var s var) ∧
      (∀var. get_var s' var = get_var s var)
Proof
 rpt strip_tac \\ dep_rewrite.DEP_REWRITE_TAC [prun_Case_GENLIST] \\ conj_tac >- simp [ver2n_lt] \\
 simp [prun_def, prun_assn_rhs_def, erun_def, erun_get_var_def, sum_map_def, sum_bind_def,
       prun_nbassn_def, assn_def, ver2n_n2VArray, get_VArray_data_def, get_VBool_data_def,
       prun_set_var_index_def] \\
 simp [set_index_LUPDATE, sum_for_def, sum_map_def] \\
 rw [set_nbq_var_fbits, get_var_cleanup, revLUPDATE_def]
QED

Triviality LIST_REL_pair_subset_writes:
 ∀f ps ps'.
 LIST_REL (λ(_, p) (_, p'). set (f p') ⊆ set (f p)) ps ps' ⇒
 set (FLAT (MAP (λ(_, p). f p) ps')) ⊆ set (FLAT (MAP (λ(_, p). f p) ps))
Proof
 gen_tac \\ ho_match_mp_tac LIST_REL_ind \\ simp [] \\ rpt strip_tac' \\ rpt (pairarg_tac \\ fs []) \\
 fs [pred_setTheory.SUBSET_DEF]
QED

Triviality OPTREL_subset_writes:
 ∀f p p'.
 OPTREL (λp p'. set (f p') ⊆ set (f p)) p p' ⇒
 set (case p' of NONE => [] | SOME p => f p) ⊆ set (case p of NONE => [] | SOME p => f p)
Proof
 gen_tac \\ Cases \\ Cases \\ simp []
QED

Theorem prun_Case_cong_array_write:
 ∀t m ps ps' d d' s1 s1' s2 fext extenv (decls : declty).
 prun fext s1 (Case t m ps d) = INR s1' ∧
 array_rel s1 s2 ∧
 vertype_env (Ev_from_decls decls) s1 ∧
 vertype_fext_n extenv fext ∧
 MAP FST ps' = MAP FST ps ∧
 LIST_REL (array_rel_prun extenv decls) (MAP SND ps) (MAP SND ps') ∧
 OPTREL (array_rel_prun extenv decls) d d' ⇒
 ∃s2'. prun fext s2 (Case t m ps' d') = INR s2' ∧ array_rel s1' s2'
Proof
 Induct_on ‘ps’ \\ Cases_on ‘ps'’ \\ simp []
 >- (Cases_on ‘d’ \\ Cases_on ‘d'’ \\ simp [prun_def, array_rel_prun_def] \\
     rpt strip_tac \\ drule_first \\ simp []) \\
 PairCases \\ PairCases_on ‘h’ \\
 rw [prun_def, sum_bind_INR] \\
 imp_res_tac array_rel_erun \\ simp [] \\
 IF_CASES_TAC \\ fs []
 >- (fs [array_rel_prun_def] \\ drule_first \\ simp [])
 \\ metis_tac []
QED

Theorem flat_genlist_nil:
 ∀n. FLAT (GENLIST (λi. []) n) = []
Proof
 Induct \\ simp [GENLIST]
QED

Theorem flat_genlist_sing:
 ∀n var. set (FLAT (GENLIST (λi. [var]) n)) ⊆ {var}
Proof
 Induct \\ simp [GENLIST, rich_listTheory.FLAT_SNOC]
QED

Theorem new_tmpnum_not_in_decls:
 ∀decls var t tmpnumstart tmpnum.
 decls_type decls var = INR t ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpnumstart ≤ tmpnum ⇒
 var ≠ tmpvar tmpnum
Proof
 rpt strip_tac \\ fs [fresh_tmpvar_decls_def]
QED

Theorem get_use_nbq_var_set_var_new_var:
 ∀b var1 var2 s1 s2 v v'.
 get_use_nbq_var s1 b var1 = INR v ∧
 array_rel s1 s2 ∧
 var1 ≠ var2 ⇒
 get_use_nbq_var (set_var s2 var2 v') b var1 = INR v
Proof
 Cases \\ rpt gen_tac \\ simp [get_use_nbq_var_def, array_rel_def] \\ TRY CASE_TAC \\ simp [get_var_cleanup]
QED

Theorem compile_array_write_correct:
 (!decls tmpnum tmps p tmpnumstart extenv tmpnum' tmps' p'.
 compile_array_write decls tmpnum tmps p = (tmpnum', tmps', p') ∧
 vertype_stmt extenv (Ev_from_decls decls) p ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ∧
 no_array_read_dyn (Ev_from_decls decls) extenv p ⇒
 tmpnum ≤ tmpnum' ∧
 set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps' ∧
 (*set (vwrites p) ⊆ set (vwrites p') ∧*)
 set (vnwrites p') ⊆ set (vnwrites p) ∧
 no_array_read_dyn (Ev_from_decls decls) extenv p' ∧
 no_array_write_dyn (Ev_from_decls decls) p' ∧
 vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) p' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧
 array_rel_prun extenv decls p p')
 ∧
 (!decls tmpnum tmps p tmpnumstart extenv tmpnum' tmps' p'.
 compile_array_write_opt decls tmpnum tmps p = (tmpnum', tmps', p') ∧
 OPTION_ALL (vertype_stmt extenv (Ev_from_decls decls)) p ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ∧
 OPTION_ALL (no_array_read_dyn (Ev_from_decls decls) extenv) p ⇒
 tmpnum ≤ tmpnum' ∧
 OPTREL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps') p p' ∧
 (*OPTREL (λp p'. set (vwrites p) ⊆ set (vwrites p')) p p' ∧*)
 OPTREL (λp p'. set (vnwrites p') ⊆ set (vnwrites p)) p p' ∧
 OPTION_ALL (no_array_read_dyn (Ev_from_decls decls) extenv) p' ∧
 OPTION_ALL (no_array_write_dyn (Ev_from_decls decls)) p' ∧
 OPTION_ALL (vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps'))) p' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧
 OPTREL (array_rel_prun extenv decls) p p')
 ∧
 (!decls tmpnum tmps ps tmpnumstart extenv tmpnum' tmps' ps' t.
 compile_array_write_case_list decls tmpnum tmps ps = (tmpnum', tmps', ps') ∧
 EVERY (λ(e, p). vertype_exp extenv (Ev_from_decls decls) e t ∧
                 vertype_stmt extenv (Ev_from_decls decls) p) ps ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ∧
 EVERY (λ(e, p). no_array_read_dyn_exp (Ev_from_decls decls) extenv e ∧
                 no_array_read_dyn (Ev_from_decls decls) extenv p) ps ⇒
 tmpnum ≤ tmpnum' ∧
 LIST_REL (λ(_, p) (_, p'). set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps') ps ps' ∧
 (*LIST_REL (λ(_, p) (_, p'). set (vwrites p) ⊆ set (vwrites p')) ps ps' ∧*)
 LIST_REL (λ(_, p) (_, p'). set (vnwrites p') ⊆ set (vnwrites p)) ps ps' ∧
 EVERY (λ(e, p). no_array_read_dyn_exp (Ev_from_decls decls) extenv e ∧
                 no_array_read_dyn (Ev_from_decls decls) extenv p) ps' ∧
 EVERY (no_array_write_dyn (Ev_from_decls decls)) (MAP SND ps') ∧
 EVERY (λ(e, p). vertype_exp extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) e t ∧
                 vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) p) ps' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧
 MAP FST ps' = MAP FST ps ∧
 LIST_REL (array_rel_prun extenv decls) (MAP SND ps) (MAP SND ps'))
Proof
 ho_match_mp_tac compile_array_write_ind \\ rewrite_tac [compile_array_write_def] \\
 rpt conj_tac \\ rpt gen_tac

 >- (* Seq *)
 (rewrite_tac [no_array_read_dyn_def] \\ rpt strip_tac' \\
  qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
  qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\ drule_first \\
  asm_rewrite_tac [] \\ simp_tac (srw_ss()) [] \\
  qpat_x_assum ‘compile_array_write _ _ _ p = _’ (assume_tac o SYM) \\ pairarg_tac \\ drule_first \\
  simp [] \\ rpt strip_tac \\ rveq \\ simp []
  >- (fs [vwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
  >- (fs [vnwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [])
  >- simp [no_array_read_dyn_def]
  >- simp [no_array_write_dyn_def]
  >- (simp [Once vertype_stmt_cases] \\ match_mp_tac vertype_stmt_extend_tmpvardecls \\ rpt asm_exists_tac)
  >- metis_tac [tmpvars_extend_trans]
  >- (fs [array_rel_prun_def, prun_def, sum_bind_INR] \\ rpt strip_tac \\
      drule_last \\ drule_first \\ impl_tac >- metis_tac [vertype_stmt_prun] \\ simp []))

 >- (* IfElse *)
 (rewrite_tac [no_array_read_dyn_def] \\ rpt strip_tac' \\
  qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
  qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\ drule_first \\
  asm_rewrite_tac [] \\ simp_tac (srw_ss()) [] \\
  qpat_x_assum ‘compile_array_write _ _ _ p = _’ (assume_tac o SYM) \\ pairarg_tac \\ drule_first \\
  simp [] \\ rpt strip_tac \\ rveq \\ simp []
  >- (fs [vwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
  >- (fs [vnwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [])
  >- simp [no_array_read_dyn_def]
  >- simp [no_array_write_dyn_def]
  >- (simp [Once vertype_stmt_cases] \\
      metis_tac [vertype_exp_extend_Ev_from_decls, vertype_stmt_extend_tmpvardecls])
  >- metis_tac [tmpvars_extend_trans]
  >- (fs [array_rel_prun_def, prun_def, sum_bind_INR] \\ rpt strip_tac \\
      drule_strip array_rel_erun \\ fs [get_VBool_data_INR] \\
      IF_CASES_TAC \\ fs [] \\ drule_first \\ metis_tac [vertype_stmt_prun]))

 >- (* Case *)
 (rewrite_tac [no_array_read_dyn_def] \\ rpt strip_tac' \\
  qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
  qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\ drule_first \\
  asm_rewrite_tac [] \\ simp_tac (srw_ss()) [] \\
  qpat_x_assum ‘compile_array_write_case_list _ _ _ _ = _’ (assume_tac o SYM) \\ pairarg_tac \\ drule_first \\
  impl_tac >- (simp [] \\ full_simp_tac (srw_ss()++boolSimps.ETA_ss) []) \\
  strip_tac \\ simp [] \\ strip_tac \\ rveq \\ rpt strip_tac \\ simp []
  >- (drule_strip OPTREL_subset_vwrites \\ drule_strip LIST_REL_subset_pair_vwrites \\
      fs [vwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
  >- (drule_strip OPTREL_subset_writes \\ drule_strip LIST_REL_pair_subset_writes \\
      simp [vnwrites_def] \\ fs [pred_setTheory.SUBSET_DEF])
  >- asm_simp_tac (srw_ss()++boolSimps.ETA_ss) [no_array_read_dyn_def]
  >- asm_simp_tac (srw_ss()++boolSimps.ETA_ss) [no_array_write_dyn_def]
  >- (simp [Once vertype_stmt_cases] \\ conj_tac
      >- (match_mp_tac vertype_exp_extend_Ev_from_decls \\ simp [])
      >- (irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ PairCases \\ simp [] \\
          metis_tac [vertype_exp_extend_tmpvardecls, vertype_stmt_extend_tmpvardecls]))
  >- metis_tac [tmpvars_extend_trans]
  >- (simp [array_rel_prun_def] \\ rpt strip_tac \\ drule_strip prun_Case_cong_array_write \\ simp []))

 THEN2 (* BlockingAssign+NonBlockingAssign Indexing *)
 (rpt strip_tac' \\
  qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
  qpat_x_assum ‘sum_CASE _ _ _ = _’ mp_tac \\
  TOP_CASE_TAC >- fs [Ev_from_decls_decls_type] \\ TOP_CASE_TAC >- fs [Ev_from_decls_decls_type] \\ TOP_CASE_TAC
  >-
  (rw [compile_array_write_prog_assn_def]
   >- (simp [vwrites_def, evwrites_def, tmpvarwrites_def, MAP_GENLIST, combinTheory.o_DEF] \\
       rw [pred_setTheory.SUBSET_DEF] \\ fs [mem_flat_genlist_nil] \\
       drule_strip mem_flat_genlist_sing \\ simp [])
   >- simp [vnwrites_def, MAP_GENLIST, combinTheory.o_DEF, evwrites_def, flat_genlist_nil, flat_genlist_sing]
   >- (fs [no_array_read_dyn_def, no_array_read_dyn_exp_def, EVERY_GENLIST] \\
       drule_strip vertype_exp_array_no_array_read_dyn_exp)
   >- (simp [no_array_write_dyn_def, MAP_GENLIST, EVERY_GENLIST, get_const_def, sum_bind_def,
             ver2n_n2VArray_lem, tenv_type_def] \\
       fs [Ev_from_decls_decls_type])
   >- (simp [Once vertype_stmt_cases] \\ conj_tac
       >- (simp [Once vertype_stmt_cases] \\
           fs [Ev_from_decls_decls_type, fresh_tmpvar_decls_def, decls_type_append] \\
           simp [decls_type_tmpvardecls, sum_alookup_cons] \\
           simp [vertype_exp_extend_Ev_from_decls])
       >- (simp [Once vertype_stmt_cases, EVERY_GENLIST] \\ fs [Ev_from_decls_decls_type] \\ rveq \\ rpt strip_tac
           >- simp [vertype_exp_extend_Ev_from_decls]
           >- simp [Once vertype_exp_cases, vertype_v_n2VArray]
           >- (simp [Once vertype_stmt_cases] \\
               fs [Ev_from_decls_decls_type, fresh_tmpvar_decls_def, decls_type_append] \\
               conj_tac \\ simp [Once vertype_exp_cases, vertype_v_n2VArray] \\
               simp [Ev_from_decls_decls_type, decls_type_append, decls_type_tmpvardecls, sum_alookup_cons])))
   >- (drule_strip tmpvars_distinct_tmpvars_range \\ simp [])
   >- simp [tmpvars_range_cons]
   >- (drule_strip tmpvars_range_tmpvars_extend \\ simp [])
   >- (simp [array_rel_prun_def] \\ fs [Ev_from_decls_decls_type] \\ rveq \\

       simp [prun_def, prun_assn_rhs_def, sum_bind_INR, sum_map_INR] \\ rpt strip_tac \\ rveq \\
       fs [prun_bassn_def, prun_nbassn_def, sum_for_INR] \\ rveq \\
       fs [assn_def, sum_for_def, sum_map_def, sum_bind_INR] \\
       imp_res_tac array_rel_erun \\ simp [] \\
       fs [ver2n_INR] \\ rveq \\ pairarg_tac \\ fs [prun_set_var_index_INR] \\ rveq \\
       fs [(*get_use_nbq_var_def,*) get_VArray_data_INR, get_VBool_data_INR] \\
       qmatch_goalsub_abbrev_tac ‘prun _ s2' _’ \\

       TRY (rename1 ‘BlockingAssign’ \\
            qspecl_then [‘s2'’, ‘i’, ‘fext’, ‘bs’, ‘name’, ‘tmpvar tmpnum’, ‘vd’, ‘rhse’, ‘VArray_t ilen’] mp_tac
                        (SIMP_RULE (srw_ss()) [ver2n_VArray] prun_code_for_BlockingAssign_Indexing_write)) \\

       TRY (rename1 ‘NonBlockingAssign’ \\
            qspecl_then [‘s2'’, ‘i’, ‘fext’, ‘bs’, ‘name’, ‘tmpvar tmpnum’, ‘vd’, ‘rhse’, ‘VArray_t ilen’] mp_tac
                        (SIMP_RULE (srw_ss()) [ver2n_VArray] prun_code_for_NonBlockingAssign_Indexing_write)) \\

       unabbrev_all_tac \\
       impl_tac >- (rpt conj_tac \\ simp [get_var_cleanup]
                    >- (match_mp_tac erun_cong_INR_type \\ rpt asm_exists_tac \\ rpt strip_tac \\
                        rw [get_var_set_var] \\ fs [fresh_tmpvar_decls_def] \\ drule_first \\ fs [])
                    >- (drule_strip new_tmpnum_not_in_decls \\
                        drule_strip get_use_nbq_var_set_var_new_var \\ simp [])) \\ strip_tac \\
       qspecl_then [‘i’, ‘s1’] assume_tac vertype_exp_erun \\ drule_first \\
       drule_strip vertype_env_get_use_nbq_var \\ fs [Ev_from_decls_decls_type] \\
       fs [vertype_v_cases] \\ rveq \\ asm_exists_tac \\

       fs [array_rel_def, set_var_fbits, set_nbq_var_fbits, get_var_cleanup, set_index_LUPDATE, revLUPDATE_def] \\
       rw [] \\ drule_strip vertype_env_get_var \\ fs [Ev_from_decls_decls_type, fresh_tmpvar_decls_def] \\
       rpt drule_first \\ fs []))
  >-
  (IF_CASES_TAC
   >- (fs [get_const_INR, is_ok_idx_const_inv] \\ rw [] \\ simp []
       >- (simp [no_array_write_dyn_def, get_const_def, sum_bind_def, ver2n_VArray, tenv_type_def] \\
           fs [Ev_from_decls_decls_type])
       >- (simp [Once vertype_stmt_cases] \\ simp [Ev_from_decls_decls_type, decls_type_append, vertype_exp_extend_Ev_from_decls])
       >- simp [array_rel_prun_refl])
   >- (strip_tac \\ rveq \\ rw [vwrites_def, vnwrites_def, no_array_read_dyn_def, no_array_write_dyn_def]
       >- simp [Once vertype_stmt_cases]
       >- (qpat_x_assum ‘vertype_exp _ _ i _’ mp_tac \\ fs [get_const_INR] \\
           simp [Once vertype_exp_cases, vertype_v_cases] \\ strip_tac \\ rveq \\
           fs [is_ok_idx_const_def] \\
           simp [array_rel_prun_def, prun_def, prun_assn_rhs_def, prun_bassn_def, prun_nbassn_def, assn_def, erun_def,
                 sum_bind_INR, sum_map_INR, sum_for_INR] \\ rpt strip_tac \\ rveq \\
           fs [sum_for_INR, sum_bind_INR, ver2n_VArray] \\ rveq \\
           pairarg_tac \\ fs [prun_set_var_index_INR, (*get_use_nbq_var_def,*) get_VArray_data_INR] \\ rveq \\
           drule_strip vertype_env_get_use_nbq_var \\ fs [Ev_from_decls_decls_type] \\ rveq \\
           fs [vertype_v_cases]))))

 THEN5 (* other stmts *)
 (rpt strip_tac' \\ fs [] \\ rveq \\
  simp [no_array_write_dyn_def, vertype_stmt_extend_Ev_from_decls, array_rel_prun_refl])

 >- (* NONE *)
 (rw [] \\ simp [])

 >- (* SOME *)
 (simp [] \\ rpt strip_tac' \\ pairarg_tac \\ drule_first \\ fs [] \\ rveq \\ simp [])

 >- (* list base *)
 (rw [] \\ simp [])

 >- (* list step *)
 (strip_tac \\ simp_tac (srw_ss()) [no_array_read_dyn_def] \\ rpt strip_tac' \\
  qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\ drule_first \\
  asm_rewrite_tac [] \\ simp_tac (srw_ss()) [] \\
  qpat_x_assum ‘compile_array_write _ _ _ _ = _’ (assume_tac o SYM) \\ pairarg_tac \\ drule_first \\
  simp [] \\ rpt strip_tac \\ rveq \\ simp []
  >- (fs [pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
  >- metis_tac [vertype_exp_extend_Ev_from_decls, vertype_stmt_extend_tmpvardecls]
  >- metis_tac [tmpvars_extend_trans])
QED

Triviality LIST_REL_subset_vnwrites:
 ∀ps ps'.
 LIST_REL (λp p'. set (vnwrites p') ⊆ set (vnwrites p)) ps ps' ⇒
 set (FLAT (MAP vnwrites ps')) ⊆ set (FLAT (MAP vnwrites ps))
Proof
 ho_match_mp_tac LIST_REL_ind \\ simp [] \\ simp [pred_setTheory.SUBSET_DEF]
QED

Theorem writes_ok_write_lem:
 ∀ps ps' newwrites.
 writes_ok ps ∧
 LIST_REL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ newwrites) ps ps' ∧
 LIST_REL (λp p'. set (vnwrites p') ⊆ set (vnwrites p)) ps ps' ∧
 EVERY (λp. DISJOINT (set (vnwrites p)) newwrites) ps ⇒
 writes_ok ps'
Proof
 rewrite_tac [writes_ok_set] \\ rpt strip_tac \\
 drule_strip LIST_REL_subset_vnwrites \\ fs [] \\
 drule_strip LIST_REL_vwrites \\
 drule_strip EVERY_vnwrites_disjoint \\
 fs [pred_setTheory.DISJOINT_ALT, pred_setTheory.SUBSET_DEF] \\ metis_tac []
QED

Theorem compile_array_write_list_correct:
 !ps ps' decls extenv tmpnum tmpnum' tmpnumstart tmps tmps'.
 compile_array_write_list decls tmpnum tmps ps = (tmpnum', tmps', ps') ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 EVERY (vertype_stmt extenv (Ev_from_decls decls)) ps ∧
 writes_ok ps ∧
 tmpnumstart ≤ tmpnum ∧
 EVERY (no_array_read_dyn (Ev_from_decls decls) extenv) ps ⇒
 tmpnum ≤ tmpnum' ∧
 LIST_REL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps') ps ps' ∧
 (*LIST_REL (λp p'. set (vwrites p) ⊆ set (vwrites p')) ps ps' ∧*)
 LIST_REL (λp p'. set (vnwrites p') ⊆ set (vnwrites p)) ps ps' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧
 EVERY (vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps'))) ps' ∧
 EVERY (no_array_read_dyn (Ev_from_decls decls) extenv) ps' ∧
 EVERY (no_array_write_dyn (Ev_from_decls decls)) ps' ∧
 writes_ok ps' ∧
 (!fext s1 s1' s2.
  sum_foldM (prun fext) s1 ps = INR s1' ∧ array_rel s1 s2 ∧
  vertype_env (Ev_from_decls decls) s1 ∧
  vertype_fext_n extenv fext ⇒
  ?s2'. sum_foldM (prun fext) s2 ps' = INR s2' /\
        array_rel s1' s2')
Proof
 Induct \\ simp_tac (srw_ss()) [compile_array_write_list_def] >- simp [sum_foldM_def] \\
 rpt strip_tac' \\
 qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\
 drule_strip (CONJUNCT1 compile_array_write_correct) \\
 asm_rewrite_tac [] \\ simp_tac (srw_ss()) [] \\ pairarg_tac \\
 drule_strip writes_ok_tl \\ drule_first \\ simp [] \\ ntac 2 strip_tac \\ rveq \\ simp [] \\
 conj_asm1_tac
 >- (fs [pred_setTheory.SUBSET_DEF] \\ rpt strip_tac \\ drule_first \\ simp [] \\
     drule_strip tmpvarwrites_tmpvars_extend \\ simp []) \\
 rpt strip_tac
 >- metis_tac [tmpvars_extend_trans]
 >- metis_tac [vertype_stmt_extend_tmpvardecls]
 >- (match_mp_tac writes_ok_write_lem \\ qexistsl_tac [‘h::ps’, ‘tmpvarwrites tmps'’] \\
     fs [EVERY_MEM] \\ metis_tac [vertype_stmt_vnwrites_tmpvarwrites]) \\
 fs [sum_foldM_INR, array_rel_prun_def] \\ drule_last \\ drule_first \\ metis_tac [vertype_stmt_prun]
QED

(** Preprocess away case-statements into if-statements **)

Theorem vertype_stmt_Ev_from_decls_extend:
 ∀extenv l1 l2 s. vertype_stmt extenv (Ev_from_decls l1) s ⇒ vertype_stmt extenv (Ev_from_decls (l1 ++ l2)) s
Proof
 simp [Ev_from_decls_def, vertype_stmt_extend]
QED

Theorem vertype_exp_Ev_from_decls_extend:
 ∀extenv l1 l2 e t. vertype_exp extenv (Ev_from_decls l1) e t ⇒ vertype_exp extenv (Ev_from_decls (l1 ++ l2)) e t
Proof
 simp [Ev_from_decls_def, vertype_exp_extend]
QED

Theorem vwrites_Case_to_IfElse:
 ∀ps d t m. vwrites (Case_to_IfElse t m ps d) = vwrites (Case t m ps d)
Proof
 Induct \\ Cases \\ simp [Case_to_IfElse_def, vwrites_def]
QED

Theorem vnwrites_Case_to_IfElse:
 ∀ps d t m. vnwrites (Case_to_IfElse t m ps d) = vnwrites (Case t m ps d)
Proof
 Induct \\ Cases \\ simp [Case_to_IfElse_def, vnwrites_def]
QED

Theorem no_array_read_dyn_exp_Case_to_IfElse_eq:
 ∀ty tenv extenv lhs rhs.
 no_array_read_dyn_exp tenv extenv (Case_to_IfElse_eq ty lhs rhs) ⇔
 no_array_read_dyn_exp tenv extenv lhs ∧ no_array_read_dyn_exp tenv extenv rhs
Proof
 Cases \\ simp [Case_to_IfElse_eq_def, no_array_read_dyn_exp_def]
QED

Theorem no_array_read_dyn_Case_to_IfElse:
 ∀ps d var t tenv extenv.
 no_array_read_dyn tenv extenv (Case_to_IfElse t (Var var) ps d) ⇔
 EVERY (λ(e,p). no_array_read_dyn_exp tenv extenv e ∧ no_array_read_dyn tenv extenv p) ps ∧
 OPTION_ALL (no_array_read_dyn tenv extenv) d
Proof
 Induct \\ Cases \\
 simp [Case_to_IfElse_def, no_array_read_dyn_def, no_array_read_dyn_exp_def,
       no_array_read_dyn_exp_Case_to_IfElse_eq, CONJ_ASSOC]
QED

Theorem no_array_write_dyn_Case_to_IfElse:
 ∀ps d var t tenv extenv.
 no_array_write_dyn tenv (Case_to_IfElse t (Var var) ps d) ⇔
 EVERY (no_array_write_dyn tenv) (MAP SND ps) ∧
 OPTION_ALL (no_array_write_dyn tenv) d
Proof
 Induct \\ Cases \\ simp [Case_to_IfElse_def, no_array_write_dyn_def, CONJ_ASSOC]
QED

Theorem no_Case_Case_to_IfElse:
 ∀tenv ty lhs ps d.
 no_Case (Case_to_IfElse ty lhs ps d) ⇔ EVERY no_Case (MAP SND ps) ∧ OPTION_ALL no_Case d
Proof
 gen_tac \\ recInduct Case_to_IfElse_ind \\ simp [Case_to_IfElse_def, no_Case_def, CONJ_ASSOC]
QED

Theorem vertype_exp_Case_to_IfElse_eq:
 ∀t extenv env lhs rhs.
 vertype_exp extenv env lhs t ∧ vertype_exp extenv env rhs t ⇒
 vertype_exp extenv env (Case_to_IfElse_eq t lhs rhs) VBool_t
Proof
 Cases \\ rpt strip_tac \\ simp [Once vertype_exp_cases, Case_to_IfElse_eq_def] \\ rpt asm_exists_tac
QED

Theorem vertype_stmt_Case_to_IfElse:
 ∀cs ty lhs d tenv extenv.
 vertype_exp extenv tenv lhs ty ∧
 EVERY (λ(e, p). vertype_exp extenv tenv e ty ∧ vertype_stmt extenv tenv p) cs ∧
 OPTION_ALL (vertype_stmt extenv tenv) d ⇒
 vertype_stmt extenv tenv (Case_to_IfElse ty lhs cs d)
Proof
 Induct >- (Cases_on ‘d’ \\ simp [Case_to_IfElse_def] \\ simp [Once vertype_stmt_cases]) \\
 PairCases \\ simp [Case_to_IfElse_def] \\ rpt strip_tac \\
 simp [Once vertype_stmt_cases, vertype_exp_Case_to_IfElse_eq]
QED

Theorem erun_Case_to_IfElse_eq:
 ∀lhs rhs lhs' rhs' t fext s.
 erun fext s lhs = INR lhs' ∧ erun fext s rhs = INR rhs' ∧
 vertype_v lhs' t ∧ vertype_v rhs' t ⇒
 erun fext s (Case_to_IfElse_eq t lhs rhs) = INR $ VBool (lhs' = rhs')
Proof
 Cases_on ‘t’ \\ rw [Case_to_IfElse_eq_def, erun_def] \\
 fs [vertype_v_cases, sum_bind_def, erun_bbop_def, erun_cmp_def, get_VArray_data_def]
QED

Theorem Case_to_IfElse_cong:
 ∀cs cs' m m' d d' ty s1 s1' s2 fext extenv (decls : declty) v.
 prun fext s1 (Case ty m cs d) = INR s1' ∧
 erun fext s2 m' = INR v ∧ vertype_v v ty ∧
 EVERY (λ(e, p). vertype_exp extenv (Ev_from_decls decls) e ty) cs ∧
 vertype_env (Ev_from_decls decls) s1 ∧
 vertype_fext_n extenv fext ∧
 (erun fext s2 m' = erun fext s1 m) ∧
 (MAP FST cs = MAP FST cs') ∧
 LIST_REL (array_rel_prun extenv decls) (MAP SND cs) (MAP SND cs') ∧
 OPTREL (array_rel_prun extenv decls) d d' ∧
 array_rel s1 s2 ⇒
 ∃s2'. prun fext s2 (Case_to_IfElse ty m' cs' d') = INR s2' ∧ array_rel s1' s2'
Proof
 Induct
 >- (Cases_on ‘d’ \\ simp [optionTheory.OPTREL_def] \\ rpt strip_tac \\
     fs [prun_def, Case_to_IfElse_def, array_rel_prun_def] \\ rw [] \\ drule_first \\ rw []) \\
 Cases \\ Cases \\ TRY (Cases_on ‘h’) \\ rw [prun_def, sum_bind_INR, Case_to_IfElse_def] \\
 rfs [] \\ qspec_then ‘q’ assume_tac array_rel_erun \\ drule_first \\
 qspecl_then [‘m'’, ‘q’] assume_tac erun_Case_to_IfElse_eq \\ drule_first \\
 impl_tac >- metis_tac [vertype_exp_erun] \\ strip_tac \\
 simp [get_VBool_data_def] \\ IF_CASES_TAC \\ fs []
 >- (fs [array_rel_prun_def] \\ drule_first \\ simp [])
 \\ first_x_assum match_mp_tac \\ rpt asm_exists_tac \\ simp []
QED

Theorem prun_Case_non_empty_erun_match:
 ∀cs ty m d fext s s'.
 cs ≠ [] ∧ prun fext s (Case ty m cs d) = INR s' ⇒
 ∃v. erun fext s m = INR v
Proof
 Cases \\ TRY (Cases_on ‘h’) \\ rw [prun_def, sum_bind_INR] \\ asm_exists_tac
QED

Theorem array_rel_set_var_tmpnum:
 ∀s1 s2 (decls : declty) tmpnumstart tmpnum v.
 array_rel s1 s2 ∧
 vertype_env (Ev_from_decls decls) s1 ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpnumstart ≤ tmpnum ⇒
 array_rel s1 (set_var s2 (tmpvar tmpnum) v)
Proof
 rw [array_rel_def, set_var_fbits, get_var_set_var, get_nbq_var_set_var] \\ rw [] \\
 fs [fresh_tmpvar_decls_def] \\ drule_first \\ fs [vertype_env_def] \\ drule_first \\
 fs [Ev_from_decls_decls_type]
QED

Theorem tmpvar_tmpvarwrites_cons:
 ∀n t tmps. tmpvar n ∈ tmpvarwrites ((n,t)::tmps)
Proof
 simp [tmpvarwrites_def]
QED

Theorem compile_Case_correct:
 (!tmpnum tmps p decls tmpnumstart extenv tmpnum' tmps' p'.
 compile_Case tmpnum tmps p = (tmpnum', tmps', p') ∧
 vertype_stmt extenv (Ev_from_decls decls) p ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ∧
 no_array_read_dyn (Ev_from_decls decls) extenv p ∧
 no_array_write_dyn (Ev_from_decls decls) p ⇒
 tmpnum ≤ tmpnum' ∧
 tmpvars_extend tmps' tmps ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps' ∧
 set (vwrites p) ⊆ set (vwrites p') ∧
 vnwrites p' = vnwrites p ∧
 no_array_read_dyn (Ev_from_decls decls) extenv p' ∧
 no_array_write_dyn (Ev_from_decls decls) p' ∧
 no_Case p' ∧
 vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) p' ∧
 array_rel_prun extenv decls p p')
 ∧
 (!tmpnum tmps p decls tmpnumstart extenv tmpnum' tmps' p'.
 compile_Case_opt tmpnum tmps p = (tmpnum', tmps', p') ∧
 OPTION_ALL (vertype_stmt extenv (Ev_from_decls decls)) p ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ∧
 OPTION_ALL (no_array_read_dyn (Ev_from_decls decls) extenv) p ∧
 OPTION_ALL (no_array_write_dyn (Ev_from_decls decls)) p ⇒
 tmpnum ≤ tmpnum' ∧
 OPTREL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps') p p' ∧
 OPTREL (λp p'. set (vwrites p) ⊆ set (vwrites p')) p p' ∧
 OPTREL (λp p'. vnwrites p' = vnwrites p) p p' ∧
 OPTION_ALL (no_array_read_dyn (Ev_from_decls decls) extenv) p' ∧
 OPTION_ALL (no_array_write_dyn (Ev_from_decls decls)) p' ∧
 OPTION_ALL no_Case p' ∧
 OPTION_ALL (vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps'))) p' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧
 OPTREL (array_rel_prun extenv decls) p p')
 ∧
 (!tmpnum tmps ps decls tmpnumstart extenv tmpnum' tmps' ps' t.
 compile_Case_case_list tmpnum tmps ps = (tmpnum', tmps', ps') ∧
 EVERY (λ(e, p). vertype_exp extenv (Ev_from_decls decls) e t ∧
                 vertype_stmt extenv (Ev_from_decls decls) p) ps ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 tmpnumstart ≤ tmpnum ∧
 EVERY (λ(e, p). no_array_read_dyn_exp (Ev_from_decls decls) extenv e ∧
                 no_array_read_dyn (Ev_from_decls decls) extenv p) ps ∧
 EVERY (no_array_write_dyn (Ev_from_decls decls)) (MAP SND ps) ⇒
 tmpnum ≤ tmpnum' ∧
 LIST_REL (λ(_, p) (_, p'). set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps') ps ps' ∧
 LIST_REL (λ(_, p) (_, p'). set (vwrites p) ⊆ set (vwrites p')) ps ps' ∧
 LIST_REL (λ(_, p) (_, p'). vnwrites p' = vnwrites p) ps ps' ∧
 EVERY (λ(e, p). no_array_read_dyn_exp (Ev_from_decls decls) extenv e ∧
                 no_array_read_dyn (Ev_from_decls decls) extenv p) ps' ∧
 EVERY (no_array_write_dyn (Ev_from_decls decls)) (MAP SND ps') ∧
 EVERY no_Case (MAP SND ps') ∧
 EVERY (λ(e, p). vertype_exp extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) e t ∧
                 vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps')) p) ps' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧
 MAP FST ps' = MAP FST ps ∧
 LIST_REL (array_rel_prun extenv decls) (MAP SND ps) (MAP SND ps'))
Proof
 ho_match_mp_tac compile_Case_ind \\ rewrite_tac [compile_Case_def] \\
 rpt conj_tac \\ rpt gen_tac

 >- (* Seq *)
 (rewrite_tac [no_array_read_dyn_def, no_array_write_dyn_def] \\ rpt strip_tac' \\
  qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
  qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\ drule_first \\
  asm_rewrite_tac [] \\ simp_tac (srw_ss()) [] \\
  qpat_x_assum ‘compile_Case _ _ p = _’ (assume_tac o SYM) \\ pairarg_tac \\ drule_first \\
  simp [] \\ rpt strip_tac \\ rveq \\ simp []
  >- metis_tac [tmpvars_extend_trans]
  >- (fs [vwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
  THEN2 (fs [vwrites_def, vnwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [])
  >- simp [no_array_read_dyn_def]
  >- simp [no_array_write_dyn_def]
  >- simp [no_Case_def]
  >- (simp [Once vertype_stmt_cases] \\ match_mp_tac vertype_stmt_extend_tmpvardecls \\ rpt asm_exists_tac)
  >- (fs [array_rel_prun_def, prun_def, sum_bind_INR] \\ rpt strip_tac \\
      drule_last \\ drule_first \\ impl_tac >- metis_tac [vertype_stmt_prun] \\ simp []))

 >- (* IfElse *)
 (rewrite_tac [no_array_read_dyn_def, no_array_write_dyn_def] \\ rpt strip_tac' \\
  qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
  qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\ drule_first \\
  asm_rewrite_tac [] \\ simp_tac (srw_ss()) [] \\
  qpat_x_assum ‘compile_Case _ _ p = _’ (assume_tac o SYM) \\ pairarg_tac \\ drule_first \\
  simp [] \\ rpt strip_tac \\ rveq \\ simp []
  >- metis_tac [tmpvars_extend_trans]
  >- (fs [vwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
  THEN2 (fs [vwrites_def, vnwrites_def, pred_setTheory.SUBSET_DEF] \\ metis_tac [])
  >- simp [no_array_read_dyn_def]
  >- simp [no_array_write_dyn_def]
  >- simp [no_Case_def]
  >- (simp [Once vertype_stmt_cases] \\
      metis_tac [vertype_exp_extend_Ev_from_decls, vertype_stmt_extend_tmpvardecls])
  >- (fs [array_rel_prun_def, prun_def, sum_bind_INR] \\ rpt strip_tac \\
      drule_strip array_rel_erun \\ fs [get_VBool_data_INR] \\
      IF_CASES_TAC \\ fs [] \\ drule_first \\ metis_tac [vertype_stmt_prun]))

 >- (* Case *)
 (rewrite_tac [no_array_read_dyn_def, no_array_write_dyn_def] \\ strip_tac \\ rpt gen_tac \\
  IF_CASES_TAC >- (TOP_CASE_TAC
  >- (rpt (pop_assum kall_tac) \\ strip_tac \\ rveq \\
      simp [vwrites_def, vnwrites_def, no_array_read_dyn_def, no_array_write_dyn_def, no_Case_def,
            Once vertype_stmt_cases, array_rel_prun_def, prun_def])
  >- (first_x_assum kall_tac \\ last_x_assum kall_tac \\ strip_tac \\
      qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
      drule_first \\ fs [no_array_read_dyn_def, no_array_write_dyn_def] \\ disch_then drule_strip \\
      fs [vwrites_def, vnwrites_def, array_rel_prun_def, prun_def] \\
      rpt strip_tac \\ drule_first \\ simp [])) \\
  strip_tac \\
  qpat_x_assum ‘vertype_stmt _ _ _’ (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\
  qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\ drule_first \\
  impl_tac >- (full_simp_tac (srw_ss()++boolSimps.ETA_ss) []) \\ strip_tac \\
  asm_rewrite_tac [] \\ simp_tac (srw_ss()) [] \\
  qpat_x_assum ‘compile_Case_case_list _ _ _ = _’ (assume_tac o SYM) \\ pairarg_tac \\ drule_first \\
  impl_tac >- (simp [] \\ full_simp_tac (srw_ss()++boolSimps.ETA_ss) []) \\
  strip_tac \\ last_x_assum kall_tac \\ simp [] \\ strip_tac \\ rveq \\ rpt strip_tac \\ simp []
  >- metis_tac [tmpvars_range_tmpvars_extend, tmpvars_extend_trans]
  >- (match_mp_tac tmpvars_distinct_tmpvars_range \\ rpt asm_exists_tac)
  >- (match_mp_tac tmpvars_range_cons \\ simp [])
  >- (drule_strip OPTREL_subset_vwrites \\ drule_strip LIST_REL_subset_pair_vwrites \\
      fs [vwrites_def, evwrites_def, vwrites_Case_to_IfElse, pred_setTheory.SUBSET_DEF] \\
      metis_tac [tmpvar_tmpvarwrites_cons, tmpvars_range_tmpvars_extend, tmpvarwrites_tmpvars_extend])
  >- (drule_strip OPTREL_preserve_vwrites \\ drule_strip LIST_REL_preserve_pair_vwrites \\
      fs [vwrites_def, vwrites_Case_to_IfElse] \\ fs [pred_setTheory.INSERT_DEF, pred_setTheory.SUBSET_DEF])
  >- (drule_strip OPTREL_vnwrites \\ drule_strip LIST_REL_pair_vnwrites \\
      simp [vnwrites_def, vnwrites_Case_to_IfElse])
  >- simp [no_array_read_dyn_def, no_array_read_dyn_Case_to_IfElse]
  >- simp [no_array_write_dyn_def, no_array_write_dyn_Case_to_IfElse]
  >- simp [no_Case_def, no_Case_Case_to_IfElse]
  >- (simp [Once vertype_stmt_cases] \\ conj_tac
      >- (simp [Once vertype_stmt_cases, Ev_from_decls_decls_type, decls_type_append] \\
          fs [fresh_tmpvar_decls_def, tmpvardecls_def, decls_type_def, vertype_exp_extend_Ev_from_decls])
      >- (match_mp_tac vertype_stmt_Case_to_IfElse \\ rpt conj_tac
          >- (simp [Once vertype_exp_cases] \\
              fs [Ev_from_decls_decls_type, decls_type_append, fresh_tmpvar_decls_def, tmpvardecls_def,
                  decls_type_def])
          >- (irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ Cases \\ rw [] \\
              metis_tac [vertype_exp_extend_tmpvardecls, vertype_stmt_extend_tmpvardecls,
                         tmpvars_range_tmpvars_extend, tmpvars_extend_trans])
          \\ metis_tac [optionTheory.OPTION_ALL_MONO, vertype_stmt_extend_tmpvardecls,
                        tmpvars_range_tmpvars_extend, tmpvars_extend_trans]))
  >- (simp [array_rel_prun_def] \\ rpt strip_tac \\
      drule_strip prun_Case_non_empty_erun_match \\
      drule_strip array_rel_erun \\
      simp [prun_def, prun_assn_rhs_def, sum_map_def, sum_for_def, sum_bind_def, prun_bassn_def, assn_def] \\
      match_mp_tac Case_to_IfElse_cong \\ asm_exists_tac \\
      qexistsl_tac [‘extenv’, ‘decls’, ‘v’] \\ simp [] \\ rpt conj_tac
      >- simp [erun_def, erun_get_var_def, get_var_set_var]
      >- metis_tac [vertype_exp_erun]
      >- (irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ Cases \\ rw [] \\
          fs [Ev_from_decls_def] \\ metis_tac [vertype_exp_extend])
      >- simp [erun_def, erun_get_var_def, get_var_set_var]
      \\ match_mp_tac array_rel_set_var_tmpnum \\ rpt asm_exists_tac \\ simp []))

 THEN3 (* other stmts *)
 (rpt strip_tac' \\ fs [] \\ rveq \\
  simp [no_array_write_dyn_def, vertype_stmt_extend_Ev_from_decls, no_Case_def, array_rel_prun_refl])

 >- (* NONE *)
 (rw [] \\ simp [])

 >- (* SOME *)
 (simp [] \\ rpt strip_tac' \\ pairarg_tac \\ drule_first \\ fs [] \\ rveq \\ simp [])

 >- (* list base *)
 (rw [] \\ simp [])

 >- (* list step *)
 (strip_tac \\ simp_tac (srw_ss()) [no_array_read_dyn_def] \\ rpt strip_tac' \\
  qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\ drule_first \\
  asm_rewrite_tac [] \\ simp_tac (srw_ss()) [] \\
  qpat_x_assum ‘compile_Case _ _ _ = _’ (assume_tac o SYM) \\ pairarg_tac \\ drule_first \\
  simp [] \\ rpt strip_tac \\ rveq \\ simp []
  >- (fs [pred_setTheory.SUBSET_DEF] \\ metis_tac [tmpvarwrites_tmpvars_extend])
  >- metis_tac [vertype_exp_extend_Ev_from_decls, vertype_stmt_extend_tmpvardecls]
  >- metis_tac [tmpvars_extend_trans])
QED

Theorem compile_Case_list_correct:
 !ps ps' decls extenv tmpnum tmpnum' tmpnumstart tmps tmps'.
 compile_Case_list tmpnum tmps ps = (tmpnum', tmps', ps') ∧
 fresh_tmpvar_decls tmpnumstart decls ∧
 tmpvars_distinct tmps ∧
 tmpvars_range tmpnumstart tmpnum tmps ∧
 EVERY (vertype_stmt extenv (Ev_from_decls decls)) ps ∧
 writes_ok ps ∧
 tmpnumstart ≤ tmpnum ∧
 EVERY (no_array_read_dyn (Ev_from_decls decls) extenv) ps ∧
 EVERY (no_array_write_dyn (Ev_from_decls decls)) ps ⇒
 tmpnum ≤ tmpnum' ∧
 LIST_REL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites tmps') ps ps' ∧
 LIST_REL (λp p'. set (vwrites p) ⊆ set (vwrites p')) ps ps' ∧
 LIST_REL (λp p'. vnwrites p' = vnwrites p) ps ps' ∧
 tmpvars_distinct tmps' ∧
 tmpvars_range tmpnumstart tmpnum' tmps' ∧
 tmpvars_extend tmps' tmps ∧
 EVERY (vertype_stmt extenv (Ev_from_decls (decls ++ tmpvardecls tmps'))) ps' ∧
 EVERY (no_array_read_dyn (Ev_from_decls decls) extenv) ps' ∧
 EVERY (no_array_write_dyn (Ev_from_decls decls)) ps' ∧
 EVERY no_Case ps' ∧
 writes_ok ps' ∧
 (!fext s1 s1' s2.
  sum_foldM (prun fext) s1 ps = INR s1' ∧ array_rel s1 s2 ∧
  vertype_env (Ev_from_decls decls) s1 ∧
  vertype_fext_n extenv fext ⇒
  ?s2'. sum_foldM (prun fext) s2 ps' = INR s2' /\
        array_rel s1' s2')
Proof
 Induct \\ simp_tac (srw_ss()) [compile_Case_list_def] >- simp [sum_foldM_def] \\
 rpt strip_tac' \\
 qpat_x_assum ‘LET _ _ = _’ mp_tac \\ simp_tac (srw_ss()) [LET_THM] \\ pairarg_tac \\
 drule_strip (CONJUNCT1 compile_Case_correct) \\
 asm_rewrite_tac [] \\ simp_tac (srw_ss()) [] \\ pairarg_tac \\
 drule_strip writes_ok_tl \\ drule_first \\ simp [] \\ ntac 2 strip_tac \\ rveq \\ simp [] \\
 conj_asm1_tac
 >- (fs [pred_setTheory.SUBSET_DEF] \\ rpt strip_tac \\ drule_first \\ simp [] \\
     drule_strip tmpvarwrites_tmpvars_extend \\ simp []) \\
 rpt strip_tac
 >- metis_tac [tmpvars_extend_trans]
 >- metis_tac [vertype_stmt_extend_tmpvardecls]
 >- (match_mp_tac writes_ok_read_lem \\ qexistsl_tac [‘h::ps’, ‘tmpvarwrites tmps'’] \\
     fs [EVERY_MEM] \\ metis_tac [vertype_stmt_vnwrites_tmpvarwrites]) \\
 fs [sum_foldM_INR, array_rel_prun_def] \\ drule_last \\ drule_first \\ metis_tac [vertype_stmt_prun]
QED

(** Top level preprocessing thm **)

Theorem tmpvardecls_wt:
 ∀tmps. EVERY (λ(var, data). OPTION_ALL (λv. vertype_v v data.type) data.init) (tmpvardecls tmps)
Proof
 Induct \\ TRY PairCases \\ fs [tmpvardecls_def, EVERY_MAP, vertype_v_build_zero]
QED

val array_rel_mrun_trans_tac =
 Induct
 >- (rw [mrun_def, mstep_combs_def, sum_bind_INR] \\
     qmatch_goalsub_abbrev_tac ‘sum_foldM _ s2' _’ \\
     drule_first \\ disch_then (qspec_then ‘s2'’ mp_tac) \\ unabbrev_all_tac \\
     impl_tac >- fs [array_rel_def, get_var_sum_alookup, get_nbq_var_def, vertype_fext_vertype_fext_n,
                     vertype_env_vertype_list, vertype_list_nil, vertype_env_filled_vertype_list_filled] \\
     strip_tac \\ fs [array_rel_def, get_var_sum_alookup]) \\

 rw [mrun_def, sum_bind_INR] \\ rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ drule_last \\
 simp [] \\ rveq \\

 rev_drule_strip vertype_list_mrun \\
 drule_strip vertype_env_mstep_ffs \\ impl_tac >- fs [vertype_fext_vertype_fext_n] \\ strip_tac \\

 fs [mstep_ffs_def, sum_bind_INR] \\
 qmatch_goalsub_abbrev_tac ‘sum_foldM _ s2'' _’ \\
 drule_last \\ disch_then (qspec_then ‘s2''’ mp_tac) \\ unabbrev_all_tac \\
 impl_tac >- (fs [array_rel_def, get_var_sum_alookup, get_nbq_var_def, vertype_fext_vertype_fext_n,
                  vertype_env_vertype_list, vertype_list_nil, vertype_env_filled_vertype_list_filled]) \\
 strip_tac \\

 fs [mstep_combs_def, sum_bind_INR] \\
 qmatch_goalsub_abbrev_tac ‘sum_foldM _ s2''' _’ \\
 drule_last \\ disch_then (qspec_then ‘s2'''’ mp_tac) \\ unabbrev_all_tac \\
 impl_tac >- (gvs [array_rel_def, get_var_sum_alookup, get_nbq_var_sum_alookup, vertype_fext_vertype_fext_n,
                   vertype_env_vertype_list, vertype_list_nil, vertype_env_filled_vertype_list_filled] \\
              rw [sum_alookup_append] \\ every_case_tac \\ fs []) \\
 strip_tac \\
 
 fs [array_rel_def, get_var_sum_alookup, get_nbq_var_sum_alookup];

Theorem array_rel_mrun_trans:
 ∀n fext fbits fbits' ffs ffs' combs combs' s1 s1' s2 tenv extenv.
 mrun fext fbits ffs combs s1 n = INR (s1', fbits') ∧
 EVERY (vertype_stmt extenv tenv) ffs ∧
 EVERY (vertype_stmt extenv tenv) combs ∧
 vertype_list tenv s1 ∧ vertype_fext extenv fext ∧
 (∀var v. sum_alookup s1 var = INR v ⇒ sum_alookup s2 var = INR v) ∧
 (∀fext s1 s1' s2.
  sum_foldM (prun fext) s1 ffs = INR s1' ∧ array_rel s1 s2 ∧
  vertype_env tenv s1 ∧ vertype_fext_n extenv fext ⇒
  ∃s2'. sum_foldM (prun fext) s2 ffs' = INR s2' ∧ array_rel s1' s2') ∧
 (∀fext s1 s1' s2.
  sum_foldM (prun fext) s1 combs = INR s1' ∧ array_rel s1 s2 ∧
  vertype_env tenv s1 ∧ vertype_fext_n extenv fext ⇒
  ∃s2'. sum_foldM (prun fext) s2 combs' = INR s2' ∧ array_rel s1' s2') ⇒
 ∃s2'. mrun fext fbits ffs' combs' s2 n = INR (s2', fbits') ∧
       (∀var v. sum_alookup s1' var = INR v ⇒ sum_alookup s2' var = INR v)
Proof
 array_rel_mrun_trans_tac
QED

Theorem array_rel_mrun_trans_filled:
 ∀n fext fbits fbits' ffs ffs' combs combs' s1 s1' s2 tenv extenv.
 mrun fext fbits ffs combs s1 n = INR (s1', fbits') ∧
 EVERY (vertype_stmt extenv tenv) ffs ∧
 EVERY (vertype_stmt extenv tenv) combs ∧
 vertype_list tenv s1 ∧ vertype_list_filled tenv s1 ∧ vertype_fext extenv fext ∧
 (∀var v. sum_alookup s1 var = INR v ⇒ sum_alookup s2 var = INR v) ∧
 (∀fext s1 s1' s2.
  sum_foldM (prun fext) s1 ffs = INR s1' ∧ array_rel s1 s2 ∧
  vertype_env tenv s1 ∧ vertype_env_filled tenv s1 ∧ vertype_fext_n extenv fext ⇒
  ∃s2'. sum_foldM (prun fext) s2 ffs' = INR s2' ∧ array_rel s1' s2') ∧
 (∀fext s1 s1' s2.
  sum_foldM (prun fext) s1 combs = INR s1' ∧ array_rel s1 s2 ∧
  vertype_env tenv s1 ∧ vertype_env_filled tenv s1 ∧ vertype_fext_n extenv fext ⇒
  ∃s2'. sum_foldM (prun fext) s2 combs' = INR s2' ∧ array_rel s1' s2') ⇒
 ∃s2'. mrun fext fbits ffs' combs' s2 n = INR (s2', fbits') ∧
       (∀var v. sum_alookup s1' var = INR v ⇒ sum_alookup s2' var = INR v)
Proof
 array_rel_mrun_trans_tac
QED

Theorem array_rel_mrun:
 ∀n fext fbits fbits' ffs combs vs1 vs1' vs2.
 mrun fext fbits ffs combs vs1 n = INR (vs1', fbits') ∧
 (∀var v. sum_alookup vs1 var = INR v ⇒ sum_alookup vs2 var = INR v) ⇒
 ∃vs2'. mrun fext fbits ffs combs vs2 n = INR (vs2', fbits') ∧
        (∀var v. sum_alookup vs1' var = INR v ⇒ sum_alookup vs2' var = INR v)
Proof
 Induct
 >- (rw [mrun_def, mstep_combs_def, sum_bind_INR] \\
     qmatch_goalsub_abbrev_tac ‘sum_foldM _ newvs _’ \\
     drule_strip array_rel_pruns \\
     disch_then (qspec_then ‘newvs’ mp_tac) \\ unabbrev_all_tac \\
     impl_tac >- fs [array_rel_def, get_var_sum_alookup, get_nbq_var_sum_alookup] \\ strip_tac \\
     fs [array_rel_def, get_var_sum_alookup]) \\

 rw [mrun_def, sum_bind_INR] \\ rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ drule_first \\

 fs [mstep_ffs_def, sum_bind_INR] \\
 qmatch_goalsub_abbrev_tac ‘sum_foldM _ newvs _’ \\
 drule_strip array_rel_pruns \\
 disch_then (qspec_then ‘newvs’ mp_tac) \\ unabbrev_all_tac \\
 impl_tac >- fs [array_rel_def, get_var_sum_alookup, get_nbq_var_sum_alookup] \\ strip_tac \\

 fs [mstep_combs_def, sum_bind_INR] \\
 qmatch_goalsub_abbrev_tac ‘sum_foldM _ newvs _’ \\
 qspec_then ‘combs’ assume_tac array_rel_pruns \\ drule_first \\
 disch_then (qspec_then ‘newvs’ mp_tac) \\ unabbrev_all_tac \\
 impl_tac >- (fs [array_rel_def, get_var_sum_alookup, get_nbq_var_sum_alookup, sum_alookup_append] \\
              rpt gen_tac \\ every_case_tac \\ fs []) \\ strip_tac \\
 
 fs [array_rel_def, get_var_sum_alookup]
QED

Theorem run_decls_append:
 ∀decls1 decls2 fbits fbits' vs vs'.
 run_decls fbits (decls1 ++ decls2) vs = (fbits', vs') ⇔
 ∃fbits'' vs''. run_decls fbits decls1 vs = (fbits'', vs'') ∧ run_decls fbits'' decls2 vs'' = (fbits', vs')
Proof
 Induct \\ TRY PairCases \\ simp [run_decls_def] \\ rpt gen_tac \\ TOP_CASE_TAC \\ TRY pairarg_tac \\ simp []
QED

Theorem run_decls_tmpvardecls_fbits:
 ∀tmps fbits fbits' vs vs'.
 run_decls fbits (tmpvardecls tmps) vs = (fbits', vs') ⇒ fbits' = fbits
Proof
 Induct \\ TRY PairCases \\ fs [tmpvardecls_def, run_decls_def] \\ rpt strip_tac \\ drule_first
QED

Theorem ALL_DISTINCT_MAP_tmpvar:
 ∀l. ALL_DISTINCT (MAP tmpvar l) ⇔ ALL_DISTINCT l
Proof
 metis_tac [tmpvar_bij, ALL_DISTINCT_MAP_INJ, ALL_DISTINCT_MAP]
QED

Triviality MAP_MAP_FST_lem:
 ∀l f. MAP f (MAP FST l) = MAP (λ(x, y). f x) l
Proof
 simp [MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]
QED

Theorem tmpvars_distinct_ALL_DISTINCT_tmpvardecls:
 ∀tmps. tmpvars_distinct tmps ⇒ ALL_DISTINCT (MAP FST (tmpvardecls tmps))
Proof
 simp [tmpvars_distinct_def, tmpvardecls_def, MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] \\
 simp [GSYM MAP_MAP_FST_lem, ALL_DISTINCT_MAP_tmpvar]
QED

Theorem get_var_type_cong:
 ∀var tenv1 tenv2 extenv t.
 get_var_type tenv1 extenv var = INR t ∧ (∀var t. tenv1 var = SOME t ⇒ tenv2 var = SOME t) ⇒
 get_var_type tenv2 extenv var = INR t
Proof
 Cases \\ rw [get_var_type_def, tenv_type_def] \\ every_case_tac \\ fs [] \\ drule_first \\ fs []
QED

Theorem no_array_read_dyn_exp_cong:
 ∀tenv1 extenv e tenv2.
 no_array_read_dyn_exp tenv1 extenv e ∧ (∀var t. tenv1 var = SOME t ⇒ tenv2 var = SOME t) ⇒
 no_array_read_dyn_exp tenv2 extenv e
Proof
 recInduct no_array_read_dyn_exp_ind \\ rw [no_array_read_dyn_exp_def] \\
 every_case_tac \\ fs [sum_bind_INR] \\ gs [sum_bind_def] \\
 drule_strip get_var_type_cong \\ fs [sum_bind_def]
QED

Theorem no_array_read_dyn_cong:
 ∀tenv1 extenv p tenv2.
 no_array_read_dyn tenv1 extenv p ∧ (∀var t. tenv1 var = SOME t ⇒ tenv2 var = SOME t) ⇒
 no_array_read_dyn tenv2 extenv p
Proof
 recInduct no_array_read_dyn_ind \\ rw [no_array_read_dyn_def]
 >- (rpt drule_first \\ metis_tac [no_array_read_dyn_exp_cong])
 >- metis_tac [no_array_read_dyn_exp_cong]
 >- (fs [EVERY_MEM] \\ Cases \\ rpt strip_tac \\ drule_first \\ fs [] \\ drule_first \\
     metis_tac [no_array_read_dyn_exp_cong])
 >- (Cases_on ‘def’ \\ fs [])
 \\ irule optionTheory.OPTION_ALL_MONO \\ asm_exists_any_tac \\ rw [] \\ metis_tac [no_array_read_dyn_exp_cong]
QED

Theorem EVERY_no_array_read_dyn_extend_Ev_from_decls:
 ∀l1 l2 ps extenv.
 EVERY (no_array_read_dyn (Ev_from_decls l1) extenv) ps ⇒ EVERY (no_array_read_dyn (Ev_from_decls (l1 ++ l2)) extenv) ps
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rpt strip_tac \\
 match_mp_tac no_array_read_dyn_cong \\ asm_exists_tac \\
 simp [Ev_from_decls_def, alist_to_map_alookup, alistTheory.ALOOKUP_APPEND]
QED

Theorem no_array_write_dyn_cong:
 ∀tenv1 p tenv2.
 no_array_write_dyn tenv1 p ∧ (∀var t. tenv1 var = SOME t ⇒ tenv2 var = SOME t) ⇒ no_array_write_dyn tenv2 p
Proof
 recInduct no_array_write_dyn_ind \\ rw [no_array_write_dyn_def]
 >- fs [EVERY_MEM]
 >- (Cases_on ‘def’ \\ fs [])
 \\ last_x_assum mp_tac \\ ntac 3 TOP_CASE_TAC \\ fs [sum_bind_INR, tenv_type_INR] \\
    drule_first \\ fs [GSYM tenv_type_INR, sum_bind_def]
QED

Theorem EVERY_no_array_write_dyn_extend_Ev_from_decls:
 ∀l1 l2 ps.
 EVERY (no_array_write_dyn (Ev_from_decls l1)) ps ⇒ EVERY (no_array_write_dyn (Ev_from_decls (l1 ++ l2))) ps
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rpt strip_tac \\
 match_mp_tac no_array_write_dyn_cong \\ asm_exists_tac \\
 simp [Ev_from_decls_def, alist_to_map_alookup, alistTheory.ALOOKUP_APPEND]
QED

Theorem tmpvars_range_decls_type_INL:
 ∀tmps l h n. tmpvars_range l h tmps ∧ h ≤ n ⇒ decls_type (tmpvardecls tmps) (tmpvar n) = INL UnknownVariable
Proof
 Induct \\ TRY PairCases \\
 fs [decls_type_sum_alookup, tmpvardecls_def, sum_alookup_cons, tmpvars_range_def, tmpvar_bij] \\
 rw [] \\ drule_first
QED

Theorem fresh_tmpvar_decls_tmpvars_range:
 ∀decls tmps l h.
 fresh_tmpvar_decls l decls ∧ tmpvars_range l h tmps ∧ l ≤ h ⇒ fresh_tmpvar_decls h (decls ++ tmpvardecls tmps)
Proof
 rw [fresh_tmpvar_decls_def, decls_type_append] \\ drule_strip tmpvars_range_decls_type_INL
QED

Theorem tmpvardecls_append:
 ∀tmps tmps'. tmpvardecls (tmps ⧺ tmps') = tmpvardecls tmps ⧺ tmpvardecls tmps'
Proof
 rw [tmpvardecls_def]
QED

Theorem LIST_REL_MEM2_IMP:
 ∀xs ys P y. LIST_REL P xs ys ∧ MEM y ys ⇒ ∃x. MEM x xs ∧ P x y
Proof
 simp [LIST_REL_EL_EQN] >> metis_tac [MEM_EL]
QED

Theorem vertype_stmt_MEM_vwrites_decls_type_lem:
 ∀p. vertype_stmt EEv (Ev_from_decls decls) p ⇒ MEM var (vwrites p) ⇒ ∃t. decls_type decls var = INR t
Proof
 ho_match_mp_tac vertype_stmt_ind \\ rw [vwrites_def, evwrites_def, Ev_from_decls_decls_type] \\ fs [SF SFY_ss]
 >- (fs [EVERY_MEM, MEM_FLAT, MEM_MAP] \\ pairarg_tac \\ gvs [] \\ drule_first \\ fs [])
 >- (every_case_tac \\ fs [])
QED

Theorem EVERY_vertype_stmt_MEM_vwrites_decls_type_lem:
 EVERY (vertype_stmt EEv (Ev_from_decls decls)) ps ∧ MEM p ps ∧ MEM var (vwrites p) ⇒ ∃t. decls_type decls var = INR t
Proof
 metis_tac [EVERY_MEM, vertype_stmt_MEM_vwrites_decls_type_lem]
QED

Theorem vertype_stmt_MEM_vnwrites_decls_type_lem:
 ∀p. vertype_stmt EEv (Ev_from_decls decls) p ⇒ MEM var (vnwrites p) ⇒ ∃t. decls_type decls var = INR t
Proof
 ho_match_mp_tac vertype_stmt_ind \\ rw [vnwrites_def, evwrites_def, Ev_from_decls_decls_type] \\ fs [SF SFY_ss]
 >- (fs [EVERY_MEM, MEM_FLAT, MEM_MAP] \\ pairarg_tac \\ gvs [] \\ drule_first \\ fs [])
 >- (every_case_tac \\ fs [])
QED

Theorem EVERY_vertype_stmt_MEM_vnwrites_decls_type_lem2:
 LIST_REL (λp p'. set (vnwrites p') ⊆ set (vnwrites p)) ffs ffs' ∧
 EVERY (vertype_stmt EEv (Ev_from_decls decls)) ffs ∧
 MEM p ffs' ∧
 MEM var (vnwrites p) ⇒
 ∃t p'. MEM p' ffs ∧ MEM var (vnwrites p') ∧ decls_type decls var = INR t
Proof
 rw [EVERY_MEM] \\ drule_strip LIST_REL_MEM2_IMP \\ drule_first \\ fs [pred_setTheory.SUBSET_DEF] \\
 metis_tac [vertype_stmt_MEM_vnwrites_decls_type_lem]
QED

Theorem tmpvarwrites_shape_lem:
 ∀var min max tmps. var ∈ tmpvarwrites tmps ∧ tmpvars_range min max tmps ⇒ ∃n. var = tmpvar n ∧ min ≤ n ∧ n < max
Proof
 rw [tmpvarwrites_def, MEM_MAP, tmpvars_range_def, EVERY_MEM] \\ drule_first \\ pairarg_tac \\ fs [] \\ metis_tac []
QED

Theorem writes_overlap_ok_old_comb_transport:
 ∀ffs ffs' combs (ffs_tmps : (num # vertype) list) tmpnum1 tmpnum2 decls EEv.
 LIST_REL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites ffs_tmps) ffs ffs' ∧
 tmpvars_range tmpnum1 tmpnum2 ffs_tmps ∧
 LIST_REL (λp p'. set (vnwrites p') ⊆ set (vnwrites p)) ffs ffs' ∧
           
 fresh_tmpvar_decls 0 decls ∧

 (*EVERY (vertype_stmt EEv (Ev_from_decls decls)) ffs ∧*)
 EVERY (vertype_stmt EEv (Ev_from_decls decls)) combs ∧

 writes_overlap_ok combs ffs
 ⇒
 writes_overlap_ok combs ffs'
Proof
 rw [writes_overlap_ok_def] \\ strip_tac \\ fs [MEM_FLAT, MEM_MAP] \\ rveq

 >- (drule_strip LIST_REL_MEM2_IMP \\ rev_drule_strip LIST_REL_MEM2_IMP \\
     fs [pred_setTheory.SUBSET_DEF] \\ rpt drule_first
     >- metis_tac []
     \\ (drule_strip EVERY_vertype_stmt_MEM_vwrites_decls_type_lem \\
         imp_res_tac tmpvarwrites_shape_lem \\
         gs [fresh_tmpvar_decls_def, tmpvar_bij])) \\

 drule_strip EVERY_vertype_stmt_MEM_vnwrites_decls_type_lem2 \\
 drule_strip LIST_REL_MEM2_IMP \\ fs [pred_setTheory.SUBSET_DEF] \\ drule_first
 >- metis_tac []
 \\ drule_strip tmpvarwrites_shape_lem \\ gs [fresh_tmpvar_decls_def]
QED

Theorem writes_overlap_ok_transport:
 ∀ffs ffs' combs combs' (ffs_tmps : (num # vertype) list) (combs_tmps : (num # vertype) list)
  tmpnum1 tmpnum2 tmpnum3 decls EEv.
 LIST_REL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites ffs_tmps) ffs ffs' ∧
 tmpvars_range tmpnum1 tmpnum2 ffs_tmps ∧
 LIST_REL (λp p'. set (vnwrites p') ⊆ set (vnwrites p)) ffs ffs' ∧
  
 LIST_REL (λp p'. set (vwrites p') ⊆ set (vwrites p) ∪ tmpvarwrites combs_tmps) combs combs' ∧
 tmpvars_range tmpnum2 tmpnum3 combs_tmps ∧
 tmpnum1 ≤ tmpnum2 ∧
 (*LIST_REL (λp p'. vnwrites p' = vnwrites p) combs combs'*)
           
 fresh_tmpvar_decls tmpnum1 decls ∧

 EVERY (vertype_stmt EEv (Ev_from_decls decls)) ffs ∧
 EVERY (vertype_stmt EEv (Ev_from_decls decls)) combs ∧

 writes_overlap_ok combs ffs
 ⇒
 writes_overlap_ok combs' ffs'
Proof
 rw [writes_overlap_ok_def] \\ strip_tac \\ fs [MEM_FLAT, MEM_MAP] \\ rveq

 >- (drule_strip LIST_REL_MEM2_IMP \\ rev_drule_strip LIST_REL_MEM2_IMP \\
     fs [pred_setTheory.SUBSET_DEF] \\ rpt drule_first
     >- metis_tac []
     \\ (drule_strip EVERY_vertype_stmt_MEM_vwrites_decls_type_lem \\
         rev_drule_strip EVERY_vertype_stmt_MEM_vwrites_decls_type_lem \\
         rpt strip_tac \\
         imp_res_tac tmpvarwrites_shape_lem \\
         gs [fresh_tmpvar_decls_def, tmpvar_bij])) \\

 drule_strip EVERY_vertype_stmt_MEM_vnwrites_decls_type_lem2 \\
 drule_strip LIST_REL_MEM2_IMP \\ fs [pred_setTheory.SUBSET_DEF] \\ drule_first
 >- metis_tac []
 \\ drule_strip tmpvarwrites_shape_lem \\ gs [fresh_tmpvar_decls_def]
QED

Theorem LIST_REL_vnwrites_eq_subset_lem:
 LIST_REL (λp p'. vnwrites p' = vnwrites p) ps ps' ⇒
 LIST_REL (λp p'. set (vnwrites p') ⊆ set (vnwrites p)) ps ps'
Proof
 rpt strip_tac \\ irule LIST_REL_mono \\ asm_exists_any_tac \\ simp []
QED

Theorem fresh_tmpvar_decls_le:
 ∀decls tmpnum tmpnum'. fresh_tmpvar_decls tmpnum decls ∧ tmpnum ≤ tmpnum' ⇒ fresh_tmpvar_decls tmpnum' decls
Proof
 rw [fresh_tmpvar_decls_def]
QED

Theorem ALOOKUP_tmpvardecls_SOME:
 ∀tmps var data. ALOOKUP (tmpvardecls tmps) var = SOME data ⇒ ∃n. var = tmpvar n ∧ MEM n (MAP FST tmps)
Proof
 Induct \\ TRY PairCases \\ fs [tmpvardecls_def] \\ metis_tac []
QED

Theorem tmpvars_range_alt:
 ∀l h tmps. tmpvars_range l h tmps ⇔ EVERY (λn. l ≤ n ∧ n < h) (MAP FST tmps)
Proof
 rw [tmpvars_range_def, EVERY_MAP, pairTheory.LAMBDA_PROD]
QED

Theorem EVERY_vertype_stmt_extend_ffs_tmps_lem:
 EVERY (vertype_stmt extenv (Ev_from_decls (l1 ++ tmpvardecls combs_tmps))) ps ∧
 tmpvars_range tmpnum2 tmpnum3 combs_tmps ∧
 tmpvars_range tmpnum1 tmpnum2 ffs_tmps ⇒
 EVERY (vertype_stmt extenv (Ev_from_decls (l1 ++ tmpvardecls ffs_tmps ++ tmpvardecls combs_tmps))) ps
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rpt strip_tac \\
 irule vertype_stmt_cong \\ asm_exists_any_tac \\
 simp [Ev_from_decls_def, alist_to_map_alookup, alistTheory.ALOOKUP_APPEND, alistTheory.ALOOKUP_MAP] \\ rpt gen_tac \\
 every_case_tac \\ rw [] \\ gvs [] \\ imp_res_tac ALOOKUP_tmpvardecls_SOME \\ fs [tmpvars_range_alt, EVERY_MEM] \\
 rpt drule_first \\ gs [tmpvar_bij]
QED

Theorem preprocess_correct:
 !m m' pseudos.
 preprocess m = INR m' ∧
 vertype_prog m ∧
 module_ok m ⇒
 m'.fextty = m.fextty /\
 (∀var rdata. ALOOKUP m.decls var = SOME rdata ⇒ ALOOKUP m'.decls var = SOME rdata) ∧
 writes_overlap_ok m.combs m'.ffs ∧
 vertype_prog m' /\
 module_ok m' ∧
 EVERY (preprocessed (Ev_from_decls m'.decls) m.fextty) m'.ffs /\
 EVERY (preprocessed (Ev_from_decls m'.decls) m.fextty) m'.combs /\
 (!fext n vs fbits fbits'.
  run fext fbits m n = INR (vs, fbits') ∧ vertype_fext m.fextty fext ⇒
  ?vs'. run fext fbits m' n = INR (vs', fbits') /\
        (!var v. sum_alookup vs var = INR v ==> sum_alookup vs' var = INR v))
Proof
 simp [preprocess_def, module_ok_def, sum_bind_INR, sum_check_INR, vertype_prog_def] \\ rpt strip_tac' \\
 drule_strip tmpvar_check_correct \\

 (* array read: ffs *)
 fs [compile_array_read_module_def] \\ ntac 2 pairarg_tac \\
 drule_strip compile_array_read_list_correct \\ simp [] \\ strip_tac \\
 drule_strip EVERY_vertype_stmt_extend_Ev_from_decls \\
 
 (* array read: combs *)
 fs [] \\ rveq \\ pairarg_tac \\
 drule_strip fresh_tmpvar_decls_le \\ disch_then (qspec_then ‘tmpnum'’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
 drule_strip compile_array_read_list_correct \\ simp [] \\
 strip_tac \\ drule_strip EVERY_vertype_stmt_extend_ffs_tmps_lem \\
 first_x_assum (qspec_then ‘tmpvardecls combs_tmps’ assume_tac) \\

 (* array write: ffs *)
 fs [] \\ rveq \\ fs [compile_array_write_module_def] \\ ntac 2 pairarg_tac \\
 rev_drule_strip fresh_tmpvar_decls_tmpvars_range \\ impl_tac >- simp [] \\ strip_tac \\
 drule_strip fresh_tmpvar_decls_tmpvars_range \\
 drule_strip compile_array_write_list_correct \\ simp [] \\
 disch_then (qspec_then ‘m.fextty’ mp_tac) \\
 impl_tac >- simp [EVERY_vertype_stmt_extend_Ev_from_decls,
                   EVERY_no_array_read_dyn_extend_Ev_from_decls] \\ strip_tac \\
 drule_strip EVERY_vertype_stmt_extend_Ev_from_decls \\

 (* array write: combs *)
 fs [] \\ rveq \\ pairarg_tac \\
 drule_strip fresh_tmpvar_decls_tmpvars_range \\
 drule_strip compile_array_write_list_correct \\ simp [] \\
 disch_then (qspec_then ‘m.fextty’ mp_tac) \\
 impl_tac >- simp [EVERY_vertype_stmt_extend_Ev_from_decls,
                   EVERY_no_array_read_dyn_extend_Ev_from_decls] \\ strip_tac \\
 first_x_assum (qspec_then ‘tmpvardecls combs_tmps'’ assume_tac) \\

 (* cases: ffs *)
 fs [] \\ rveq \\ fs [compile_Case_module_def] \\ pairarg_tac \\
 drule_strip fresh_tmpvar_decls_tmpvars_range \\
 drule_strip compile_Case_list_correct \\ simp [] \\
 disch_then (qspec_then ‘m.fextty’ mp_tac) \\
 impl_tac >- simp [EVERY_vertype_stmt_extend_Ev_from_decls,
                   EVERY_no_array_read_dyn_extend_Ev_from_decls,
                   EVERY_no_array_write_dyn_extend_Ev_from_decls] \\ strip_tac \\

 (* cases: combs *)
 fs [] \\ rveq \\ pairarg_tac \\
 drule_strip fresh_tmpvar_decls_tmpvars_range \\
 drule_strip compile_Case_list_correct \\ simp [] \\
 disch_then (qspec_then ‘m.fextty’ mp_tac) \\
 impl_tac >- simp [EVERY_vertype_stmt_extend_Ev_from_decls,
                   EVERY_no_array_read_dyn_extend_Ev_from_decls,
                   EVERY_no_array_write_dyn_extend_Ev_from_decls] \\ strip_tac \\
 
 fs [] \\ rveq \\ rpt strip_tac \\ simp []
 >- simp [alistTheory.ALOOKUP_APPEND]
 >- (imp_res_tac LIST_REL_vnwrites_eq_subset_lem \\
     rpt (match_mp_tac writes_overlap_ok_old_comb_transport \\ rpt asm_exists_tac))
 (* slow but works: *)
 >- (fs [ALL_DISTINCT_APPEND, tmpvars_distinct_ALL_DISTINCT_tmpvardecls] \\
     rpt strip_tac \\ fs [tmpvardecls_def, MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] \\
     fs [MEM_MAP, FST_THM] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\
     fs [tmpvar_check_def, tmpvar_bij, tmpvars_range_def, EVERY_MEM] \\
     rpt drule_first \\ fs [not_tmpvar_decl_def, is_tmpvar_tmpvar])
 \\ TRY (simp [tmpvardecls_wt] \\ NO_TAC)
 >- simp [EVERY_vertype_stmt_extend_Ev_from_decls]
 >- (imp_res_tac LIST_REL_vnwrites_eq_subset_lem \\
     match_mp_tac writes_overlap_ok_transport \\ rpt asm_exists_tac \\
     (*asm_exists_any_tac \\ conj_tac >- simp [EVERY_vertype_stmt_extend_Ev_from_decls] \\*)
     match_mp_tac writes_overlap_ok_transport \\ rpt asm_exists_tac \\
     (*asm_exists_any_tac \\ conj_tac >- simp [EVERY_vertype_stmt_extend_Ev_from_decls] \\*)
     match_mp_tac writes_overlap_ok_transport \\ rpt asm_exists_tac \\
     rpt asm_exists_any_tac \\ simp [])
 THEN2 simp [EVERY_preprocessed,
             EVERY_no_array_read_dyn_extend_Ev_from_decls, EVERY_no_array_write_dyn_extend_Ev_from_decls] \\
 fs [run_def] \\ rpt (pairarg_tac \\ fs []) \\
 fs [run_decls_append] \\ imp_res_tac run_decls_tmpvardecls_fbits \\ rveq \\
 drule_strip vertype_list_run_decls \\
 drule_strip vertype_list_filled_run_decls \\

 drule_strip array_rel_mrun_trans_filled \\ disch_then (qspecl_then [‘ffs’, ‘combs’, ‘vs''’] mp_tac) \\
 impl_tac >- (rw [] \\ metis_tac []) \\ strip_tac \\

 drule_strip array_rel_mrun_trans \\ disch_then (qspecl_then [‘ffs'’, ‘combs'’, ‘vs''’] mp_tac) \\
 impl_tac >- (rw [vertype_list_extend_Ev_from_decls] \\
              first_x_assum match_mp_tac \\ rpt asm_exists_tac \\ rw [vertype_env_extend_Ev_from_decls]) \\
 strip_tac \\

 drule_strip array_rel_mrun_trans \\ disch_then (qspecl_then [‘ffs''’, ‘combs''’, ‘vs''’] mp_tac) \\
 impl_tac >- (rw [vertype_list_extend_Ev_from_decls] \\
              first_x_assum match_mp_tac \\ rpt asm_exists_tac \\ rw [vertype_env_extend_Ev_from_decls]) \\
 strip_tac \\

 drule_strip array_rel_mrun \\ disch_then (qspec_then ‘vs'’ mp_tac) \\
 impl_tac >- (drule_strip tmpvar_check_run_decls \\ simp [sum_alookup_nil] \\ strip_tac \\
              imp_res_tac run_decls_tmpvardecls \\ metis_tac []) \\ strip_tac \\
 simp []
QED

val _ = export_theory ();
