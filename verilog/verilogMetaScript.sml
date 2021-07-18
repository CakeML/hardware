open hardwarePreamble;

open bitstringTheory;

open oracleTheory sumExtraTheory verilogTheory verilogTypeTheory;

val _ = new_theory "verilogMeta";

(** variables **)

val get_var_set_var = Q.store_thm("get_var_set_var",
 `!s var v var'.
  get_var (set_var s var v) var' = if var = var' then INR v else get_var s var'`,
 rw [set_var_def, get_var_def]);

val get_nbq_var_set_var = Q.store_thm("get_nbq_var_set_var",
 `!s var v var'.
  get_nbq_var (set_var s var v) var' = get_nbq_var s var'`,
 rw [set_var_def, get_nbq_var_def]);

val get_var_set_nbq_var = Q.store_thm("get_var_set_nbq_var",
 `!s var v var'.
  get_var (set_nbq_var s var v) var' = get_var s var'`,
 rw [get_var_def, set_nbq_var_def]);

val get_nbq_var_set_nbq_var = Q.store_thm("get_nbq_var_set_nbq_var",
 `!s var v var'.
  get_nbq_var (set_nbq_var s var v) var' = if var = var' then INR v else get_nbq_var s var'`,
 rw [get_nbq_var_def, set_nbq_var_def]);

(* Everything at once, can probably delete above thms *)
Theorem get_var_cleanup:
 (!s var v var'. get_var (set_var s var v) var' =
                 if var = var' then INR v else get_var s var') /\
 (!s var v var'. get_nbq_var (set_var s var v) var' = get_nbq_var s var') /\
 (!s var v var'. get_var (set_nbq_var s var v) var' = get_var s var') /\
 (!s var v var'. get_nbq_var (set_nbq_var s var v) var' =
                 if var = var' then INR v else get_nbq_var s var')
Proof
 rw [get_var_def, set_var_def, get_nbq_var_def, set_nbq_var_def]
QED

Theorem sum_alookup_cleanup:
 (!s var v var'. sum_alookup (set_var s var v).vars var' = if var = var' then INR v else sum_alookup s.vars var') /\
 (!s var v var'. sum_alookup (set_var s var v).nbq var' = sum_alookup s.nbq var') /\
 (!s var v var'. sum_alookup (set_nbq_var s var v).vars var' = sum_alookup s.vars var') /\
 (!s var v var'. sum_alookup (set_nbq_var s var v).nbq var' = if var = var' then INR v else sum_alookup s.nbq var')
Proof
 rw [sum_alookup_def, set_var_def, set_nbq_var_def]
QED

(** Const thms **)

Theorem set_var_const:
 !s k v. (set_var s k v).nbq = s.nbq
Proof
 rw [set_var_def]
QED

Theorem set_nbq_var_const:
 !s k v. (set_nbq_var s k v).vars = s.vars
Proof
 rw [set_nbq_var_def]
QED

Theorem nd_reset_const:
 !s s' v v'. nd_reset s v = (s', v') ==> s'.vars = s.vars /\ s'.nbq = s.nbq
Proof
 Cases_on `v` \\ simp [nd_reset_def, oracle_bit_def, shift_seq_def] \\
 rpt strip_tac' \\ pairarg_tac \\ fs [] \\ rw []
QED

Theorem prun_assn_rhs_const:
 !fext s s' lhs rhs v.
 prun_assn_rhs fext s lhs rhs = INR (s', v) ==> s'.vars = s.vars /\ s'.nbq = s.nbq
Proof
 Cases_on `rhs`
 >- (Cases_on `lhs` \\ simp [prun_assn_rhs_def, prun_assn_lhs_prev_def, prun_assn_rhs_def, sum_map_INR] \\
    rpt strip_tac' \\ drule_strip nd_reset_const \\ simp [])
 \\ simp [prun_assn_rhs_def, sum_map_INR]
QED

(** Oracle **)

Theorem nd_value_VArray_t_correct:
 !l oracle v oracle'.
 nd_value oracle (VArray_t l) = (v, oracle') ==> vertype_v v (VArray_t l) /\ oracle' = shift_seq l oracle
Proof
 simp [Once vertype_v_cases, nd_value_def] \\ rpt strip_tac' \\
 pairarg_tac \\ drule_strip oracle_bits_correct \\ fs [v2ver_def] \\ rw [EVERY_MAP] \\
 simp [Once vertype_v_cases]
QED

Theorem nd_value_correct: (* <-- strange name *)
 !t oracle v oracle'.
 nd_value oracle t = (v, oracle') ==> vertype_v v t /\ ?n. oracle' = shift_seq n oracle
Proof
 Cases \\ rpt strip_tac'
 >- (fs [Once vertype_v_cases, nd_value_def, oracle_bit_def] \\ metis_tac [])
 >- metis_tac [nd_value_VArray_t_correct]
QED

Theorem nd_reset_type_preserving:
 !t v v' env env'.
 nd_reset env v = (env', v') /\ vertype_v v t ==> (?fbits. env' = env with fbits := fbits) /\ vertype_v v' t
Proof
 Cases \\ rw [vertype_v_cases] \\ fs [nd_reset_def] \\ pairarg_tac \\ fs [] \\ rveq \\
 metis_tac [oracle_bits_correct]
QED

(** fbits thms **)

Theorem pstate_fbits_fbits:
 !(s:pstate). s with fbits := s.fbits = s
Proof
 simp [pstate_component_equality]
QED

Theorem set_var_fbits:
 (!s name v. (set_var s name v).fbits = s.fbits) /\
 (!s name v fbits. (set_var (s with fbits := fbits) name v) = (set_var s name v) with fbits := fbits)
Proof
 rw [set_var_def]
QED

Theorem set_nbq_var_fbits:
 (!s name v. (set_nbq_var s name v).fbits = s.fbits) /\
 (!s name v fbits. (set_nbq_var (s with fbits := fbits) name v) = (set_nbq_var s name v) with fbits := fbits)
Proof
 rw [set_nbq_var_def]
QED

Theorem get_var_fbits:
 !s fbits var. get_var (s with fbits := fbits) var = get_var s var
Proof
 rw [get_var_def]
QED

Theorem get_nbq_var_fbits:
 !s fbits var. get_nbq_var (s with fbits := fbits) var = get_nbq_var s var
Proof
 rw [get_nbq_var_def]
QED

Theorem get_use_nbq_var_fbits:
 !s fbits use_nbq var. get_use_nbq_var (s with fbits := fbits) use_nbq var = get_use_nbq_var s use_nbq var
Proof
 rw [get_use_nbq_var_def, get_var_fbits, get_nbq_var_fbits]
QED

Theorem erun_get_var_fbits:
 !exp fext s fbits. erun_get_var fext (s with fbits := fbits) exp = erun_get_var fext s exp
Proof
 Cases_on `exp` \\ rw [erun_get_var_def, get_var_fbits]
QED

Theorem erun_fbits:
 !e fext s fbits. erun fext (s with fbits := fbits) e = erun fext s e
Proof
 Induct \\ rw [erun_def, erun_get_var_fbits] \\ metis_tac [sum_mapM_cong]
QED

Theorem assn_fbits:
 !lhs fext use_nbq s fbits v. assn fext (s with fbits := fbits) use_nbq lhs v = assn fext s use_nbq lhs v
Proof
 Cases \\ rw [assn_def, get_var_fbits, get_use_nbq_var_fbits, erun_fbits]
QED

Theorem vertype_env_fbits:
 !tenv s fbits. vertype_env tenv (s with fbits := fbits) <=> vertype_env tenv s
Proof
 rw [vertype_env_def, get_var_fbits, get_nbq_var_fbits]
QED

Theorem vertype_env_filled_fbits:
 !tenv s fbits. vertype_env_filled tenv (s with fbits := fbits) <=> vertype_env_filled tenv s
Proof
 rw [vertype_env_filled_def, get_var_fbits]
QED

Theorem vertype_env_set_var:
 !tenv s var v t.
 vertype_env tenv s /\ tenv var = SOME t /\ vertype_v v t ==> vertype_env tenv (set_var s var v)
Proof
 rw [vertype_env_def] \\ fs [get_var_cleanup] \\ every_case_tac \\ fs []
QED

Theorem vertype_env_filled_set_var:
 !tenv s var v t.
 vertype_env_filled tenv s /\ tenv var = SOME t /\ vertype_v v t ==> vertype_env_filled tenv (set_var s var v)
Proof
 rw [vertype_env_filled_def] \\ fs [get_var_cleanup] \\ every_case_tac \\ fs []
QED

Theorem vertype_env_set_nbq_var:
 !tenv s var v t.
 vertype_env tenv s /\ tenv var = SOME t /\ vertype_v v t ==> vertype_env tenv (set_nbq_var s var v)
Proof
 rw [vertype_env_def] \\ fs [get_var_cleanup] \\ every_case_tac \\ fs []
QED

Theorem vertype_env_filled_set_nbq_var:
 !tenv s var v t.
 vertype_env_filled tenv s ==> vertype_env_filled tenv (set_nbq_var s var v)
Proof
 simp [vertype_env_filled_def, get_var_cleanup]
QED

(** Various thms **)

Theorem prun_Seq_Skip:
 (∀fext s p. prun fext s (Seq p Skip) = prun fext s p) ∧  (∀fext s p. prun fext s (Seq Skip p) = prun fext s p)
Proof
 rw [prun_def, sum_bind_id, sum_bind_def]
QED
 
Theorem set_index_LUPDATE:
 !bs b i. i < LENGTH bs ==> set_index i bs b = INR (LUPDATE b i bs)
Proof
 Induct >- simp [] \\ Cases_on ‘i’ \\ rw [set_index_def, LUPDATE_def, sum_for_def, sum_map_def]
QED

Theorem prun_set_var_index_ok_idx:
 !var i bs b. i < LENGTH bs ==> prun_set_var_index var i bs b = INR (var, VArray $ revLUPDATE b i bs)
Proof
 rw [prun_set_var_index_def, revLUPDATE_def, set_index_LUPDATE, sum_for_def, sum_map_def]
QED

Theorem prun_set_var_index_INR:
 !vname vname' i vd vd' rhse.
 prun_set_var_index vname i vd rhse = INR (vname', vd') <=>
 i < LENGTH vd /\ vname' = vname /\ vd' = VArray (revLUPDATE rhse i vd)
Proof
 rw [prun_set_var_index_def, sum_for_INR, set_index_LUPDATE, revLUPDATE_def] \\ metis_tac []
QED
        
(** prun induction cases **)

Theorem prun_Seq:
 !fext p p' s s' v.
  prun fext s (Seq p p') = INR s'
  <=>
  ?sm. prun fext s p = INR sm /\ prun fext sm p' = INR s'
Proof
 rw [prun_def, sum_bind_INR]
QED

Theorem prun_IfElse:
 !fext s c pt pf s'.
  prun fext s (IfElse c pt pf) = INR s' <=>
  (prun fext s pt = INR s' /\ erun fext s c = INR (VBool T)) \/
  (prun fext s pf = INR s' /\ erun fext s c = INR (VBool F))
Proof
 rw [prun_def, sum_bind_INR, get_VBool_data_INR] \\ eq_tac \\
 rpt strip_tac' \\ rveq \\ every_case_tac \\ simp []
QED

Theorem prun_Case:
 !fext s ty e ccond cprog cs default s'.
  prun fext s (Case ty e ((ccond, cprog)::cs) default) = INR s' <=>
  ?e' ccond'. erun fext s e = INR e' /\
  erun fext s ccond = INR ccond' /\
  ((prun fext s cprog = INR s' /\ e' = ccond') \/
  (prun fext s (Case ty e cs default) = INR s' /\ e' <> ccond'))
Proof
 rw [prun_def, sum_bind_INR] \\ EQ_TAC \\ strip_tac \\ every_case_tac \\ simp []
QED

(** Various type things **)

Theorem vertype_v_build_zero:
 ∀t. vertype_v (build_zero t) t
Proof
 Cases \\ rw [build_zero_def, vertype_v_cases]
QED

(** Dynamic semantic respects type system **)

Theorem length_ver_fixwidth:
 ∀bs n. LENGTH (ver_fixwidth n bs) = n
Proof
 rw [ver_fixwidth_def, bitstringTheory.length_pad_left]
QED

Triviality vertype_exp_erun_lem:
 !extenv tenv e t.
 vertype_exp extenv tenv e t ==>
 !env v fext.
 erun fext env e = INR v /\
 vertype_env tenv env /\
 vertype_fext_n extenv fext ==>
 vertype_v v t
Proof
 ntac 2 gen_tac \\ ho_match_mp_tac vertype_exp_ind \\
 rw [erun_def, sum_bind_INR, alist_to_map_alookup, GSYM sum_alookup_INR]
 >- (fs [erun_get_var_def, vertype_env_def] \\ drule_first \\ rfs [])
 >- (fs [erun_get_var_def, vertype_fext_n_def] \\ drule_first \\ rfs [])
 >- (rename1 ‘get_array_index _ vvar’ \\ Cases_on ‘vvar’ \\ fs [get_array_index_def, sum_map_INR] \\
    rveq \\ simp [vertype_v_cases])
 >- (fs [erun_get_var_def, vertype_env_def] \\ drule_first \\
     fs [] \\ rfs [vertype_v_cases] \\ fs [get_array_slice_def])
 >- fs [ver_liftVBool_INR, vertype_v_cases]
 >- (every_case_tac \\ fs [] \\ rw [vertype_v_cases])
 >- (rpt drule_first \\ fs [ver_mapVArray_INR] \\ rveq \\
    fs [n2ver_def, v2ver_def, ver_liftVArray_def] \\ rveq \\ 
    fs [vertype_v_cases, length_ver_fixwidth])
 >- simp [vertype_v_cases]
QED

Theorem vertype_exp_erun:
 !e env extenv tenv t fext v.
 vertype_exp extenv tenv e t ∧
 erun fext env e = INR v ∧
 vertype_env tenv env ∧
 vertype_fext_n extenv fext ⇒
 vertype_v v t
Proof
 rpt strip_tac \\ drule_strip vertype_exp_erun_lem
QED

Theorem prun_Case_cases:
 !cases d ty e fext env env'.
 prun fext env (Case ty e cases d) = INR env' ==>
 (?p. MEM p (MAP SND cases) /\ prun fext env p = INR env') \/
 case d of
   NONE => env' = env
 | SOME d => prun fext env d = INR env'
Proof
 Induct >- (Cases \\ rw [prun_def]) \\ PairCases \\ rw [prun_def, sum_bind_INR] \\ metis_tac []
QED

Theorem vertype_stmt_prun:
 !extenv tenv p.
 vertype_stmt extenv tenv p ==>
 !env env' fext.
 prun fext env p = INR env' /\
 vertype_env tenv env /\
 vertype_fext_n extenv fext ==>
 vertype_env tenv env' ∧ (vertype_env_filled tenv env ⇒ vertype_env_filled tenv env')
Proof
 ntac 2 gen_tac \\ ho_match_mp_tac vertype_stmt_ind \\ simp [prun_def, sum_bind_INR] \\
 rpt conj_tac \\ rpt strip_tac'
 >- metis_tac []
 >- metis_tac []
 >- (drule_strip prun_Case_cases
  >- (fs [EVERY_MEM, MEM_MAP] \\ drule_first \\ pairarg_tac \\ fs [] \\ rveq \\ drule_first \\ simp [])
  >- (every_case_tac \\ fs [] \\ drule_first \\ simp []))
 (* Blocking assignments *)
 >- (fs [prun_assn_rhs_def, sum_map_INR, prun_assn_lhs_prev_def] \\ pairarg_tac \\ rveq \\
    fs [prun_bassn_def, sum_for_INR, assn_def] \\
    drule_strip vertype_env_get_var_type \\ drule_strip nd_reset_type_preserving \\
    simp [set_var_fbits, vertype_env_fbits, vertype_env_filled_fbits] \\
    simp [vertype_env_set_var, vertype_env_filled_set_var])
 >- (fs [prun_assn_rhs_def, sum_map_INR, prun_bassn_def] \\ rveq \\ fs [sum_for_INR, assn_def] \\ rveq \\
     drule_strip vertype_exp_erun \\ simp [vertype_env_set_var, vertype_env_filled_set_var])
 >- (fs [prun_assn_rhs_def, sum_map_INR] \\ rveq \\ fs [prun_bassn_def, sum_for_INR, assn_def, sum_bind_INR] \\
     pairarg_tac \\ fs [prun_set_var_index_INR, get_VArray_data_INR, get_VBool_data_INR] \\ rveq \\
     drule_strip vertype_env_get_use_nbq_var \\ rpt strip_tac
     >- (match_mp_tac vertype_env_set_var \\ rpt asm_exists_tac \\ fs [vertype_v_cases])
     >- (match_mp_tac vertype_env_filled_set_var \\ rpt asm_exists_tac \\ fs [vertype_v_cases]))
 (* Non-blocking assignments, essentially copied from blocking cases *)
 >- (fs [prun_assn_rhs_def, sum_map_INR, prun_assn_lhs_prev_def] \\ pairarg_tac \\ rveq \\
    fs [prun_nbassn_def, sum_for_INR, assn_def] \\
    drule_strip vertype_env_get_var_type \\ drule_strip nd_reset_type_preserving \\
    simp [set_nbq_var_fbits, vertype_env_fbits, vertype_env_filled_fbits] \\
    simp [vertype_env_set_nbq_var, vertype_env_filled_set_nbq_var])
 >- (fs [prun_assn_rhs_def, sum_map_INR, prun_nbassn_def] \\ rveq \\ fs [sum_for_INR, assn_def] \\ rveq \\
     drule_strip vertype_exp_erun \\ simp [vertype_env_set_nbq_var, vertype_env_filled_set_nbq_var])
 >- (fs [prun_assn_rhs_def, sum_map_INR] \\ rveq \\ fs [prun_nbassn_def, sum_for_INR, assn_def, sum_bind_INR] \\
     pairarg_tac \\ fs [prun_set_var_index_INR, get_VArray_data_INR, get_VBool_data_INR] \\ rveq \\
     simp [vertype_env_filled_set_nbq_var] \\
     drule_strip vertype_env_get_use_nbq_var \\
     match_mp_tac vertype_env_set_nbq_var \\ rpt asm_exists_tac \\ fs [vertype_v_cases])
QED

Theorem vertype_env_pruns:
 !ps tenv fext venv venv' extenv.
 sum_foldM (prun fext) venv ps = INR venv' /\
 EVERY (vertype_stmt extenv tenv) ps /\
 vertype_fext_n extenv fext /\
 vertype_env tenv venv ==>
 vertype_env tenv venv' ∧ (vertype_env_filled tenv venv ⇒ vertype_env_filled tenv venv')
Proof
 Induct \\ fs [sum_foldM_def, sum_bind_INR] \\ rpt strip_tac' \\
 drule_strip vertype_stmt_prun \\ drule_first \\ simp []
QED

(* Variant of vertype_env_pruns that's good for irule sometimes *)
(*Theorem vertype_env_pruns':
 !ps tenv fext venv venv' extenv.
 sum_foldM (prun fext) venv ps = INR venv' /\
 EVERY (vertype_stmt extenv tenv) ps /\
 vertype_fext_n extenv fext /\
 vertype_env tenv venv ==>
 vertype_env tenv venv'
Proof
 metis_tac [vertype_env_pruns]
QED*)

Theorem vertype_list_append:
 ∀l1 l2 tenv. vertype_list tenv l1 ∧ vertype_list tenv l2 ⇒ vertype_list tenv (l1 ++ l2)
Proof
 rw [vertype_list_def, alistTheory.ALOOKUP_APPEND] \\ every_case_tac \\ rw []
QED

Theorem vertype_list_filled_append:
 ∀l1 l2 tenv. vertype_list tenv l1 ∧ vertype_list_filled tenv l2 ⇒ vertype_list_filled tenv (l1 ⧺ l2)
Proof
 rw [vertype_list_def, vertype_list_filled_def, alistTheory.ALOOKUP_APPEND] \\ CASE_TAC \\ simp [] \\
 rpt drule_first \\ rfs []
QED

Theorem vertype_env_mstep_ffs:
 !ps tenv fext venv venv' extenv fbits fbits'.
 mstep_ffs fext fbits ps venv = INR (venv', fbits') /\
 EVERY (vertype_stmt extenv tenv) ps /\
 vertype_fext_n extenv fext /\
 vertype_list tenv venv ==>
 vertype_list tenv venv' ∧ (vertype_list_filled tenv venv ⇒ vertype_list_filled tenv venv')
Proof
 simp [mstep_ffs_def, sum_bind_INR] \\ rpt strip_tac' \\
 drule_strip vertype_env_pruns \\
 fs [vertype_env_vertype_list, vertype_env_filled_vertype_list_filled, vertype_list_nil] \\
 metis_tac [vertype_list_append, vertype_list_filled_append]
QED

Theorem vertype_env_mstep_combs:
 !ps tenv fext venv venv' extenv fbits fbits'.
 mstep_combs fext fbits ps venv = INR (venv', fbits') /\
 EVERY (vertype_stmt extenv tenv) ps /\
 vertype_fext_n extenv fext /\
 vertype_list tenv venv ==>
 vertype_list tenv venv' ∧ (vertype_list_filled tenv venv ⇒ vertype_list_filled tenv venv')
Proof
 simp [mstep_combs_def, sum_bind_INR] \\ rpt strip_tac' \\
 drule_strip vertype_env_pruns \\
 fs [vertype_env_vertype_list, vertype_env_filled_vertype_list_filled, vertype_list_nil]
QED

Theorem vertype_list_mrun:
 !n tenv fext fbits fbits' ffs combs venv venv' extenv.
 mrun fext fbits ffs combs venv n = INR (venv', fbits') ∧
 EVERY (vertype_stmt extenv tenv) ffs /\
 EVERY (vertype_stmt extenv tenv) combs /\
 vertype_fext extenv fext /\
 vertype_list tenv venv ==>
 vertype_list tenv venv' ∧ (vertype_list_filled tenv venv ⇒ vertype_list_filled tenv venv')
Proof
 Induct >- (simp [mrun_def, vertype_fext_vertype_fext_n] \\
            rpt strip_tac' \\ first_x_assum (qspec_then ‘0’ assume_tac) \\
            drule_strip vertype_env_mstep_combs \\ simp []) \\
 
 simp [mrun_def, sum_bind_INR] \\ rpt strip_tac' \\
 rpt (pairarg_tac \\ gvs [sum_bind_INR]) \\
 drule_first \\

 fs [vertype_fext_vertype_fext_n] \\
 first_assum (qspec_then ‘n’ assume_tac) \\
 first_x_assum (qspec_then ‘SUC n’ assume_tac) \\
 
 drule_strip vertype_env_mstep_ffs \\
 drule_strip vertype_env_mstep_combs \\
 simp []
QED

Triviality vertype_list_run_decls_lem:
 !decls fbits fbits' venv venv' Ev.
 run_decls fbits decls venv = (fbits', venv') /\
 EVERY (λ(var, data). OPTION_ALL (λv. vertype_v v data.type) data.init) decls /\
 Ev_covers_decls Ev decls /\
 vertype_list Ev venv ==>
 vertype_list Ev venv'
Proof
 Induct \\ TRY PairCases \\ fs [run_decls_def, Ev_covers_decls_cons] \\ rpt gen_tac \\ rpt TOP_CASE_TAC \\
 TRY (pairarg_tac \\ drule_strip nd_value_correct) \\
 rw [] \\ first_x_assum match_mp_tac \\ asm_exists_tac \\ fs [vertype_list_def] \\
 rw [] \\ rpt asm_exists_tac
QED

Theorem vertype_list_run_decls:
 !decls fbits fbits' venv.
 run_decls fbits decls [] = (fbits', venv) ∧
 EVERY (λ(var, data). OPTION_ALL (λv. vertype_v v data.type) data.init) decls ∧
 ALL_DISTINCT (MAP FST decls) ⇒
 vertype_list (Ev_from_decls decls) venv
Proof
 rpt strip_tac \\ drule_strip vertype_list_run_decls_lem \\
 disch_then (qspec_then ‘Ev_from_decls decls’ mp_tac) \\
 simp [Ev_covers_decls_Ev_from_decls, vertype_list_def]
QED

Theorem run_decls_unchanged:
 ∀decls fbits fbits' venv venv'.
 run_decls fbits decls venv = (fbits', venv') ⇒
 ∀var. ~MEM var (MAP FST decls) ⇒ ALOOKUP venv' var = ALOOKUP venv var
Proof
 Induct \\ TRY PairCases \\ simp [run_decls_def] \\ rpt gen_tac \\ rpt TOP_CASE_TAC \\
 TRY pairarg_tac \\ rw [] \\ drule_first \\ fs []
QED

Theorem vertype_list_filled_run_decls:
 ∀decls fbits fbits' venv venv'.
 run_decls fbits decls venv = (fbits', venv') ∧
 EVERY (λ(var, data). OPTION_ALL (λv. vertype_v v data.type) data.init) decls ∧
 ALL_DISTINCT (MAP FST decls) ⇒
 vertype_list_filled (Ev_from_decls decls) venv'
Proof
 Induct >- simp [run_decls_def, Ev_from_decls_nil, vertype_list_filled_def] \\
 PairCases \\ simp [run_decls_def] \\ rpt gen_tac \\ rpt TOP_CASE_TAC \\ FIRST
 [pairarg_tac \\ rw [] \\ drule_first \\
  fs [vertype_list_filled_def, Ev_from_decls_def, alist_to_map_alookup] \\ rw [] \\
  drule_strip run_decls_unchanged \\ drule_strip nd_value_correct \\ simp [],
     
  rw [] \\ drule_first \\
  fs [vertype_list_filled_def, Ev_from_decls_def, alist_to_map_alookup] \\ rw [] \\
  drule_strip run_decls_unchanged \\ simp []]
QED

(** erun read/write thms **)

Theorem erun_get_var_cong:
 !fext s exp s'.
 (!var. MEM var (evreads exp) ==> get_var s var = get_var s' var) ==>
 erun_get_var fext s exp = erun_get_var fext s' exp
Proof
 Cases_on `exp` \\ rw [erun_get_var_def, evreads_def]
QED

Theorem erun_cong_ArrayIndex:
 !es fext s s'.
 (!e var. MEM e es /\ (MEM var (evreads e) ==> get_var s var = get_var s' var) ==>
          erun fext s e = erun fext s' e) /\
 (∀var. (∃l. (∃e. l = evreads e /\ MEM e es) /\ MEM var l) ==>
        get_var s var = get_var s' var) ==>
 sum_mapM (erun fext s) es = sum_mapM (erun fext s') es
Proof
 Induct \\ rw [sum_mapM_def] \\ TOP_CASE_TAC \\ metis_tac []
QED

Theorem erun_cong:
 !fext s exp s'.
 (!var. MEM var (evreads exp) ==> get_var s var = get_var s' var) ==>
 erun fext s exp = erun fext s' exp
Proof
 Induct_on ‘exp’ \\ rw [erun_def, erun_get_var_def, evreads_def, MEM_FLAT, MEM_MAP] \\
 metis_tac [sum_mapM_cong, erun_get_var_cong, erun_cong_ArrayIndex]
QED

Theorem vertype_exp_evreads_decls_type:
 ∀extenv decls t' var e t.
 vertype_exp extenv (Ev_from_decls decls) e t ⇒ MEM var (evreads e) ⇒ ∃t'. decls_type decls var = INR t'
Proof
 ntac 4 gen_tac \\ ho_match_mp_tac vertype_exp_ind \\
 rw [evreads_def, Ev_from_decls_decls_type] \\ metis_tac []
QED

Theorem erun_cong_type:
 !exp extenv fext s s' decls t.
 vertype_exp extenv (Ev_from_decls decls) exp t ∧
 (!var t. decls_type decls var = INR t ==> get_var s' var = get_var s var) ==>
 erun fext s exp = erun fext s' exp
Proof
 metis_tac [erun_cong, vertype_exp_evreads_decls_type]
QED

Theorem erun_cong_INR_type:
 !exp extenv fext s s' (decls : declty) t v.
 erun fext s exp = INR v ∧
 vertype_exp extenv (Ev_from_decls decls) exp t ∧
 (!var t. decls_type decls var = INR t ==> get_var s' var = get_var s var) ⇒
 erun fext s' exp = INR v
Proof
 metis_tac [erun_cong_type]
QED

Theorem erun_get_var_cong_INR:
 !e fext s s' v.
 erun_get_var fext s e = INR v /\
 (!var v. (*MEM var (evreads e) /\*) get_var s var = INR v ==> get_var s' var = INR v) ==>
 erun_get_var fext s' e = INR v
Proof
 Cases \\ rw [evreads_def, erun_get_var_def]
QED

(* Note that this does not follow from erun_cong because the condition here both weaker and stronger *)
Theorem erun_cong_INR:
 !e fext s s' v.
 erun fext s e = INR v /\
 (!var v. (*MEM var (evreads e) /\*) get_var s var = INR v ==> get_var s' var = INR v) ==>
 erun fext s' e = INR v
Proof
 Induct \\ rw [erun_def, sum_bind_INR]
 >- drule_strip erun_get_var_cong_INR
 >- drule_strip erun_get_var_cong_INR
 >- (drule_strip erun_get_var_cong_INR \\ simp [] \\ drule_first \\ simp [])
 >- (drule_strip erun_get_var_cong_INR \\ simp [])
 >- (rpt drule_last \\ simp [])
 >- (drule_last \\ simp [] \\ IF_CASES_TAC \\ fs [] \\ first_x_assum match_mp_tac \\ rpt asm_exists_tac)
 \\ rpt drule_last \\ simp []
QED

(** prun read/write thms **)

(* NOTE: Could have evreads_index as precond here, but slice updates etc. updates
         whole value, not just part... *)
(*Theorem assn_cong:
 !lhs fext s s' rhs.
 (!var. MEM var (evreads lhs) ==> get_var s var = get_var s' var) ==>
 assn fext s lhs rhs = assn fext s' lhs rhs
Proof
 Induct \\ rw [evwrites_def, evreads_def, assn_def] \\
 Cases_on `l` \\ simp [assn_def] \\
 Cases_on `lhs` \\ simp [assn_def] \\
 TRY (Cases_on `t` \\ simp [assn_def]) \\
 fs [evreads_def] \\ metis_tac [erun_cong]
QED*)

Theorem get_use_nbq_var_cong_INR:
 !use_nbq var v s s'.
 get_use_nbq_var s use_nbq var = INR v /\
 (!var v. get_var s var = INR v ==> get_var s' var = INR v) /\
 (!var. get_nbq_var s' var = get_nbq_var s var) ==>
 get_use_nbq_var s' use_nbq var = INR v
Proof
 rw [get_use_nbq_var_def] \\ TOP_CASE_TAC \\ fs []
QED

Theorem assn_cong_INR:
 !lhs rhs v fext s s' use_nbq.
 assn fext s use_nbq lhs rhs = INR v /\
 (!var v. get_var s var = INR v ==> get_var s' var = INR v) /\
 (!var. get_nbq_var s' var = get_nbq_var s var) ==>
 assn fext s' use_nbq lhs rhs = INR v
Proof
 Cases \\ rw [assn_def, sum_bind_INR] \\ drule_strip get_use_nbq_var_cong_INR
 >- (drule_strip erun_cong_INR \\ simp [])
 \\ fs [sum_for_INR]
QED

(*
val same_shape_set_index = Q.store_thm("same_shape_set_index",
 `!is n v v'. set_index n is v = INR v' ==> same_shape (VArray v') (VArray is)`,
 Induct >- rw [set_index_def] \\ Cases_on `n`
 >- rw [set_index_def, same_shape_def, same_shape_refl]
 \\ rw [set_index_def] \\ drule sum_for_INR_old \\ strip_tac \\ fs [sum_for_def, sum_map_def] \\ rveq \\
    simp [same_shape_def, same_shape_refl] \\ first_x_assum match_mp_tac \\
    asm_exists_tac \\ simp []);

val same_shape_set_slice = Q.store_thm("same_shape_set_slice",
 `!il ih d d' newdata.
   il <= ih /\ ih < LENGTH d /\ set_slice (LENGTH d − (ih + 1)) (ih + 1 − il) d newdata = INR d'
   ==> same_shape (VArray d') (VArray d)`,
 rw [set_slice_def] \\ fs [rich_listTheory.DROP_DROP] \\

 once_rewrite_tac [same_shape_sym] \\
 Q.ISPECL_THEN [`LENGTH d − (ih + 1)`, `d`] mp_tac (GSYM TAKE_DROP) \\
 disch_then (fn th => PURE_REWRITE_TAC [Once th, Once (GSYM APPEND_ASSOC)]) \\
 match_mp_tac same_shape_append \\ conj_tac
 >- simp [same_shape_refl] \\

 Q.ISPECL_THEN [`ih + 1 − il`, `DROP (LENGTH d − (ih + 1)) d`] mp_tac (GSYM TAKE_DROP) \\
 disch_then (fn th => PURE_REWRITE_TAC [Once th]) \\
 match_mp_tac same_shape_append \\
 simp [rich_listTheory.DROP_DROP, same_shape_refl]);

(* Move? *)
val get_VArray_data_INR = Q.store_thm("get_VArray_data_INR",
 `!v d. get_VArray_data v = INR d ==> ?vd. v = VArray vd`,
 Cases \\ rw [get_VArray_data_def]);

val assn_INR = Q.store_thm("assn_INR",
 `!fext s lhs v r.
   assn fext s lhs v = INR r ==>
   (?name v'.
     lhs = Var name /\ r = (name, v) /\
     get_var s name = INR v' /\ same_shape v v') \/

   (?name i v' v''.
     lhs = ArrayIndex (Var name) [i] /\ r = (name, v') /\
     get_var s name = INR v'' /\ same_shape v' v'') \/

   (?name ih il v' v''.
     lhs = ArraySlice (Var name) [] ih il /\ r = (name, v') /\
     get_var s name = INR v'' /\ same_shape v' v'') \/

   (?name i ih il v' v''.
     lhs = ArraySlice (Var name) [i] ih il /\ r = (name, v') /\
     get_var s name = INR v'' /\ same_shape v' v'')`,
 rpt gen_tac \\ Cases_on `lhs` \\ simp [assn_def]
 >- (strip_tac \\ imp_res_tac sum_bind_INR_old \\ fs [sum_bind_def]) \\
 TRY (qmatch_goalsub_rename_tac `ArraySlice e l ih il`) \\
 Cases_on `e` \\ simp [assn_def] \\ Cases_on `l` \\ simp [assn_def] \\
 TRY (Cases_on `t` \\ simp [assn_def]) \\ strip_tac \\

 rpt (CHANGED_TAC (imp_res_tac sum_bind_INR_old \\ fs [sum_bind_def])) \\
 fs [prun_set_var_index_def, prun_set_slice_def]

 >-
 (last_x_assum mp_tac \\ rw [] \\
 imp_res_tac sum_for_INR_old \\ fs [sum_for_def, sum_map_def] \\
 drule same_shape_set_index \\ strip_tac \\
 (* Horrible: *)
 qexists_tac `VArray v'''''` \\ simp [] \\ Cases_on `v'''` \\ fs [get_VArray_data_def])

 \\
 every_case_tac \\ fs [sum_for_def, sum_map_def] \\
 drule_strip sum_map_INR_old

 >-
 (imp_res_tac same_shape_set_slice \\
 (* Horrible: *)
 imp_res_tac get_VArray_data_INR \\ rveq \\ fs [get_VArray_data_def] \\ rveq \\
 fs [sum_for_def, sum_map_def] \\ metis_tac [])

 \\
 fs [sum_map_def] \\ rveq \\ simp [] \\
 drule_strip same_shape_set_index \\
 imp_res_tac same_shape_set_slice \\
 (* Horrible: *)
 imp_res_tac get_VArray_data_INR \\ fs [get_VArray_data_def]);
*)

Theorem assn_NoIndexing_same_after:
 !fext s use_nbq var v v'.
 assn fext s use_nbq (NoIndexing var) v = INR v' ==> ?v''. v' = (var, v'')
Proof
 simp [assn_def]
QED

Theorem assn_Indexing_same_after:
 !fext s use_nbq var islen is v v'.
 assn fext s use_nbq (Indexing var islen is) v = INR v' ==> ?v''. v' = (var, v'')
Proof
 Cases_on `is` \\ simp [assn_def, sum_bind_INR, prun_set_var_index_def] \\
 rpt strip_tac \\ every_case_tac \\ fs [sum_for_INR] \\ rw []
QED

Theorem assn_SliceIndexing_same_after:
 !fext s use_nbq var n m v v'.
 assn fext s use_nbq (SliceIndexing var n m) v = INR v' ==> ?v''. v' = (var, v'')
Proof
 rw [assn_def, sum_bind_INR, prun_set_slice_def, set_slice_def] \\ every_case_tac \\
 fs [sum_for_INR] \\ rw []
QED

Theorem prun_same_after:
 !fext s p s'.
 prun fext s p = INR s' ==>
 (!var. ~MEM var (vwrites p) ==> get_var s' var = get_var s var) /\
 (!var. ~MEM var (vnwrites p) ==> get_nbq_var s' var = get_nbq_var s var) /\
 (!var err. get_var s' var = INL err ==> get_var s var = INL err) /\
 (!var err. get_nbq_var s' var = INL err ==> get_nbq_var s var = INL err)
Proof
 recInduct prun_ind \\ rpt conj_tac \\ rpt strip_tac' \\
 TRY (fs [prun_def, vwrites_def, vnwrites_def] \\ NO_TAC)
 >- (rpt strip_tac \\ fs [prun_Seq, vwrites_def, vnwrites_def] \\ res_tac \\ fs [])
 >- (rpt strip_tac \\ fs [prun_IfElse, vwrites_def, vnwrites_def])
 >- (rpt strip_tac \\ fs [prun_Case, vwrites_def, vnwrites_def] \\ res_tac)
 \\ (* BlockingAssign and NonBlockingAssign *)
    fs [prun_def, vwrites_def, vnwrites_def, sum_bind_INR, prun_bassn_def, prun_nbassn_def, sum_for_INR] \\
    (pairarg_tac \\ rveq \\ drule_strip prun_assn_rhs_const \\ fs [sum_for_INR] \\
    Cases_on `lhs` \\ rveq
    >- (fs [assn_def] \\ rw [evwrites_def, get_var_cleanup] \\ rfs [get_var_def, get_nbq_var_def])
    >- (drule_strip assn_Indexing_same_after \\ fs [get_var_cleanup, evwrites_def] \\ rw [get_var_def, get_nbq_var_def])
    \\ drule_strip assn_SliceIndexing_same_after \\ fs [get_var_cleanup, evwrites_def] \\ rw [get_var_def, get_nbq_var_def])
QED

Theorem pruns_same_after:
 !ps fext s s'.
 sum_foldM (prun fext) s ps = INR s' ⇒
 (!var. EVERY (\p. ~MEM var (vwrites p)) ps ==> get_var s' var = get_var s var) /\
 (!var. EVERY (\p. ~MEM var (vnwrites p)) ps ==> get_nbq_var s' var = get_nbq_var s var) /\
 (!var err. get_var s' var = INL err ==> get_var s var = INL err) /\
 (!var err. get_nbq_var s' var = INL err ==> get_nbq_var s var = INL err)
Proof
 Induct \\ simp [sum_foldM_INR] \\ rpt strip_tac' \\
 drule_strip prun_same_after \\ drule_first \\ fs []
QED

Theorem EVERY_MEM_MEM_FLAT_MAP:
 ∀x f l. EVERY (λp. ¬MEM x (f p)) l ⇔ ¬MEM x (FLAT (MAP f l))
Proof
 simp [EVERY_MEM, MEM_FLAT, MEM_MAP] \\ metis_tac []
QED

Theorem vertype_stmt_writes:
 !EEv Ev var p. vertype_stmt EEv Ev p ⇒ Ev var = NONE ⇒ ~MEM var (vwrites p) ∧ ~MEM var (vnwrites p)
Proof
 ntac 3 gen_tac \\ ho_match_mp_tac vertype_stmt_ind \\ simp [vwrites_def, vnwrites_def, evwrites_def] \\ rw [] \\
 every_case_tac \\ fs [MEM_FLAT, MEM_MAP, EVERY_MEM, pairTheory.FORALL_PROD] \\ metis_tac []
QED

Theorem vertype_stmts_writes:
 !EEv Ev var ps.
 EVERY (vertype_stmt EEv Ev) ps ∧ Ev var = NONE ⇒ ~MEM var (FLAT (MAP vwrites ps)) ∧ ~MEM var (FLAT (MAP vnwrites ps))
Proof
 simp [EVERY_MEM, MEM_FLAT, MEM_MAP] \\ metis_tac [vertype_stmt_writes]
QED

(** module-level **)

(*Theorem mstep_step:
 (!fextn vs. mstep fextn [] vs = INR vs) ∧
 (!fextn p ps vs vs'.
 mstep fextn (p::ps) vs = INR vs' <=>
 ?vs''. prun fextn vs p = INR vs'' /\
        mstep fextn ps vs'' = INR vs')
Proof
 rw [mstep_def, sum_foldM_INR]
QED

Theorem mrun_step:
 !fext fbits fbits' ps vs vs' n.
 mrun fext fbits ps vs (SUC n) = INR (vs', fbits') <=>
 ?vs'' fbits''. mrun fext fbits ps vs n = INR (vs'', fbits'') /\
                mstep_commit (fext n) fbits'' ps vs'' = INR (vs', fbits')
Proof
 rw [mrun_def, sum_bind_INR, sum_bind_def] \\ eq_tac \\ rpt strip_tac' \\ TRY pairarg_tac \\ fs []
QED

Theorem mrun_empty:
 !fext fbits s n. mrun fext fbits [] s n = INR (s, fbits)
Proof
 Induct_on `n` \\
 rw [mrun_def, mstep_commit_def, mstep_def, sum_foldM_def, sum_bind_def, sum_map_def]
QED

Theorem mstep_same_after:
 !ps fext s s'.
 mstep fext ps s = INR s' ==>
 (!var. EVERY (\p. ~MEM var (vwrites p)) ps ==> get_var s' var = get_var s var) /\
 (!var. EVERY (\p. ~MEM var (vnwrites p)) ps ==> get_nbq_var s' var = get_nbq_var s var) /\
 (!var err. get_var s' var = INL err ==> get_var s var = INL err) /\
 (!var err. get_nbq_var s' var = INL err ==> get_nbq_var s var = INL err)
Proof
 Induct >- rw [mstep_def, sum_foldM_def] \\ simp [mstep_step] \\ rpt strip_tac' \\
 drule_strip prun_same_after \\ drule_first \\ fs []
QED*)

(** misc thms, vnwrites correct etc. **)
val vnwrites_nil_correct = Q.store_thm("vnwrites_nil_correct",
 `!fext ver_s p ver_s'.
   prun fext ver_s p = INR ver_s' /\ vnwrites p = [] ==>
   ver_s'.nbq = ver_s.nbq`,
 recInduct prun_ind \\ rpt strip_tac \\ rveq \\ fs [vnwrites_def]
 >- (* Skip *)
 fs [prun_def]
 >- (* Seq *)
 (fs [prun_Seq] \\ res_tac \\ fs [])
 >- (* IfElse *)
 (fs [prun_IfElse] \\ res_tac \\ pop_assum match_mp_tac)
 >- (* Case i *)
 (fs [prun_Case] \\ res_tac)
 >- (* Case ii *)
 fs [prun_def]
 >- (* Case iii *)
 fs [prun_def]
 \\ (* BlockingAssn *)
  fs [prun_def, sum_bind_INR] \\ pairarg_tac \\ rveq \\
  drule_strip prun_assn_rhs_const \\ fs [prun_bassn_def, sum_for_INR] \\
  pairarg_tac \\ rw [set_var_const]);

Theorem EVERY_vnwrites_nil_correct:
 ∀ps fext s s'. sum_foldM (prun fext) s ps = INR s' ∧ EVERY (λp. vnwrites p = []) ps ⇒ s'.nbq = s.nbq
Proof
 Induct \\ simp [sum_foldM_INR] \\ metis_tac [vnwrites_nil_correct]
QED

val fixwidth_LENGTH_cong = Q.store_thm("fixwidth_LENGTH_cong",
 `!l n. n = LENGTH l ==> fixwidth n l = l`,
 Induct \\ rw [fixwidth]);

val LENGTH_fixwidth = Q.store_thm("LENGTH_fixwidth",
 `!l n. LENGTH (fixwidth n l) = n`,
 Induct \\ rw [fixwidth]);

(*val ver_fixwidth_fixwidth_MAP = Q.store_thm("ver_fixwidth_fixwidth_MAP",
 `!v n. ver_fixwidth n (MAP VBool v) = MAP VBool (fixwidth n v)`,
 rw [ver_fixwidth_def, fixwidth_def, zero_extend_def, MAP_DROP, PAD_LEFT, MAP_GENLIST]);

val EVERY_isVBool_MAP_VBool = Q.store_thm("EVERY_isVBool_MAP_VBool",
 `!l. EVERY isVBool (MAP VBool l)`,
 Induct \\ rw [isVBool_def]);

val same_shape_prun = Q.store_thm("same_shape_prun",
 `!fext s p name v s'.
   prun fext s p = INR s' /\
   get_var s name = INR v /\
   (!nbq_v. get_nbq_var s name = INR nbq_v ==> same_shape nbq_v v) ==>
   (?v'. get_var s' name = INR v' /\ same_shape v' v) /\
   (!nbq_v. get_nbq_var s' name = INR nbq_v ==> same_shape nbq_v v)`,
 recInduct prun_ind \\ rpt conj_tac \\ rpt strip_tac'
 >- rfs [prun_def, same_shape_refl]
 >- (fs [prun_Seq] \\ rpt drule_first \\ metis_tac [same_shape_trans, same_shape_sym])
 >- (fs [prun_IfElse] \\ rpt drule_first)
 >- (fs [prun_Case] \\ drule_last \\ simp [])
 >- (fs [prun_def] \\ drule_first)
 >- rfs [prun_def, same_shape_refl]
 \\ fs [prun_def] \\ drule_strip sum_bind_INR_old \\
    fs [sum_bind_def, prun_bassn_def, prun_nbassn_def] \\
    drule_strip sum_for_INR_old \\ fs [sum_for_def, sum_map_def] \\
    drule_strip assn_INR \\
    rw [get_var_cleanup, same_shape_refl] \\ fs [] \\ rveq \\ simp []);

val has_type_prun = Q.store_thm("has_type_prun",
 `!fext s p name v s' ty.
   prun fext s p = INR s' /\
   get_var s name = INR v /\ has_type v ty /\
   (!nbq_v. get_nbq_var s name = INR nbq_v ==> has_type nbq_v ty) ==>
   (?v'. get_var s' name = INR v' /\ has_type v' ty) /\
   (!nbq_v. get_nbq_var s' name = INR nbq_v ==> has_type nbq_v ty)`,
 rpt strip_tac' \\ drule_strip same_shape_prun \\ metis_tac [has_type_same_shape, same_shape_has_type]);

val var_has_type_prun = Q.store_thm("var_has_type_prun",
 `!fext s p v s' ty.
  var_has_type s.vars v ty /\ nbq_var_has_type s v ty /\ prun fext s p = INR s' ==>
  (var_has_type s'.vars v ty /\ nbq_var_has_type s' v ty)`,
 simp [var_has_type_def, nbq_var_has_type_def, GSYM get_var_ALOOKUP] \\ rpt strip_tac' \\
 drule_strip has_type_prun \\ simp []);

val vars_has_type_prun = Q.store_thm("vars_has_type_prun",
 `!tys fext p s s'.
   vars_has_type s.vars tys /\ nbq_vars_has_type s tys /\ prun fext s p = INR s' ==>
   (vars_has_type s'.vars tys /\ nbq_vars_has_type s' tys)`,
 Induct >- rw [vars_has_type_def, nbq_vars_has_type_def] \\ Cases_on `h` \\
 simp [vars_has_type_def, nbq_vars_has_type_def] \\ rpt strip_tac' \\
 drule_first \\ drule_strip var_has_type_prun \\ simp []);
*)

(*
val mstep_commit_unfold1 = Q.store_thm("mstep_commit_unfold1",
 `!fext ps p ver_s ver_s' vars.
  mstep fext (p::ps) ver_s = INR ver_s' <=>
  ?ver_s''. prun fext ver_s p = INR ver_s'' /\
            mstep fext ps ver_s'' = INR ver_s'`,
  rw [mstep_def, sum_foldM_def] \\ EQ_TAC \\ strip_tac
  >- (imp_res_tac sum_bind_INR \\ fs [sum_bind_def])
  \\ fs [sum_map_def, sum_bind_def]);
*)

(*
val vars_has_type_mstep = Q.store_thm("vars_has_type_mstep",
 `!ps fext s s' tys.
   mstep fext ps s = INR s' /\ vars_has_type s.vars tys /\ nbq_vars_has_type s tys ==>
   (vars_has_type s'.vars tys /\ nbq_vars_has_type s' tys)`,
 Induct >- (rw [mstep_def, sum_foldM_def] \\ simp []) \\ simp [mstep_step] \\ rpt strip_tac' \\
 drule_strip vars_has_type_prun \\ drule_first \\ simp []);

val nbq_vars_has_type_empty = Q.store_thm("nbq_vars_has_type_empty",
 `!tys s. s.nbq = [] ==> nbq_vars_has_type s tys`,
 Induct \\ TRY (Cases_on `h`) \\ rw [nbq_vars_has_type_def, nbq_var_has_type_def, get_nbq_var_def]);

val vars_has_type_APPEND = Q.store_thm("vars_has_type_APPEND",
 `!tys v. vars_has_type v.vars tys /\ nbq_vars_has_type v tys ==> vars_has_type (v.nbq ++ v.vars) tys`,
 Induct \\ TRY (Cases_on `h`) \\ rw [vars_has_type_def, nbq_vars_has_type_def] \\
 fs [var_has_type_def, nbq_var_has_type_def, alistTheory.ALOOKUP_APPEND, get_nbq_var_def, get_var_def] \\
 TOP_CASE_TAC \\ rw []);

val vars_has_type_mstep_commit = Q.store_thm("vars_has_type_mstep_commit",
 `!ps fext vs vs' tys.
   mstep_commit fext ps vs = INR vs' /\ vars_has_type vs tys ==>
   vars_has_type vs' tys`,
 rw [mstep_commit_def] \\ drule_strip sum_map_INR_old \\ drule_strip vars_has_type_mstep \\
 simp [vars_has_type_def] \\ disch_then drule \\ simp [nbq_vars_has_type_empty] \\ strip_tac \\
 fs [sum_map_def] \\ rveq \\ simp [vars_has_type_APPEND]);

val vars_has_type_mrun = Q.store_thm("vars_has_type_mrun",
 `!n ps tys fext vs vs'.
   vars_has_type vs tys /\ mrun fext ps vs n = INR vs' ==>
   vars_has_type vs' tys`,
 Induct \\ simp [mrun_def] \\ rpt strip_tac \\ drule_strip sum_bind_INR_old \\
 fs [sum_bind_def] \\ metis_tac [vars_has_type_mstep_commit]);
*)

(*
val WORD_get_1dim_VArray_data = Q.store_thm("WORD_get_1dim_VArray_data",
 `!w v. WORD w v ==> ?v'. get_1dim_VArray_data v = INR v' /\ VArray v' = w2ver w`,
 rw [WORD_def, get_1dim_VArray_data_def, w2ver_def, EVERY_isVBool_MAP_VBool, w2v_not_empty]);
*)

(* Maybe something from the standard library could be used here? *)
val memsublist_def = Define `
 memsublist l1 l2 <=> !x. MEM x l1 ==> MEM x l2`;

Theorem memsublist_sym:
 !l. memsublist l l
Proof
 simp [memsublist_def]
QED

Theorem memsublist_tl:
 !x xs ys. memsublist (x::xs) ys ==> memsublist xs ys
Proof
 simp [memsublist_def]
QED

Theorem writes_ok_tl:
 !p ps. writes_ok (p::ps) ==> writes_ok ps
Proof
 rw [writes_ok_def] \\ metis_tac []
QED

Theorem writes_ok_memsublist:
 !l1 l2. memsublist l1 l2 /\ writes_ok l2 ==> writes_ok l1
Proof
 rw [memsublist_def, writes_ok_def, MEM_FLAT, MEM_MAP] \\ metis_tac []
QED

(* Inefficient but simple *)
(*Theorem writes_ok_computable:
 !p. writes_ok p <=> EVERY (\var. ~MEM var (vnwrites p)) (vwrites p) /\
                     EVERY (\var. ~MEM var (vwrites p)) (vnwrites p)
Proof
 simp [writes_ok_def, EVERY_MEM] \\ metis_tac []
QED*)

(*Theorem writes_ok_non_overlapping:
 !p fext s s'.
 writes_ok p /\ prun fext s p = INR s' /\ s.nbq = [] ==>
 (!var v. get_var s' var = INR v ==> get_nbq_var s' var = INL UnknownVariable) /\
 (!var v. get_nbq_var s' var = INR v ==> get_var s' var = INL UnknownVariable)
Proof
 simp [writes_ok_def] \\ rpt strip_tac' \\ drule_strip prun_same_after \\ rpt strip_tac \\
 last_x_assum (qspec_then `var` strip_assume_tac) \\ drule_first
 >- fs [] 
QED*)

(* Similar to prun_same_after but other direction, too weak... *)
Theorem prun_get_nbq_var_INR:
 !fext s p s' var v.
 prun fext s p = INR s' /\ get_nbq_var s' var = INR v ==>
 MEM var (vnwrites p) \/ get_nbq_var s var = INR v
Proof
 recInduct prun_ind \\ rpt conj_tac \\ rpt strip_tac' \\
 fs [vnwrites_def, prun_def, sum_bind_INR]
 \\ TRY (metis_tac []) (* <-- ugly but works here *)
 \\ pairarg_tac \\ rveq \\ drule_strip prun_assn_rhs_const \\
    fs [prun_bassn_def, prun_nbassn_def, sum_for_INR]
   >- (pairarg_tac \\ rveq \\ fs [get_var_cleanup] \\ fs [get_nbq_var_def])
   \\ Cases_on `lhs` \\ fs [assn_def]
    >- (rveq \\ fs [get_var_cleanup] \\ every_case_tac \\ fs [evwrites_def, get_nbq_var_def])
    >- (fs [sum_bind_INR, prun_set_var_index_def] \\ every_case_tac \\ fs [sum_for_INR] \\
       rveq \\ fs [get_var_cleanup] \\ every_case_tac \\ fs [evwrites_def, get_nbq_var_def])
    \\ fs [sum_bind_INR, sum_for_INR] \\
       rveq \\ fs [get_var_cleanup] \\ every_case_tac \\ fs [evwrites_def, get_nbq_var_def]
QED

Theorem pruns_get_nbq_var_INR:
 !ps fext s s' var v.
 sum_foldM (prun fext) s ps = INR s' /\ get_nbq_var s' var = INR v ==>
 MEM var (FLAT (MAP vnwrites ps)) \/ get_nbq_var s var = INR v
Proof
 Induct \\ fs [sum_foldM_def, sum_bind_INR] \\ metis_tac [prun_get_nbq_var_INR]
QED

(* Deterministic things *)

Definition deterministic_process_def:
 (deterministic_process Skip ⇔ T) ∧
 (deterministic_process (Seq s1 s2) ⇔ deterministic_process s1 ∧ deterministic_process s2) ∧
 (deterministic_process (IfElse c s1 s2) ⇔ deterministic_process s1 ∧ deterministic_process s2) ∧
 (deterministic_process (Case ty c ss ds) ⇔ EVERY (λ(_, s). deterministic_process s) ss ∧ OPTION_ALL deterministic_process ds) ∧
 (deterministic_process (BlockingAssign lhs rhs) ⇔ IS_SOME rhs) ∧
 (deterministic_process (NonBlockingAssign lhs rhs) ⇔ IS_SOME rhs)
Termination
 WF_REL_TAC `measure vprog_size` \\ rw [] \\
 drule_strip MEM_IMP_vprog_size \\ decide_tac
End

(* Could also prove that fbits do not change... *)
Theorem deterministic_process_prun:
 ∀fext s p fbits s'.
 prun fext s p = INR s' ∧ deterministic_process p ⇒
 prun fext (s with fbits := fbits) p = INR (s' with fbits := fbits)
Proof
 recInduct prun_ind \\ rw [prun_def, sum_bind_INR, deterministic_process_def]
 >- metis_tac []
 >- (simp [erun_fbits] \\ metis_tac [])
 >- (simp [erun_fbits] \\ metis_tac [])
 \\ fs [optionTheory.IS_SOME_EXISTS] \\ fs [prun_assn_rhs_def, erun_fbits, sum_map_INR] \\ rveq \\
    fs [prun_bassn_def, prun_nbassn_def, assn_fbits, sum_for_INR, set_var_fbits, set_nbq_var_fbits] \\
    pairarg_tac \\ fs []
QED

Theorem prun_Case_cong:
 !fext s ty ty' c c' cases cases' dcase dcase'.
 (∀fext s. erun fext s c' = erun fext s c) ∧
 (LENGTH cases' = LENGTH cases) ∧
 (∀i e e' p p'. i < LENGTH cases ∧ EL i cases = (e, p) ∧ EL i cases' = (e', p') ⇒
                (∀fext s. erun fext s e' = erun fext s e) ∧
                (∀fext s. prun fext s p' = prun fext s p)) ∧
 (IS_SOME dcase' ⇔ IS_SOME dcase) ∧
 (∀p p'. dcase = SOME p ∧ dcase' = SOME p' ⇒ ∀fext s. prun fext s p' = prun fext s p) ⇒
 prun fext s (Case ty' c' cases' dcase') = prun fext s (Case ty c cases dcase)
Proof
 Induct_on `cases` \\ Cases_on ‘cases'’ \\ simp []
 >- (Cases_on `dcase` \\ Cases_on ‘dcase'’ \\ simp [prun_def]) \\
 PairCases \\ PairCases_on ‘h’ \\ rw [prun_def] \\
 match_mp_tac sum_bind_cong \\ rw [] \\
 first_assum (qspec_then ‘0’ mp_tac) \\ simp [] \\ strip_tac \\
 match_mp_tac sum_bind_cong \\ rw [] \\
 last_x_assum match_mp_tac \\ simp [] \\ rpt strip_tac' \\
 first_x_assum (qspec_then ‘SUC i’ mp_tac) \\ simp []
QED

Theorem pruns_cong:
 ∀fext ps' ps.
 (LIST_REL (λp' p. ∀fext s. prun fext s p' = prun fext s p) ps' ps) ⇒
 ∀s. sum_foldM (prun fext) s ps' = sum_foldM (prun fext) s ps
Proof
 gen_tac \\ ho_match_mp_tac LIST_REL_ind \\ rpt strip_tac \\ simp [sum_foldM_def]
QED

Theorem mrun_cong:
 ∀fext n ps1 ps1' ps2 ps2'.
 (LIST_REL (λp' p. ∀fext s. prun fext s p' = prun fext s p) ps1' ps1) ∧
 (LIST_REL (λp' p. ∀fext s. prun fext s p' = prun fext s p) ps2' ps2) ⇒
 ∀fbits s. mrun fext fbits ps1' ps2' s n = mrun fext fbits ps1 ps2 s n
Proof
 gen_tac \\ Induct \\ rw [mrun_def] \\
 res_tac \\ imp_res_tac pruns_cong \\ simp [mstep_ffs_def, mstep_combs_def]
QED

val _ = export_theory ();
