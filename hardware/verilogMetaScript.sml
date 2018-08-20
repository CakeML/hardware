open preamble;

open bitstringTheory;

open verilogTheory verilogTypeTheory sumExtraTheory;

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
val get_var_cleanup = Q.store_thm("get_var_cleanup",
 `(!s var v var'. get_var (set_var s var v) var' =
                  if var = var' then INR v else get_var s var') /\
  (!s var v var'. get_nbq_var (set_var s var v) var' = get_nbq_var s var') /\
  (!s var v var'. get_var (set_nbq_var s var v) var' = get_var s var') /\
  (!s var v var'. get_nbq_var (set_nbq_var s var v) var' =
                  if var = var' then INR v else get_nbq_var s var')`,
 rw [get_var_def, set_var_def, get_nbq_var_def, set_nbq_var_def]);

val get_var_ALOOKUP = Q.store_thm("get_var_ALOOKUP",
 `!s name v. get_var s name = INR v <=> ALOOKUP s.vars name = SOME v`,
 rw [get_var_def] \\ TOP_CASE_TAC);

(*
val get_var_set_var_ALT = Q.store_thm("get_var_set_var_ALT",
 `!s var v s' var'.
  set_var s var v = s' ==>
  get_var s' var' = if var = var' then INR v else get_var s var'`,
 metis_tac [get_var_set_var]);
*)

(** erun **)

(*
(* probably not needed? *)
val erun_env = Q.store_thm("erun_env",
 `!s exp s' env. erun (s with vars := env) exp = erun (s' with vars := env) exp`,
 recInduct erun_ind \\ rpt strip_tac
 >- (* Const *)
 rw [erun_def]
 >- (* Var *)
 rw [erun_def, get_var_def]
 >- (* ArrayIndex *)
 (rw [erun_def, get_var_def] \\
 (* TODO, lots of strange things going on here: *)
 pop_assum (assume_tac o
           (Q.GEN `a`) o
           (Q.SPECL [`a`, `s'`, `env`]) o
           (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV))) \\
 imp_res_tac sum_mapM_cong \\
 rewrite_tac [ETA_THM] \\ fs []) (* <-- rw [ETA_THM] does nothing here *)
 >- (* ArraySlice i *)
 rw [erun_def, get_var_def]
 >- (* ArraySlice ii *)
 rw [erun_def]
 >- (* Op *)
 (rw [erun_def] \\ metis_tac [])
 >- (* Cmp *)
 (rw [erun_def] \\ metis_tac [])
 >- (* ZeroExtend *)
 cheat
 >- (* SignExtend *)
 cheat);
*)

(** prun induction cases **)

val prun_Seq = Q.store_thm("prun_Seq",
 `!fext p p' s s' v.
   prun fext s (Seq p p') = INR s'
   <=>
   ?sm. prun fext s p = INR sm /\ prun fext sm p' = INR s'`,
 rw [prun_def] \\ Cases_on `prun fext s p` \\ fs [sum_bind_def]);

val prun_IfElse = Q.store_thm("prun_IfElse",
 `!fext s c pt pf s'.
   prun fext s (IfElse c pt pf) = INR s' <=>
   (prun fext s pt = INR s' /\ erun fext s c = INR (VBool T)) \/
   (prun fext s pf = INR s' /\ erun fext s c = INR (VBool F))`,
 rpt gen_tac \\ EQ_TAC \\ rw [prun_def] \\ fs [sum_bind_def, get_VBool_data_def] \\
 imp_res_tac sum_bind_INR \\ fs [sum_bind_def] \\
 Cases_on `v'` \\ fs [get_VBool_data_def, sum_bind_def] \\
 FULL_CASE_TAC \\ simp []);

val prun_Case = Q.store_thm("prun_Case",
 `!fext s e ccond cprog cs default s'.
   prun fext s (Case e ((ccond, cprog)::cs) default) = INR s' <=>
   ?e' ccond'. erun fext s e = INR e' /\
   erun fext s ccond = INR ccond' /\
   ((prun fext s cprog = INR s' /\ e' = ccond') \/
   (prun fext s (Case e cs default) = INR s' /\ e' <> ccond'))`,
 rw [prun_def] \\ EQ_TAC \\ strip_tac
 >- (imp_res_tac sum_bind_INR \\ fs [sum_bind_def] \\
     imp_res_tac sum_bind_INR \\ fs [sum_bind_def] \\
     FULL_CASE_TAC \\ simp [])
 \\ simp [sum_bind_def]);

(** erun read/write thms **)

val erun_get_var_cong = Q.store_thm("erun_get_var_cong",
`!fext s exp s'.
  (!var. MEM var (evreads exp) ==> get_var s var = get_var s' var) ==>
  erun_get_var fext s exp = erun_get_var fext s' exp`,
 Cases_on `exp` \\ rw [erun_get_var_def, evreads_def]);

val erun_cong_ArrayIndex = Q.store_thm("erun_cong_ArrayIndex",
 `!es fext s s'.
  (!e var. MEM e es /\ (MEM var (evreads e) ==> get_var s var = get_var s' var) ==>
           erun fext s e = erun fext s' e) /\
  (∀var. (∃l. (∃e. l = evreads e /\ MEM e es) /\ MEM var l) ==>
         get_var s var = get_var s' var) ==>
  sum_mapM (erun fext s) es = sum_mapM (erun fext s') es`,
 Induct \\ rw [sum_mapM_def] \\ TOP_CASE_TAC \\ metis_tac []);

val erun_cong = Q.store_thm("erun_cong",
 `!fext s exp s'.
  (!var. MEM var (evreads exp) ==> get_var s var = get_var s' var) ==>
  erun fext s exp = erun fext s' exp`,
 recInduct erun_ind \\ rw [erun_def, erun_get_var_def, evreads_def, MEM_FLAT, MEM_MAP] \\
 metis_tac [sum_mapM_cong, erun_get_var_cong, erun_cong_ArrayIndex]);

(** prun read/write thms **)

(* NOTE: Could have evreads_index as precond here, but slice updates etc. updates
         whole value, not just part... *)
val assn_cong = Q.store_thm("assn_cong",
 `!lhs fext s s' rhs.
   (!var. MEM var (evreads lhs) ==> get_var s var = get_var s' var) ==>
   assn fext s lhs rhs = assn fext s' lhs rhs`,
 Induct \\ rw [evwrites_def, evreads_def, assn_def] \\
 Cases_on `l` \\ simp [assn_def] \\
 Cases_on `lhs` \\ simp [assn_def] \\
 Cases_on `t` \\ simp [assn_def] \\
 fs [evreads_def] \\ metis_tac [erun_cong]);

val same_shape_set_index = Q.store_thm("same_shape_set_index",
 `!is n v v'. set_index n is v = INR v' ==> same_shape (VArray v') (VArray is)`,
 Induct >- rw [set_index_def] \\ Cases_on `n`
 >- rw [set_index_def, same_shape_def, same_shape_refl]
 \\ rw [set_index_def] \\ drule sum_for_INR \\ strip_tac \\ fs [sum_for_def, sum_map_def] \\ rveq \\
    simp [same_shape_def, same_shape_refl] \\ first_x_assum match_mp_tac \\
    asm_exists_tac \\ simp []);

val assn_INR = Q.store_thm("assn_INR",
 `!fext s lhs v r.
   assn fext s lhs v = INR r ==>
   (?name v'. lhs = Var name /\ r = (name, v) /\
              get_var s name = INR v' /\ same_shape v v') \/
   (?name i v' v''. lhs = ArrayIndex (Var name) [i] /\ r = (name, v') /\
                    get_var s name = INR v'' /\ same_shape v' v'')`,
 rpt gen_tac \\ Cases_on `lhs` \\ simp [assn_def]
 >- (strip_tac \\ imp_res_tac sum_bind_INR \\ fs [sum_bind_def]) \\
 Cases_on `e` \\ simp [assn_def] \\ Cases_on `l` \\ simp [assn_def] \\
 Cases_on `t` \\ simp [assn_def] \\ strip_tac \\
 rpt (CHANGED_TAC (imp_res_tac sum_bind_INR \\ fs [sum_bind_def])) \\
 fs [prun_set_var_index_def] \\ last_x_assum mp_tac \\ rw [] \\
 imp_res_tac sum_for_INR \\ fs [sum_for_def, sum_map_def] \\
 drule same_shape_set_index \\ strip_tac \\
 (* Horrible: *)
 qexists_tac `VArray v'''''` \\ simp [] \\ Cases_on `v'''` \\ fs [get_VArray_data_def]);

val prun_same_after = Q.store_thm("prun_same_after",
 `!fext ver_s p ver_s'.
 prun fext ver_s p = INR ver_s' ==>
 (!var. ~MEM var (vwrites p) ==> get_var ver_s' var = get_var ver_s var) /\
 (!var. ~MEM var (vnwrites p) ==> get_nbq_var ver_s' var = get_nbq_var ver_s var)`,
 recInduct prun_ind \\ rpt conj_tac \\ rpt gen_tac \\ rpt disch_tac \\
 TRY (fs [prun_def, vwrites_def, vnwrites_def] \\ NO_TAC)
 >- (rpt strip_tac \\ fs [prun_Seq, vwrites_def, vnwrites_def] \\ res_tac \\ fs [])
 >- (rpt strip_tac \\ fs [prun_IfElse, vwrites_def, vnwrites_def])
 >- (rpt strip_tac \\ fs [prun_Case, vwrites_def, vnwrites_def] \\ res_tac)
 \\ (* BlockingAssign and NonBlockingAssign *)
    fs [prun_def, vwrites_def, vnwrites_def] \\ imp_res_tac sum_bind_INR \\
    fs [sum_bind_def, prun_bassn_def, prun_nbassn_def] \\
    imp_res_tac sum_for_INR \\ drule assn_INR \\ strip_tac \\ rveq \\
    fs [sum_for_def, sum_map_def] \\
    rw [evwrites_def, get_var_cleanup]);

val prun_get_var_INL = Q.store_thm("prun_get_var_INL",
 `!fext s p s' var err.
   prun fext s p = INR s' /\ get_var s' var = INL err ==> get_var s var = INL err`,
 recInduct prun_ind \\ rpt strip_tac
 >- fs [prun_def]
 >- fs [prun_Seq]
 >- fs [prun_IfElse]
 >- (fs [prun_Case] \\ metis_tac [])
 \\ fs [prun_def] \\ drule_strip sum_bind_INR \\ fs [sum_bind_def, prun_bassn_def, prun_nbassn_def] \\
    drule_strip sum_for_INR \\ fs [sum_for_def, sum_map_def] \\ drule_strip assn_INR \\
    fs [get_var_cleanup] \\ EVERY_CASE_TAC \\ fs []);

(** misc thms, vnwrites correct etc. **)

val vnwrites_nil_correct = Q.store_thm("vnwrites_nil_correct",
 `!fext ver_s p env ver_s'.
   vnwrites p = [] /\
   prun fext ver_s p = INR ver_s' ==>
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
 >- (* BlockingAssn *)
 (fs [prun_def] \\ imp_res_tac sum_bind_INR \\ fs [sum_bind_def, prun_bassn_def] \\
  imp_res_tac sum_for_INR \\ fs [sum_for_def, sum_map_def] \\ PairCases_on `v''` \\
  fs [set_var_def, pstate_component_equality])
 \\ (* NonBlockingAssn *)
 (fs [prun_def] \\ imp_res_tac sum_bind_INR \\ fs [sum_bind_def, prun_nbassn_def] \\
  imp_res_tac sum_for_INR \\ fs [sum_for_def, sum_map_def] \\
  Cases_on `lhs` \\ fs [assn_def, evwrites_def] \\ Cases_on `e` \\ fs [assn_def, evwrites_def]));

val fixwidth_LENGTH_cong = Q.store_thm("fixwidth_LENGTH_cong",
 `!l n. n = LENGTH l ==> fixwidth n l = l`,
 Induct \\ rw [fixwidth]);

val LENGTH_fixwidth = Q.store_thm("LENGTH_fixwidth",
 `!l n. LENGTH (fixwidth n l) = n`,
 Induct \\ rw [fixwidth]);

val ver_fixwidth_fixwidth_MAP = Q.store_thm("ver_fixwidth_fixwidth_MAP",
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
 \\ fs [prun_def] \\ drule_strip sum_bind_INR \\
    fs [sum_bind_def, prun_bassn_def, prun_nbassn_def] \\
    drule_strip sum_for_INR \\ fs [sum_for_def, sum_map_def] \\
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

val mstep_unfold1 = Q.store_thm("mstep_unfold1",
 `!fext ps p ver_s ver_s' vars.
  mstep fext (p::ps) ver_s = INR ver_s' <=>
  ?ver_s''. prun fext ver_s p = INR ver_s'' /\
            mstep fext ps ver_s'' = INR ver_s'`,
  rw [mstep_def, sum_foldM_def] \\ EQ_TAC \\ strip_tac
  >- (imp_res_tac sum_bind_INR \\ fs [sum_bind_def])
  \\ fs [sum_map_def, sum_bind_def]);

val mrun_unfold1 = Q.store_thm("mrun_unfold1",
 `!fext ps vs vs' n.
   mrun fext ps vs (SUC n) = INR vs' <=>
   ?vs''. mrun fext ps vs n = INR vs'' /\ mstep_commit (fext n) ps vs'' = INR vs'`,
 rw [mrun_def] \\ eq_tac \\ strip_tac
 >- (drule sum_bind_INR \\ strip_tac \\ fs [sum_bind_def])
 \\ simp [sum_bind_def]);

val vars_has_type_mstep = Q.store_thm("vars_has_type_mstep",
 `!ps fext s s' tys.
   mstep fext ps s = INR s' /\ vars_has_type s.vars tys /\ nbq_vars_has_type s tys ==>
   (vars_has_type s'.vars tys /\ nbq_vars_has_type s' tys)`,
 Induct >- (rw [mstep_def, sum_foldM_def] \\ simp []) \\ simp [mstep_unfold1] \\ rpt strip_tac' \\
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
 rw [mstep_commit_def] \\ drule_strip sum_map_INR \\ drule_strip vars_has_type_mstep \\
 simp [vars_has_type_def] \\ disch_then drule \\ simp [nbq_vars_has_type_empty] \\ strip_tac \\
 fs [sum_map_def] \\ rveq \\ simp [vars_has_type_APPEND]);

val vars_has_type_mrun = Q.store_thm("vars_has_type_mrun",
 `!n ps tys fext vs vs'.
   vars_has_type vs tys /\ mrun fext ps vs n = INR vs' ==>
   vars_has_type vs' tys`,
 Induct \\ simp [mrun_def] \\ rpt strip_tac \\ drule_strip sum_bind_INR \\
 fs [sum_bind_def] \\ metis_tac [vars_has_type_mstep_commit]);

val get_var_mget_var = Q.store_thm("get_var_mget_var",
 `!vs nbq var. get_var <|vars := vs; nbq := nbq|> var = mget_var vs var`,
 rw [get_var_def, mget_var_def]);

(*
val WORD_get_1dim_VArray_data = Q.store_thm("WORD_get_1dim_VArray_data",
 `!w v. WORD w v ==> ?v'. get_1dim_VArray_data v = INR v' /\ VArray v' = w2ver w`,
 rw [WORD_def, get_1dim_VArray_data_def, w2ver_def, EVERY_isVBool_MAP_VBool, w2v_not_empty]);
*)

val _ = export_theory ();
