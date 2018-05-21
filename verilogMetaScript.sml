open preamble;

open verilogTheory bitstringTheory;

val _ = new_theory "verilogMeta";

(** Some simpl thms about the sum type **)

val sum_EL_EL = Q.store_thm("sum_EL_EL",
 `!i l. i < LENGTH l ==> sum_EL i l = INR (EL i l)`,
 Induct \\ Cases_on `l` \\ fs [sum_EL_def]);

val sum_EL_eq_EL = Q.store_thm("sum_EL_eq_EL",
 `!i l e. i < LENGTH l ==> (sum_EL i l = INR e <=> EL i l = e)`,
 Induct \\ rpt strip_tac \\ Cases_on `l` \\ fs [sum_EL_def]);

val sum_EL_LENGTH = Q.store_thm("sum_EL_LENGTH",
 `!xs x y. sum_EL (LENGTH xs) (xs ++ [x]) = INR x`,
 Induct \\ rw [sum_EL_def]);

(*
val sum_revEL_0 = Q.store_thm("sum_revEL_0",
 `!xs x y. sum_revEL 0 (xs ++ [x]) = INR y ==> x = y`,
 rw [sum_revEL_def, sum_EL_def] \\ metis_tac [sum_EL_LENGTH]);
*)

val sum_EL_LENGTH_INR_LENGTH = Q.store_thm("sum_EL_LENGTH_INR_LENGTH",
 `!n xs x y. n < LENGTH xs /\ sum_EL (LENGTH xs − n) (x::xs) = INR y ==>
             sum_EL (LENGTH xs − (n + 1)) xs = INR y`,
 rpt strip_tac \\ `LENGTH xs − (n + 1) = LENGTH xs − n - 1` by DECIDE_TAC \\
 pop_assum (fn th => REWRITE_TAC [th]) \\
 Cases_on `LENGTH xs − n` \\ fs [sum_EL_def]);

val sum_EL_APPEND_EQN = Q.store_thm("sum_EL_APPEND_EQN",
 `!l1 l2 n.
   sum_EL n (l1 ++ l2) = if n < LENGTH l1 then sum_EL n l1 else sum_EL (n − LENGTH l1) l2`,
 Induct \\ rw [] \\ Cases_on `n` \\ fs [sum_EL_def]);

val sum_revEL_LENGTH = Q.store_thm("sum_revEL_LENGTH",
 `!xs x. sum_revEL (LENGTH xs) (x::xs) = INR x`,
 Induct \\ rw [sum_revEL_def, sum_EL_def]);

val sum_revEL_APPEND_EQN = Q.store_thm("sum_revEL_APPEND_EQN",
 `!l2 l1 n.
   sum_revEL n (l1 ++ l2) =
   if n < LENGTH l2 then sum_revEL n l2 else sum_revEL (n − LENGTH l2) l1`,
 rw [sum_revEL_def] \\ fs [sum_EL_APPEND_EQN]);

(*
val sum_revEL_APPEND_single = Q.store_thm("sum_revEL_APPEND_single",
 `!n xs x. sum_revEL (SUC n) (xs ++ [x]) = sum_revEL n xs`,
 rw [sum_revEL_def, sum_EL_APPEND_EQN, ADD1]);
*)

val sum_revEL_0 = Q.store_thm("sum_revEL_0",
 `!xs x. sum_revEL 0 (xs ++ [x]) = INR x`,
 Induct \\ rw [sum_revEL_def, sum_EL_def, sum_EL_LENGTH]);

val sum_revEL_INR_LENGTH = Q.store_thm("sum_revEL_INR_LENGTH",
 `!n xs x y. n < LENGTH xs /\ sum_revEL n (x::xs) = INR y ==> sum_revEL n xs = INR y`,
 rw [sum_revEL_def] \\ metis_tac [sum_EL_LENGTH_INR_LENGTH]);

(*

 `!xs x y n.
   n < LENGTH xs /\
   sum_revEL n (x::xs) = INR y ==>
   sum_revEL n xs = INR y`,
 Induct \\ rw [sum_revEL_def, sum_EL_def]

val sum_revEL_dimindex = Q.store_thm("sum_revEL_dimindex",
 `!(i:'a word) xs x y.
(*   SUC (LENGTH xs) <= dimindex (:'a) /\ *)
   LENGTH xs < dimindex (:'a) /\
   sum_revEL (w2n i) (x::xs) = INR y ==>
   sum_revEL (w2n i) xs = INR y`,
 rpt strip_tac \\ w2n_lt
*)


(** variables **)

val get_var_set_var = Q.store_thm("get_var_set_var",
 `!s var v var'.
  get_var (set_var s var v) var' = if var = var' then INR v else get_var s var'`,
 rw [set_var_def, get_var_def]);

val get_var_cleanup = Q.store_thm("get_var_cleanup",
 `!s nbq var. get_var (s with nbq := nbq) var = get_var s var`,
 rw [get_var_def]);

val get_nbq_var_set_var = Q.store_thm("get_nbq_var_set_var",
 `!s var v var'.
  get_nbq_var (set_var s var v) var' = get_nbq_var s var'`,
 rw [set_var_def, get_nbq_var_def]);

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
 `!p p' s s' v.
   prun s (Seq p p') = INR (v, s') <=> ?sm vm. prun s p = INR (vm, sm) /\ prun sm p' = INR (v, s')`,
 rw [prun_def] \\ Cases_on `prun s p` \\ fs [sum_bind_def] \\ PairCases_on `y` \\ fs []);

val prun_IfElse = Q.store_thm("prun_IfElse",
 `!s c pt pf v s'.
   prun s (IfElse c pt pf) = INR (v, s') <=>
   (prun s pt = INR (v, s') /\ erun s c = INR (VBool T)) \/
   (prun s pf = INR (v, s') /\ erun s c = INR (VBool F))`,
 rpt gen_tac \\ EQ_TAC \\ rw [prun_def] \\ fs [sum_bind_def, get_VBool_data_def] \\
 Cases_on `erun s c` \\ fs [sum_bind_def] \\
 Cases_on `y` \\ fs [get_VBool_data_def, sum_bind_def] \\
 Cases_on `b` \\ fs []);

val prun_Case = Q.store_thm("prun_Case",
 `!s e ccond cprog cs default v s'.
   prun s (Case e ((ccond, cprog)::cs) default) = INR (v, s') <=>
   ?e' ccond'. erun s e = INR e' /\
   erun s ccond = INR ccond' /\
   ((prun s cprog = INR (v, s') /\ e' = ccond') \/
   (prun s (Case e cs default) = INR (v, s') /\ e' <> ccond'))`,
 rw [prun_def] \\ EQ_TAC \\ strip_tac
 >- (Cases_on `erun s e` \\ fs [sum_bind_def] \\ Cases_on `erun s ccond` \\ fs [sum_bind_def] \\
    Cases_on `y = y'` \\ fs [])
 \\ fs [sum_bind_def]);

(** erun read/write thms **)

val erun_cong = Q.store_thm("erun_cong",
 `!s exp s'.
  (!var. MEM var (evreads exp) ==> get_var s var = get_var s' var) ==>
  erun s exp = erun s' exp`,
 recInduct erun_ind \\ rw [erun_def, evreads_def, MEM_FLAT, MEM_MAP] \\ metis_tac [sum_mapM_cong]);

(** prun read/write thms **)

(* NOTE: Could have evreads_index as precond here, but slice updates etc. updates
         whole value, not just part... *)
val assn_cong = Q.store_thm("assn_cong",
 `!lhs s s' rhs.
   (!var. MEM var (evreads lhs) ==> get_var s var = get_var s' var) ==>
   assn s lhs rhs = assn s' lhs rhs`,
 Induct \\ rw [evwrites_def, evreads_def, assn_def] \\
 Cases_on `l` \\ simp [assn_def] \\
 Cases_on `t` \\ simp [assn_def] \\ fs [] \\
 `erun s'' h = erun s' h` by metis_tac [erun_cong] \\ simp []);

val assn_Var_INR = Q.store_thm("assn_Var_INR",
 `!s var v r. assn s (Var var) v = INR r ==> r = (var, v)`,
 rw [assn_def] \\ imp_res_tac sum_bind_INR \\ fs [sum_bind_def]);

val assn_ArrayIndex_INR = Q.store_thm("assn_ArrayIndex_INR",
 `!s var es v r. assn s (ArrayIndex var es) v = INR r ==> ?v'. r = (var, v')`,
 rpt gen_tac \\ Cases_on `es` \\ simp [assn_def] \\ Cases_on `t` \\ simp [assn_def] \\
 strip_tac \\ rpt (CHANGED_TAC (imp_res_tac sum_bind_INR \\ fs [sum_bind_def])) \\
 fs [prun_set_var_index_def] \\ last_x_assum mp_tac \\ CASE_TAC \\ simp [] \\ strip_tac \\
 imp_res_tac sum_for_INR \\ fs [sum_for_def, sum_map_def] \\ metis_tac []);

val prun_val_always_NONE = Q.store_thm("prun_val_always_NONE",
 `!ver_s p v ver_s'. prun ver_s p = INR (v, ver_s') ==> v = NONE`,
 recInduct prun_ind \\ rpt strip_tac
 \\ TRY (fs [prun_def] \\ NO_TAC)
 >- metis_tac [prun_Seq]
 >- metis_tac [prun_IfElse]
 >- metis_tac [prun_Case]
 (* Blocking and non-blocking assign *)
 \\ (fs [prun_def] \\ imp_res_tac sum_bind_INR \\ fs [sum_bind_def, prun_bassn_def, prun_nbassn_def] \\
    imp_res_tac sum_for_INR \\ fs [sum_for_def, sum_map_def] \\ Cases_on `v''` \\ fs []));

val prun_same_after_general = Q.store_thm("prun_same_after_general",
 `!ver_s p v ver_s'.
 prun ver_s p = INR (v, ver_s') ==>
 (!var. ~MEM var (vwrites p) ==> get_var ver_s' var = get_var ver_s var) /\
 (!var. ~MEM var (vnwrites p) ==> get_nbq_var ver_s' var = get_nbq_var ver_s var)`,
 recInduct prun_ind \\ rpt conj_tac \\ rpt gen_tac \\ rpt disch_tac \\
 TRY (fs [prun_def, vwrites_def, vnwrites_def] \\ NO_TAC)
 >- (rpt strip_tac \\ fs [prun_Seq, vwrites_def, vnwrites_def] \\ res_tac \\ fs [])
 >- (rpt strip_tac \\ fs [prun_IfElse, vwrites_def, vnwrites_def])
 >- (rpt strip_tac \\ fs [prun_Case, vwrites_def, vnwrites_def] \\ res_tac)
 \\ (* BlockingAssign and NonBlockingAssign *)
    (fs [prun_def, vwrites_def, vnwrites_def] \\ imp_res_tac sum_bind_INR \\
    fs [sum_bind_def, prun_bassn_def, prun_nbassn_def] \\
    Cases_on `lhs` \\ fs [assn_def, sum_for_def, sum_map_def, evwrites_def]
    >- (imp_res_tac sum_map_INR \\ fs [sum_map_def] \\
       imp_res_tac sum_bind_INR \\ fs [sum_bind_def] \\ rveq \\
       fs [get_var_set_var, get_nbq_var_set_var, get_var_def, get_nbq_var_def])
    \\ (imp_res_tac sum_map_INR \\ fs [sum_map_def] \\
       (* Only simple case implemented in semantics *)
       Cases_on `l` \\ fs [assn_def] \\ Cases_on `t` \\ fs [assn_def] \\
       rpt (CHANGED_TAC (imp_res_tac sum_bind_INR \\ fs [sum_bind_def])) \\
       fs [prun_set_var_index_def] \\ FULL_CASE_TAC \\ fs [sum_for_def, sum_map_def] \\
       imp_res_tac sum_map_INR \\ fs [sum_map_def] \\ rveq \\ fs [] \\ rveq \\
       fs [get_var_set_var, get_nbq_var_set_var, get_var_def, get_nbq_var_def])));

(* Specialization for backwards comp *)
val prun_same_after = Q.store_thm("prun_same_after",
 `!ver_s p v ver_s'.
 prun ver_s p = INR (v, ver_s') ==>
 !var. ~MEM var (vwrites p) ==> get_var ver_s' var = get_var ver_s var`,
 metis_tac [prun_same_after_general]);

val prun_same_before_Case_NONE = Q.store_thm("prun_same_before_Case_NONE",
 `!cs var s s' e v.
  ~MEM var (FLAT (MAP (λ(_, cb). vwrites cb) cs)) /\
  prun s (Case e cs NONE) = INR (v, s') ==>
  get_var s' var = get_var s var`,
 Induct >- rw [prun_def] \\ Cases \\ rpt strip_tac \\ fs [prun_Case] \\ metis_tac [prun_same_after]);

val prun_same_before_Case_SOME = Q.store_thm("prun_same_before_Case_SOME",
 `!cs var s s' e default v.
  ~MEM var (FLAT (MAP (λ(_,cb). vwrites cb) cs)) /\
  ~MEM var (vwrites default) /\
  prun s (Case e cs (SOME default)) = INR (v, s') ==>
  get_var s' var = get_var s var`,
 Induct >- metis_tac [prun_def, prun_same_after] \\ Cases \\ rpt strip_tac \\
 fs [prun_Case] \\ metis_tac [prun_same_after]);

(*
(* TODO: Not used anywhere as far as I know, containes cheats *)
val prun_same_before = Q.store_thm("prun_same_before",
 `!s p v s' s''.
  prun s p = INR (v, s') /\
  (!var. MEM var (vreads p) ==> get_var s'' var = get_var s var) /\
  (!var. MEM var (vwrites p) ==> get_var s'' var = get_var s var)
  ==>
  ?s'''. prun s'' p = INR (v, s''') /\
         (!var. MEM var (vreads p) ==> get_var s''' var = get_var s' var) /\
         (!var. MEM var (vwrites p) ==> get_var s''' var = get_var s' var)`,
 recInduct prun_ind \\ rpt strip_tac
 >- fs [prun_def, vwrites_def]
 >- (* Seq *)
    (fs [prun_Seq, vreads_def, vwrites_def, MEM_disj_impl] \\
    first_x_assum drule \\ disch_then (qspec_then `s''` drule) \\ disch_then drule \\ strip_tac \\
    first_x_assum drule \\ disch_then (qspec_then `s'''` mp_tac) \\ impl_tac \\
    strip_tac \\ fs [] \\ metis_tac [prun_same_after])
 >- (* IfElse *)
    (fs [vreads_def, vwrites_def, MEM_disj_impl] \\
    imp_res_tac erun_cong \\ fs [prun_IfElse] \\
    first_x_assum drule \\ disch_then drule \\ disch_then drule \\ strip_tac \\ fs [] \\
    CONV_TAC (DEPTH_CONV AND_FORALL_CONV) \\ gen_tac \\
    metis_tac [prun_same_after])
 >- (* Case *)
    (fs [vreads_def, vwrites_def, MEM_disj_impl] \\
    imp_res_tac erun_cong \\ fs [prun_Case] \\
    first_x_assum drule
     >- (disch_then (qspec_then `s''` drule) \\ disch_then drule \\
        strip_tac \\ asm_exists_tac \\ fs [] \\ metis_tac [prun_same_after])
     \\ (disch_then drule \\ disch_then (qspec_then `s''` mp_tac) \\ impl_tac >- fs [] \\
        rpt (disch_then drule) \\ strip_tac \\ asm_exists_tac \\ fs [] \\
        CONV_TAC (DEPTH_CONV AND_FORALL_CONV) \\ gen_tac \\
        pop_assum mp_tac \\ TOP_CASE_TAC \\ fs []
         >- (Cases_on `MEM var (FLAT (MAP (λ(_,cb). vwrites cb) cs))` >- metis_tac [] \\
            metis_tac [prun_same_before_Case_NONE, prun_same_after])
         \\ (Cases_on `MEM var (FLAT (MAP (λ(_,cb). vwrites cb) cs)) \/ MEM var (vwrites x)`
            >- metis_tac [] \\ metis_tac [prun_same_before_Case_SOME, prun_same_after])))
 >- (* Case ii *)
    (fs [prun_def, vreads_def, vwrites_def, MEM_disj_impl] \\ last_x_assum drule \\
    disch_then drule \\ strip_tac \\ asm_exists_tac \\ fs [] \\ metis_tac [prun_same_after])
 >- (* Case iii *)
    (fs [prun_def, vreads_def, vwrites_def, MEM_disj_impl] \\ last_x_assum drule \\
    disch_then drule \\ strip_tac \\ asm_exists_tac \\ fs [] \\ metis_tac [prun_same_after])
 >- (* BlockingAssign *)
    cheat
 >- (* NonBlockingAssing *)
    cheat);
*)

(*
val prun_same_both = Q.store_thm("prun_same_both",
 `!s p v s' s''.
   prun s p = INR (v, s') /\
   (!var. MEM var (vreads p) ==> get_var s'' var = get_var s var) /\
   (!var. MEM var (vwrites p) ==> get_var s'' var = get_var s var)
   ==>
   ?s'''. prun s'' p = INR (v, s''') /\
          (!var. get_var s''' var = if MEM var (vwrites p) then
                                    get_var s' var
                                    else if MEM var (vreads p) then
                                    get_var s var
                                    else
                                    get_var s'' var)`,
 cheat);
*)

(* NOT TRUE, need to include writes also, consider Seq case:
val prun_same_varP = Q.store_thm("prun_same_varP",
  `!varP s p v s' s''.
  prun s p = INR (v, s') /\
  (!var. MEM var (vreads p) ==> get_var s'' var = get_var s var) /\
  (!var. varP var ==> get_var s'' var = get_var s var)
  ==>
  ?s'''. prun s'' p = INR (v, s''') /\
         (!var. MEM var (vreads p) \/ varP var ==>
                get_var s''' var = get_var s' var)`,
 gen_tac \\ recInduct prun_ind \\ rpt strip_tac
 >- (* Skip *)
 (fs [prun_def] \\ metis_tac [])
 >- (* Seq *)
 (fs [prun_Seq, vreads_def, MEM_disj_impl] \\
 first_x_assum drule \\ disch_then (qspec_then `s''` drule) \\ disch_then drule \\ strip_tac \\
 first_x_assum drule \\ disch_then (qspec_then `s'''''` mp_tac) \\ impl_tac \\
 >- rpt strip_tac \\ fs [] \\ *)

(** misc thms, vnwrites correct etc. **)

val vnwrites_nil_correct = Q.store_thm("vnwrites_nil_correct",
 `!ver_s p env v ver_s'.
   vnwrites p = [] /\
   prun ver_s p = INR (v, ver_s')
   ==>
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
 Cases_on `lhs` \\ fs [assn_def, evwrites_def]));

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

(*
val WORD_get_1dim_VArray_data = Q.store_thm("WORD_get_1dim_VArray_data",
 `!w v. WORD w v ==> ?v'. get_1dim_VArray_data v = INR v' /\ VArray v' = w2ver w`,
 rw [WORD_def, get_1dim_VArray_data_def, w2ver_def, EVERY_isVBool_MAP_VBool, w2v_not_empty]);
*)

val _ = export_theory ();
