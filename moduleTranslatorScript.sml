open preamble;

open stringSyntax;

open verilogTheory verilogMetaTheory;
open translatorCoreLib translatorTheory;

open tinyConfigLib;

val _ = new_theory "moduleTranslator";

(* TODO: More or less duplicates relS, can be fixed... *)

val relM_var_def = Define `
 relM_var hol_s (mod_s:module) var a accessf =
  (?v. mget_var mod_s var = INR v /\ a (accessf hol_s) v)`;

fun build_relM_var (name, accessf) = let
  val nameHOL = fromMLstring name
  val pred = accessf |> dest_const |> snd |> dom_rng |> snd |> predicate_for_type_ty
in
  ``relM_var hol_s mod_s ^nameHOL ^pred ^accessf``
end;

val relM_def =
 accessors
 |> map build_relM_var
 |> list_mk_conj
(* |> (curry mk_icomb) (mk_icomb (equality, mk_comb (mk_comb (mk_var ("relM", ``:tinyImpl_state -> module -> bool``), mk_var ("hol_s", ``:tinyImpl_state``)), mk_var ("mod_s", ``:module``))))
 |> (curry new_definition) "relM";*)
 |> (fn tm => Define `relM hol_s mod_s = ^tm`);

(** Introduce non-blocking writes **)

val get_assn_var_def = Define `
 (get_assn_var (Var vname) = SOME vname) /\
 (get_assn_var (ArrayIndex vname _) = SOME vname) /\
 (get_assn_var (ArraySlice vname _ _ _) = SOME vname) /\
 (get_assn_var _  = NONE)`;

val intro_cvars_def = tDefine "intro_cvars" `
 (intro_cvars vars (Seq rp lp) = Seq (intro_cvars vars rp) (intro_cvars vars lp)) /\
 (intro_cvars vars (IfElse exp tp fp) = IfElse exp (intro_cvars vars tp)
                                                   (intro_cvars vars fp)) /\
 (intro_cvars vars (Case exp cases def) =
  Case exp
       (MAP (\(cond, p). (cond, (intro_cvars vars p))) cases)
       (OPTION_MAP (intro_cvars vars) def)) /\
 (intro_cvars vars (BlockingAssign lhs rhs) =
  case get_assn_var lhs of
      SOME name =>
      if MEM name vars
      then NonBlockingAssign lhs rhs
      else BlockingAssign lhs rhs
    | NONE => BlockingAssign lhs rhs) /\
 (intro_cvars _ p = p)`

 (WF_REL_TAC `measure (vprog_size o SND)` \\ rw [] \\
 imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

val intro_cvars_ind = fetch "-" "intro_cvars_ind";

val vwrites_intro_cvars_eq = Q.store_thm("vwrites_intro_cvars_eq",
 `!vars p var. MEM var (vwrites (intro_cvars vars p)) <=> MEM var (vwrites p) /\ ~MEM var vars`,
 recInduct intro_cvars_ind \\ rpt strip_tac \\ fs [intro_cvars_def, vwrites_def]
 >- metis_tac []
 >- metis_tac []
 >- (rw [MEM_FLAT, MEM_MAP] \\ EQ_TAC \\ strip_tac
    >- (rveq \\ PairCases_on `y'` \\ fs [] \\ res_tac \\ simp [] \\ disj1_tac \\
       qexists_tac `vwrites y'1` \\ simp [] \\ qexists_tac `(y'0, y'1)` \\ simp [])
    >- (Cases_on `def` \\ fs [] \\ res_tac \\ simp [])
    >- (rveq \\ PairCases_on `y` \\ fs [] \\ res_tac \\ disj1_tac \\
       qexists_tac `vwrites (intro_cvars vars y1)` \\ simp [] \\
       qexists_tac `(y0, intro_cvars vars y1)` \\ simp [] \\
       qexists_tac `(y0, y1)` \\ simp [])
    \\ Cases_on `def` \\ fs [])
 \\ Cases_on `lhs` \\ fs [get_assn_var_def, evwrites_def, vwrites_def] \\ EQ_TAC \\
    FULL_CASE_TAC \\ fs [vwrites_def, evwrites_def] \\ Cases_on `var = s` \\ simp []);

val not_vwrites_intro_cvars = Q.store_thm("not_vwrites_intro_cvars",
 `!var vars p. ~MEM var (vwrites p) ==> ~MEM var (vwrites (intro_cvars vars p))`,
 simp [vwrites_intro_cvars_eq]);

val vnwrites_intro_cvars_eq = Q.store_thm("vnwrites_intro_cvars_eq",
 `!vars p var. MEM var (vnwrites (intro_cvars vars p)) <=> MEM var (vwrites p) /\ MEM var vars \/
                                                           MEM var (vnwrites p)`,
 recInduct intro_cvars_ind \\ rpt strip_tac \\ fs [intro_cvars_def, vwrites_def, vnwrites_def]
 >- metis_tac []
 >- metis_tac []
 >- (rw [MEM_FLAT, MEM_MAP] \\ EQ_TAC \\ rpt strip_tac
    (* TODO: There's some duplication going on in these cases ... *)
    >- (rveq \\ PairCases_on `y'` \\ fs [] \\ last_x_assum drule \\ strip_tac \\ fs []
       >- (disj1_tac \\ disj1_tac \\ qexists_tac `vwrites y'1` \\ simp [] \\
          qexists_tac `(y'0,y'1)` \\ simp [])
       \\ disj2_tac \\ disj1_tac \\ qexists_tac `vnwrites y'1` \\ simp [] \\
          qexists_tac `(y'0,y'1)` \\ simp [])
    >- (Cases_on `def` \\ fs [] \\ res_tac \\ simp [])
    >- (disj1_tac \\ rveq \\ PairCases_on `y` \\ fs [] \\ last_x_assum drule \\ strip_tac \\
       qexists_tac `vnwrites (intro_cvars vars y1)` \\ simp [] \\
       qexists_tac `(y0, intro_cvars vars y1)` \\ simp [] \\
       qexists_tac `(y0, y1)` \\ simp [])
    >- (Cases_on `def` \\ fs [])
    >- (disj1_tac \\ rveq \\ PairCases_on `y` \\ fs [] \\ last_x_assum drule \\ strip_tac \\
       qexists_tac `vnwrites (intro_cvars vars y1)` \\ simp [] \\
       qexists_tac `(y0, intro_cvars vars y1)` \\ simp [] \\
       qexists_tac `(y0, y1)` \\ simp [])
    \\ (Cases_on `def` \\ fs []))
 \\ Cases_on `lhs` \\ fs [get_assn_var_def, evwrites_def, vnwrites_def] \\ EQ_TAC \\
    FULL_CASE_TAC \\ fs [vnwrites_def, evwrites_def] \\ Cases_on `var = s` \\ simp []);

val not_vnwrites_intro_cvars = Q.store_thm("not_vnwrites_intro_cvars",
 `!var vars p. ~MEM var (vwrites p) /\ ~MEM var (vnwrites p) ==> ~MEM var (vnwrites (intro_cvars vars p))`,
 metis_tac [vnwrites_intro_cvars_eq]);

val prun_intro_cvars_same_after = Q.store_thm("prun_intro_cvars_same_after",
 `!ver_s vars p v ver_s'.
   prun ver_s (intro_cvars vars p) = INR (v, ver_s') /\ vnwrites p = [] ==>
   !var. ~MEM var (vwrites p) ==> get_var ver_s' var = get_var ver_s var /\
                                  get_nbq_var ver_s' var = get_nbq_var ver_s var`,
 rpt strip_tac
 >- metis_tac [not_vwrites_intro_cvars, prun_same_after_general]
 \\ `~MEM var (vnwrites p)` by simp [] \\
    metis_tac [not_vnwrites_intro_cvars, prun_same_after_general]);

val prun_intro_cvars_same_after2 = Q.store_thm("prun_intro_cvars_same_after2",
 `!ver_s vars p v ver_s'.
   prun ver_s (intro_cvars vars p) = INR (v, ver_s') ==>
   !var. MEM var vars ==> get_var ver_s' var = get_var ver_s var`,
 rpt strip_tac \\ metis_tac [vwrites_intro_cvars_eq, prun_same_after_general]);

(* Can be generalized *)
val prun_intro_cvars_same_after3 = Q.store_thm("prun_intro_cvars_same_after3",
 `!ver_s vars p v ver_s'.
   prun ver_s (intro_cvars vars p) = INR (v, ver_s') /\ vnwrites p = [] ==>
   !var. ~MEM var vars ==> get_nbq_var ver_s' var = get_nbq_var ver_s var`,
  rpt strip_tac \\ `~MEM var (vnwrites p)` by simp [] \\
  metis_tac [vnwrites_intro_cvars_eq, prun_same_after_general]);

(*
val vwrites_intro_cvars = Q.store_thm("vwrites_intro_cvars",
 `!vars p. elems_not_in vars (vwrites (intro_cvars vars p))`,
 recInduct intro_cvars_ind \\ rpt strip_tac
 \\ (* Most cases *)
 TRY (fs [elems_not_in_def, vwrites_def, intro_cvars_def] \\ NO_TAC)

 >- (* Case *)
 (simp [intro_cvars_def, vwrites_def, elems_not_in_APPEND, elems_not_in_FLAT] \\ CONJ_TAC
  >- (simp [MAP_MAP_o, EVERY_MAP, EVERY_MEM] \\ Cases \\ rw [] \\ res_tac)
  \\ (Cases_on `def` \\ fs [elems_not_in_def]))

 \\ (* BlockingAssign *)
 (Cases_on `lhs` \\
 simp [intro_cvars_def, get_assn_var_def, vwrites_def, evwrites_def, elems_not_in_def] \\
 (* Only needed for the "difficult" cases: *)
 TOP_CASE_TAC \\ rw [vwrites_def, evwrites_def] \\ CCONTR_TAC \\ fs []));
*)

(** valid_ps_for_module **)

(* Processes are not allowed to read variables written non-blockingly from other modules,
   must use non-blocking writes for communication.

   If a module is valid, then the order processes are run in does not matter. *)
val valid_ps_for_module_def = Define `
  valid_ps_for_module vars ps = !p q. MEM p ps /\ MEM q ps /\ p <> q ==>
                                      (!x. ~MEM x vars /\ MEM x (vreads p) ==> ~MEM x (vwrites q)) /\
                                      (!x. MEM x (vwrites p) ==> ~MEM x (vwrites q))`;

val valid_ps_for_module_tl = Q.store_thm("valid_ps_for_module_tl",
 `!vars p ps. valid_ps_for_module vars (p::ps) ==>
              valid_ps_for_module vars ps`,
 rw [valid_ps_for_module_def] \\ metis_tac []);

val valid_ps_for_module_tl2 = Q.store_thm("valid_ps_for_module_tl2",
 `!vars p1 p2 ps. valid_ps_for_module vars (p1::p2::ps) ==>
                  valid_ps_for_module vars (p1::ps)`,
 once_rewrite_tac [valid_ps_for_module_def] \\ rpt strip_tac \\
 last_x_assum (qspecl_then [`p`, `q`] assume_tac) \\ metis_tac [MEM]);

(*
val valid_ps_for_module_tl_vwrites_NAMECOLL = Q.store_thm("valid_ps_for_module_tl_vwrites_NAMECOLL",
 `!ps p var vars.
  MEM var (vwrites p) /\ ALL_DISTINCT (p::ps) /\ valid_ps_for_module vars (p::ps) ==>
  EVERY (\p. ¬MEM var (vwrites p)) ps`,
 Induct >- rw [valid_ps_for_module_def] \\ rpt strip_tac \\
 last_x_assum drule \\ impl_tac
 >- (CONJ_TAC
    >- fs []
    \\ match_mp_tac valid_ps_for_module_tl2 \\ asm_exists_tac \\ fs [])
 \\ pop_assum mp_tac \\ rewrite_tac [valid_ps_for_module_def] \\
    disch_then (qspecl_then [`p`, `h`] assume_tac) \\ fs []);
*)

val valid_ps_for_module_tl_vreads = Q.store_thm("valid_ps_for_module_tl_vreads",
 `!h ps p var vars.
   valid_ps_for_module vars (h::ps) /\ MEM p ps /\ p <> h /\
   MEM var (vreads p) /\ ~MEM var vars ==> ~MEM var (vwrites h)`,
 rewrite_tac [valid_ps_for_module_def] \\ rpt strip_tac \\ last_x_assum (qspecl_then [`p`, `h`] mp_tac) \\
 impl_tac >- fs [] \\ strip_tac \\ metis_tac []);

val valid_ps_for_module_tl_vwrites = Q.store_thm("valid_ps_for_module_tl_vwrites",
 `!h ps p var vars.
   valid_ps_for_module vars (h::ps) /\ MEM p ps /\ p <> h /\
   MEM var (vwrites p) ==> ~MEM var (vwrites h)`,
 rewrite_tac [valid_ps_for_module_def] \\ rpt strip_tac \\ last_x_assum (qspecl_then [`p`, `h`] mp_tac) \\
 impl_tac >- fs [] \\ strip_tac \\ metis_tac []);

(* Just for the itp 2018 paper, not part of the formal development. *)
val valid_program_def = Define `
 valid_program ps = !p q. MEM p ps /\ MEM q ps /\ p <> q ==>
                     (!x. MEM x (vreads p) ==> ~MEM x (vwrites q)) /\
                     (!x. (MEM x (vnwrites p) \/ MEM x (vwrites p)) ==>
                          (~MEM x (vwrites q) /\ ~MEM x (vnwrites q)))`;

val relM_relS = Q.store_thm("relM_relS",
 `!s env ps. relM s <| vars := env; ps := ps |> ==> relS s <| vars := env; nbq := [] |>`,
 rw [relM_def, relS_def, relM_var_def, mget_var_def, relS_var_def, get_var_def] \\ fs []);

(*
val no_writes_before_read_exp_def = Define `
 no_writes_before_read_exp vars writes exp = EVERY (\v. MEM v vars ==> ~MEM v writes) (evreads exp)`;

val no_writes_before_read_def = tDefine "no_writes_before_read" `
 (no_writes_before_read vars writes Skip = T) /\
 (no_writes_before_read vars writes (Seq p1 p2) = (no_writes_before_read vars writes p1 /\
                                                   no_writes_before_read vars (vnwrites p1 ++ writes) p2)) /\
 (no_writes_before_read vars writes (IfElse c pt pf) = (no_writes_before_read_exp vars writes c /\
                                                        no_writes_before_read vars writes pt /\
                                                        no_writes_before_read vars writes pf)) /\
 (no_writes_before_read vars writes (Case m cs d) = (no_writes_before_read_exp vars writes m /\
                                                     EVERY (\(cc, cb). no_writes_before_read_exp vars writes cc /\
                                                                       no_writes_before_read vars writes cb)
                                                           cs /\
                                                     (case d of SOME d' => no_writes_before_read vars writes d'
                                                              | NONE => T))) /\
 (no_writes_before_read vars writes (BlockingAssign lhs rhs) = no_writes_before_read_exp vars writes rhs) /\
 (no_writes_before_read vars writes (NonBlockingAssign lhs rhs) = no_writes_before_read_exp vars writes rhs)`

 (WF_REL_TAC `measure (vprog_size o (\(a,b,c). c))` \\ rw [] \\
 imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);
*)

val cvar_writes_cond_def = tDefine "cvar_writes_cond" `
 (cvar_writes_cond vars (Seq p q) =
  (EVERY (\var. ~(MEM var (vwrites p) /\ MEM var (vwrites q))) vars /\
  cvar_writes_cond vars p /\ cvar_writes_cond vars q)) /\
 (cvar_writes_cond vars (IfElse _ p q) = (cvar_writes_cond vars p /\ cvar_writes_cond vars q)) /\
 (cvar_writes_cond vars (Case _ cs d) = (EVERY (\(_, p). cvar_writes_cond vars p) cs /\
                                         case d of SOME dp => cvar_writes_cond vars dp | NONE => T)) /\
 (cvar_writes_cond _ _ = T)`

 (WF_REL_TAC `measure (vprog_size o SND)` \\ rw [] \\
  imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

val prun_untainted_state = Q.store_thm("prun_untainted_state",
 `!vars ver_s p ver_s' v ver_s''.
  prun ver_s p = INR (v, ver_s') /\

  (* Conditions on what programs can be lifted *)
  vnwrites p = [] /\
  (!var. MEM var vars /\ MEM var (vreads p) ==> ~MEM var (vwrites p)) /\
  cvar_writes_cond vars p /\

  (* Conditions on the environment *)
  (!var. MEM var (vreads p) \/ MEM var (vwrites p) ==>
         get_var ver_s'' var = get_var ver_s var) /\
  (!var. MEM var vars /\ MEM var (vwrites p) ==>
         (get_nbq_var ver_s'' var = get_var ver_s var \/
         get_nbq_var ver_s'' var = get_nbq_var ver_s var))
  ==>
  ?ver_s'''. prun ver_s'' (intro_cvars vars p) = INR (v, ver_s''') /\
             (!var. MEM var (vreads p) \/ (~MEM var vars /\ MEM var (vwrites p)) ==>
                    get_var ver_s''' var = get_var ver_s' var) /\
             (!var. MEM var vars /\ MEM var (vwrites p) ==>
                    get_nbq_var ver_s''' var = get_var ver_s' var \/
                    (get_nbq_var ver_s''' var = get_nbq_var ver_s'' var /\
                     get_var ver_s''' var = get_var ver_s' var /\
                     get_var ver_s' var = get_var ver_s var))`,
 gen_tac \\ recInduct prun_ind \\ rpt strip_tac
 >- (* Skip *)
 fs [intro_cvars_def, prun_def, vwrites_def, vreads_def]
 >- (* Seq *)
 (fs [intro_cvars_def, prun_Seq, vwrites_def, vnwrites_def, vreads_def, cvar_writes_cond_def, EVERY_MEM] \\
 first_x_assum drule \\ disch_then (qspec_then `ver_s''` mp_tac) \\
 impl_tac >- (simp [] \\ metis_tac []) \\ strip_tac \\ simp [] \\
 first_x_assum drule \\ disch_then (qspec_then `ver_s'''` mp_tac) \\
 impl_tac \\ (* TOOD: inefficient but works: *)
 TRY (rpt strip_tac) \\ `~MEM var (vnwrites p0)` by fs [] \\ simp [] \\ metis_tac [prun_intro_cvars_same_after, prun_same_after_general])

 >- (* IfElse *)
 (fs [intro_cvars_def, prun_IfElse, vwrites_def, vnwrites_def, vreads_def, cvar_writes_cond_def, EVERY_MEM] \\
 first_x_assum drule \\ disch_then (qspec_then `ver_s''` mp_tac) \\
 (impl_tac >- (simp [] \\ metis_tac [])) \\ strip_tac \\ qexists_tac `ver_s'''` \\ simp [] \\
 (conj_tac >- metis_tac [erun_cong]) \\
 (* TODO: metis takes forever here *)
 conj_tac \\ gen_tac \\ metis_tac [prun_intro_cvars_same_after, prun_same_after_general])

 >- (* Case *)
 (fs [intro_cvars_def, prun_Case, vwrites_def, vnwrites_def, vreads_def, cvar_writes_cond_def, EVERY_MEM] \\
 last_x_assum drule \\ last_x_assum (fn _ => all_tac) \\
 TRY (disch_then drule) \\ disch_then (qspec_then `ver_s''` mp_tac) \\
 rpt (impl_tac >- (simp [] \\ metis_tac [])) \\
 strip_tac \\ simp [] \\
 `erun ver_s'' e = erun s e` by metis_tac [erun_cong] \\
 `erun ver_s'' ccond = erun s ccond` by metis_tac [erun_cong] \\ simp []
 >- (rveq \\ TRY strip_tac \\ metis_tac [prun_intro_cvars_same_after, prun_same_after_general])
 \\
 (* UGLY, TODO, OMG: *)
 qspecl_then [`ver_s''`, `vars`, `Case e cs default`] mp_tac prun_intro_cvars_same_after \\
 simp [intro_cvars_def, vnwrites_def, vwrites_def] \\ strip_tac \\

 qpat_x_assum `prun s _ = _` assume_tac \\
 drule prun_same_after_general \\ strip_tac \\

 strip_tac \\ gen_tac \\ Cases_on `MEM var (vwrites (Case e cs default))` \\
 fs [vwrites_def] \\ metis_tac [])

 >- (* Case ii *)
 (fs [intro_cvars_def, prun_def, vwrites_def, vnwrites_def, vreads_def, cvar_writes_cond_def, EVERY_MEM] \\
 last_x_assum (qspec_then `ver_s''` mp_tac) \\ impl_tac >- (simp [] \\ metis_tac []) \\
 strip_tac \\ asm_exists_tac \\ simp [] \\
 metis_tac [prun_intro_cvars_same_after, prun_same_after_general])

 >- (* Case iii *)
 fs [intro_cvars_def, prun_def, vwrites_def, vnwrites_def, vreads_def]

 >- (* BlockingAssign *)
 (fs [intro_cvars_def, prun_def, vwrites_def, vnwrites_def, vreads_def] \\
 imp_res_tac sum_bind_INR \\ fs [sum_bind_def, prun_bassn_def] \\
 imp_res_tac sum_for_INR \\ fs [sum_for_def, sum_map_def] \\

 `erun ver_s'' rhs = erun s rhs` by metis_tac [erun_cong] \\

 qabbrev_tac `lhs_ = lhs` \\
 Cases_on `lhs` \\ TRY (unabbrev_all_tac \\ fs [assn_def] \\ NO_TAC) \\

 `(!var. MEM var (evreads lhs_) ==> get_var ver_s'' var = get_var s var)`
 by (unabbrev_all_tac \\ fs [evwrites_def, evreads_def, evreads_index_def] \\ metis_tac []) \\

 `assn ver_s'' lhs_ v' = assn s lhs_ v'` by metis_tac [assn_cong] \\

 unabbrev_all_tac \\
 (* UGLY: Can we rewrite this directly instead of using imp_res_tac? *)
 imp_res_tac assn_Var_INR \\ imp_res_tac assn_ArrayIndex_INR \\
 rveq \\ fs [] \\ rveq \\

 simp [get_assn_var_def] \\ Cases_on `MEM s' vars` \\
 simp [prun_def, sum_bind_def, sum_for_def, sum_map_def, prun_bassn_def, prun_nbassn_def] \\
 fs [evreads_def, evwrites_def, get_var_set_var, get_var_cleanup, get_nbq_var_def] \\ metis_tac [])

 \\ (* NonBlockingAssign *)
 fs [prun_def] \\ imp_res_tac sum_bind_INR \\ fs [sum_bind_def, prun_nbassn_def] \\
 imp_res_tac sum_for_INR \\ fs [sum_for_def, sum_map_def] \\ rveq \\
 Cases_on `lhs` \\ fs [vnwrites_def, evwrites_def, assn_def]);

val mstep_unfold1 = Q.store_thm("mstep_unfold1",
 `!ps p ver_s ver_s' vars.
  mstep ver_s (p::ps) = INR ver_s' <=>
  ?ver_s''. prun ver_s p = INR (NONE, ver_s'') /\
            mstep ver_s'' ps = INR ver_s'`,
  rw [mstep_def, sum_foldM_def] \\ EQ_TAC \\ strip_tac
  >- (imp_res_tac sum_bind_INR \\ fs [sum_bind_def] \\
     imp_res_tac sum_map_INR \\ fs [sum_map_def] \\
     PairCases_on `v''` \\ imp_res_tac prun_val_always_NONE \\ fs [])
  \\ fs [sum_map_def, sum_bind_def]);

val relS_with_same_vars = Q.store_thm("relS_with_same_vars",
 `!s ver_s. relS s ver_s ==> relS s (ver_s with vars := ver_s.vars)`,
 rw [relS_def, relS_var_def, get_var_def]);

val pstate_vars_cleanup = Q.store_thm("pstate_vars_cleanup",
 `!(ver_s:pstate). ver_s with vars := ver_s.vars = ver_s`,
 rw [pstate_component_equality]);

val mstep_no_writes = Q.store_thm("mstep_no_writes",
 `!ps var vars ver_s ver_s'.
  EVERY (\p. ~MEM var (vwrites p)) ps /\
  EVERY (\p. vnwrites p = []) ps /\
  mstep ver_s (MAP (intro_cvars vars) ps) = INR ver_s' ==>
  get_var ver_s' var = get_var ver_s var /\
  get_nbq_var ver_s' var = get_nbq_var ver_s var`,
 Induct >- rw [mstep_def, sum_foldM_def] \\
 rpt gen_tac \\ strip_tac \\ fs [mstep_unfold1] \\
 metis_tac [prun_intro_cvars_same_after]);

val mstep_untainted_state = Q.store_thm("mstep_untainted_state",
 `!vars ps ver_s ver_s' s Penv.
  Penv ver_s.vars /\
  (* Conditions on what programs can be lifted *)
  (!p. MEM p ps ==> (?s'. !env. Penv env ==> EvalS s env s' p) /\
                    vnwrites p = [] /\
                    cvar_writes_cond vars p /\
                    (!var. MEM var vars /\ MEM var (vreads p) ==> ~MEM var (vwrites p))) /\
  ALL_DISTINCT ps /\

  (* Conditions on the environment *)
  relS s ver_s /\
  valid_ps_for_module vars ps /\

  (!p. MEM p ps ==>
  (!var. MEM var (vreads p) \/ MEM var (vwrites p) ==>
         get_var ver_s' var = get_var ver_s var) /\
  (!var. MEM var (vwrites p) ==>
         get_nbq_var ver_s' var = get_nbq_var ver_s var))
  ==>
  ?ver_s''. mstep ver_s' (MAP (intro_cvars vars) ps) = INR ver_s'' /\
            (!p. MEM p ps ==>
             (?ver_s_p. prun ver_s p = INR (NONE, ver_s_p) /\
             (!var. MEM var (vwrites p) ==>
              if MEM var vars
              then get_nbq_var ver_s'' var = get_var ver_s_p var \/
                   (get_nbq_var ver_s'' var = get_nbq_var ver_s' var /\
                   get_var ver_s'' var = get_var ver_s_p var)
              else get_var ver_s'' var = get_var ver_s_p var /\
                   get_nbq_var ver_s'' var = get_nbq_var ver_s' var)))`,
 gen_tac \\ Induct >- rw [mstep_def, sum_foldM_def] \\
 simp [mstep_unfold1] \\ Ho_Rewrite.ONCE_REWRITE_TAC [MEM_disj_impl] \\ simp [] \\ rpt strip_tac \\
 CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV) \\

 (* TODO: This is ugly... *)
 imp_res_tac relS_with_same_vars \\
 first_x_assum drule \\ disch_then (drule o (PURE_REWRITE_RULE [EvalS_def])) \\
 simp [pstate_vars_cleanup] \\ strip_tac \\

 drule prun_untainted_state \\ rpt (disch_then drule) \\
 (*disch_then (qspec_then `ver_s'` mp_tac) \\*)
 impl_tac >- (simp [] \\ metis_tac []) \\ strip_tac \\
 asm_exists_tac \\ simp [] \\

 imp_res_tac valid_ps_for_module_tl \\
 last_x_assum drule \\ disch_then (qspec_then `ver_s'''` mp_tac) \\ rpt (disch_then drule) \\
 impl_tac >- metis_tac [valid_ps_for_module_tl_vreads, valid_ps_for_module_tl_vwrites,
                        prun_intro_cvars_same_after, prun_intro_cvars_same_after2] \\
 strip_tac \\ simp [] \\
 `EVERY (\p. vnwrites p = []) ps` by (rw [EVERY_MEM]) \\
 rpt strip_tac

 >- (`EVERY (\p. ~MEM var (vwrites p)) ps` by (simp [EVERY_MEM] \\
                                              metis_tac [valid_ps_for_module_tl_vwrites]) \\
 metis_tac [valid_ps_for_module_tl_vwrites, prun_intro_cvars_same_after3, mstep_no_writes])

 \\ (*first_x_assum drule \\ strip_tac \\ asm_exists_tac \\ simp [] \\ rpt strip_tac \\
    first_x_assum drule \\ strip_tac \\ `p <> h` by metis_tac [MEM] \\*)
    metis_tac [valid_ps_for_module_tl_vwrites, prun_intro_cvars_same_after]);

(* Useful for variables never written to *)
val mget_var_mstep_no_writes = Q.store_thm("mget_var_mstep_no_writes",
 `!ps var vars ver_s ver_s'.
  mstep ver_s (MAP (intro_cvars vars) ps) = INR ver_s' /\
  EVERY (\p. ~MEM var (vwrites p)) ps /\
  EVERY (\p. vnwrites p = []) ps /\
  get_nbq_var ver_s var = INL UnknownVariable ==>
  mget_var <| vars := ver_s'.nbq ++ ver_s'.vars; ps := MAP (intro_cvars vars) ps |> var =
  get_var ver_s var`,
 rw [mget_var_def, alistTheory.ALOOKUP_APPEND] \\ drule mstep_no_writes \\
 rpt (disch_then drule) \\ EVERY_CASE_TAC \\ fs [get_var_def, get_nbq_var_def]);

val _ = export_theory();
