open hardwarePreamble;

open pred_setTheory;

open stringSyntax;

open sumExtraTheory verilogTheory verilogTypeTheory verilogMetaTheory;
open verilogTranslatorTheory;

open verilogTranslatorConfigLib verilogTranslatorCoreLib;

val _ = new_theory "moduleTranslator";

(* TODO: More or less duplicates relS, can be fixed... *)

val relM_var_def = Define `
 relM_var hol_s (vs:envT) var a accessf =
  (?v. sum_alookup vs var = INR v /\ a (accessf hol_s) v)`;

fun build_relM_var (name, accessf) = let
  val nameHOL = fromMLstring name
  val pred = accessf |> dest_const |> snd |> dom_rng |> snd |> predicate_for_type_ty
in
  ``relM_var hol_s vs ^nameHOL ^pred ^accessf``
end;

val relM_def =
 accessors
 |> map build_relM_var
 |> list_mk_conj
 |> (fn tm => Define `relM hol_s vs = ^tm`);

fun build_relM_type (name, accessf) = let
  val nameHOL = fromMLstring name
  val ty = accessf |> dest_const |> snd |> dom_rng |> snd |> verty_for_type
in
  ``(^nameHOL, ^ty)``
end;

val relMtypes_def =
 accessors
 |> map build_relM_type
 |> (fn tms => listSyntax.mk_list (tms, ``:string # vertype``))
 |> (fn tm => Define `relMtypes = ^tm`);

val lift_fext_vars =
 zip (TypeBase.fields_of fext_ty |> map (fn (f, info) => (f, #ty info)))
     (TypeBase.accessors_of fext_ty |> map (rator o lhs o snd o strip_forall o concl))
 |> filter (fn ((name, _), _) => not (mem name model_fext_vars));

val lift_fext_others =
 lift_fext_vars
 |> map (fromMLstring o fst o fst);

val lift_fext_def =
 lift_fext_vars
 |> map (fn ((f, ty), accessor) => (fromMLstring f, hol2ver_for_type ty, accessor))
 |> map (fn (f, ty, accessor) => ``fextv (n:num) ^f = INR (^ty (^accessor (fext n)))``)
 |> flip append [build_fextv_others true lift_fext_others]
 |> list_mk_conj |> inst [ alpha |-> ``:error`` ]
 |> (fn tm => Define `lift_fext fextv fext = !n. ^tm`);

val lift_fext_unique = Q.store_thm("lift_fext_unique",
 `!fext fextv1 fextv2.
   lift_fext fextv1 fext /\ lift_fext fextv2 fext ==> fextv1 = fextv2`,
 rw [lift_fext_def, FUN_EQ_THM] \\
 qmatch_goalsub_rename_tac `fextv1 _ var` \\
 MAP_EVERY (fn var => Cases_on `var = ^var` >- rw []) lift_fext_others \\
 fs []);

val lift_fext_relS_fextv_fext = Q.store_thm("lift_fext_relS_fextv_fext",
 `!fextv fext. lift_fext fextv fext <=> (!n. relS_fextv (fextv n) (fext n))`,
 rw [lift_fext_def, relS_fextv_def]);

(** Introduce non-blocking writes **)

val intro_cvars_def = tDefine "intro_cvars" `
 (intro_cvars vars (Seq rp lp) = Seq (intro_cvars vars rp) (intro_cvars vars lp)) /\
 (intro_cvars vars (IfElse exp tp fp) = IfElse exp (intro_cvars vars tp)
                                                   (intro_cvars vars fp)) /\
 (intro_cvars vars (Case ty exp cases def) =
  Case ty exp
       (MAP (\(cond, p). (cond, (intro_cvars vars p))) cases)
       (OPTION_MAP (intro_cvars vars) def)) /\
 (intro_cvars vars (BlockingAssign lhs rhs) =
  if MEM (evwrites lhs) vars
  then NonBlockingAssign lhs rhs
  else BlockingAssign lhs rhs) /\
 (intro_cvars _ p = p)`

 (WF_REL_TAC `measure (vprog_size o SND)` \\ rw [] \\
 imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

val intro_cvars_ind = fetch "-" "intro_cvars_ind";

val intro_cvars_nil_help = Q.prove(
 `!vars p. vars = [] ==> intro_cvars vars p = p`,
 recInduct intro_cvars_ind \\ rw [intro_cvars_def]
 >- (Induct_on `cases` \\ rw []
    >- (pairarg_tac \\ simp [])
    \\ metis_tac [])
 >- (Cases_on `def` \\ fs [])
 \\ every_case_tac \\ simp []);

val intro_cvars_nil = Q.store_thm("intro_cvars_nil",
 `!p. intro_cvars [] p = p`,
 rw [intro_cvars_nil_help]);

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
 \\ Cases_on `lhs` \\ fs [vwrites_def, evwrites_def] \\
    TRY (Cases_on `e`) \\ rw [vwrites_def, evwrites_def] \\
    Cases_on `var = s` \\ simp []);

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
 \\ Cases_on `lhs` \\ fs [vnwrites_def, evwrites_def] \\
    TRY (Cases_on `e`) \\ rw [vnwrites_def, evwrites_def] \\
    Cases_on `var = s` \\ simp []);

val not_vnwrites_intro_cvars = Q.store_thm("not_vnwrites_intro_cvars",
 `!var vars p. ~MEM var (vwrites p) /\ ~MEM var (vnwrites p) ==> ~MEM var (vnwrites (intro_cvars vars p))`,
 metis_tac [vnwrites_intro_cvars_eq]);

val prun_intro_cvars_same_after = Q.store_thm("prun_intro_cvars_same_after",
 `!fext ver_s vars p ver_s'.
   prun fext ver_s (intro_cvars vars p) = INR ver_s' /\ vnwrites p = [] ==>
   !var. ~MEM var (vwrites p) ==> get_var ver_s' var = get_var ver_s var /\
                                  get_nbq_var ver_s' var = get_nbq_var ver_s var`,
 rpt strip_tac
 >- metis_tac [not_vwrites_intro_cvars, prun_same_after]
 \\ `~MEM var (vnwrites p)` by simp [] \\
    metis_tac [not_vnwrites_intro_cvars, prun_same_after]);

val prun_intro_cvars_same_after2 = Q.store_thm("prun_intro_cvars_same_after2",
 `!fext ver_s vars p ver_s'.
   prun fext ver_s (intro_cvars vars p) = INR ver_s' ==>
   !var. MEM var vars ==> get_var ver_s' var = get_var ver_s var`,
 rpt strip_tac \\ metis_tac [vwrites_intro_cvars_eq, prun_same_after]);

(* Can be generalized *)
val prun_intro_cvars_same_after3 = Q.store_thm("prun_intro_cvars_same_after3",
 `!fext ver_s vars p ver_s'.
   prun fext ver_s (intro_cvars vars p) = INR ver_s' /\ vnwrites p = [] ==>
   !var. ~MEM var vars ==> get_nbq_var ver_s' var = get_nbq_var ver_s var`,
  rpt strip_tac \\ drule_strip prun_same_after \\ fs [vnwrites_intro_cvars_eq]);

(** valid_ps_for_module **)

(* Processes are not allowed to read variables written non-blockingly from other modules,
   must use non-blocking writes for communication.

   If a module is valid, then the order processes are run in does not matter. *)
val all_idx_def = Define `
 all_idx P xs =
  !i j. 0 <= i /\ i < LENGTH xs /\ 0 <= j /\ j < LENGTH xs /\ i <> j ==>
        let p = EL i xs;
            q = EL j xs in
         P p q`;

val valid_ps_for_module_def = Define `
 valid_ps_for_module vars p q <=>
  (!x. ((~MEM x vars /\ MEM x (vreads p)) ==> ~MEM x (vwrites q))) /\
  (!x. MEM x (vwrites p) ==> ~MEM x (vwrites q))`;

val valid_ps_for_module_tl = Q.store_thm("valid_ps_for_module_tl",
 `!vars p ps. all_idx (valid_ps_for_module vars) (p::ps) ==>
              all_idx (valid_ps_for_module vars) ps`,
 rw [all_idx_def, valid_ps_for_module_def] \\
 first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) \\
 simp []);

val valid_ps_for_module_tl2 = Q.store_thm("valid_ps_for_module_tl2",
 `!vars p1 p2 ps. all_idx (valid_ps_for_module vars) (p1::p2::ps) ==>
                  all_idx (valid_ps_for_module vars) (p1::ps)`,
 simp [all_idx_def, valid_ps_for_module_def] \\ rpt strip_tac' \\
 Cases_on `i`
  >- (Cases_on `j` \\ fs [] \\ first_x_assum (qspecl_then [`0`, `SUC (SUC n)`] mp_tac) \\ fs [])
  \\ (Cases_on `j` \\ fs []
      >- (first_x_assum (qspecl_then [`SUC (SUC n)`, `0`] mp_tac) \\ fs [])
      \\ (first_x_assum (qspecl_then [`SUC (SUC n)`, `SUC (SUC n')`] mp_tac) \\ fs [])));

val valid_ps_for_module_tl_vreads = Q.store_thm("valid_ps_for_module_tl_vreads",
 `!h ps p var vars.
   all_idx (valid_ps_for_module vars) (h::ps) /\ MEM p ps /\
   MEM var (vreads p) /\ ~MEM var vars ==> ~MEM var (vwrites h)`,
 rewrite_tac [all_idx_def, valid_ps_for_module_def] \\ rpt strip_tac' \\
 imp_res_tac MEM_EL \\
 last_x_assum (qspecl_then [`SUC n'`, `0`] mp_tac) \\ fs []);

val valid_ps_for_module_tl_vwrites = Q.store_thm("valid_ps_for_module_tl_vwrites",
 `!h ps p var vars.
   all_idx (valid_ps_for_module vars) (h::ps) /\ MEM p ps /\
   MEM var (vwrites p) ==> ~MEM var (vwrites h)`,
 rewrite_tac [all_idx_def, valid_ps_for_module_def] \\ rpt strip_tac' \\
 imp_res_tac MEM_EL \\
 last_x_assum (qspecl_then [`SUC n'`, `0`] mp_tac) \\ fs []);

val relM_relS = Q.store_thm("relM_relS",
 `!s env. relM s env ==> relS s <| vars := env; nbq := [] |>`,
 rw [relM_def, relS_def, relM_var_def, sum_alookup_def, relS_var_def, get_var_def] \\ fs []);

(*
val no_writes_before_read_exp_def = Define `
 no_writes_before_read_exp var written exp = (~written \/ ~MEM var (evreads exp))`;

val no_writes_before_read_lhs = Define `
 (no_writes_before_read_lhs var (Var name) = (name = var)) /\
 (no_writes_before_read_lhs var (ArrayIndex (Var name) _) = (name = var)) /\
 (no_writes_before_read_lhs var (ArraySlice (Var name) _ _ _) = (name = var)) /\
 (no_writes_before_read_lhs var _ = F)`;

(* The only case we care about here is when ret is T *)
val no_writes_before_read_def = tDefine "no_writes_before_read" `
 (no_writes_before_read var written Skip = (T, written)) /\
 (no_writes_before_read var written (Seq p1 p2) =
  let (ret, written') = no_writes_before_read var written p1;
      (ret', written'') = no_writes_before_read var written' p2 in
       (ret /\ ret', written'')) /\
 (no_writes_before_read var written (IfElse c pt pf) =
  let ret = no_writes_before_read_exp var written c;
      (ret', written') = no_writes_before_read var written pt;
      (ret'', written'') = no_writes_before_read var written pf in
       (ret /\ ret' /\ ret'', written' \/ written'')) /\
 (no_writes_before_read var written (Case m cs d) =
  let mret = no_writes_before_read_exp var written m;
      (ret', written') =
       FOLDR (λ(cc, cb) (ret, written').
        let ccret = no_writes_before_read_exp var written cc;
            (ret', written'') = no_writes_before_read var written cb in
           (ccret /\ ret', written' \/ written'')) (T, written) cs;
      (ret'', written'') =
       (case d of SOME d' => no_writes_before_read var written d'
                | NONE => (T, F)) in
    (mret /\ ret' /\ ret'', written' \/ written'')) /\
 (no_writes_before_read var written (BlockingAssign lhs rhs) =
  (no_writes_before_read_exp var written rhs,
   written \/ no_writes_before_read_lhs var lhs)) /\
 (no_writes_before_read var written (NonBlockingAssign lhs rhs) =
  (no_writes_before_read_exp var written rhs, written))`

 (WF_REL_TAC `measure (vprog_size o (\(a,b,c). c))` \\ rw [] \\
 imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

(*
(* No reads after writes to communication variables *)
val cvar_writes_cond_def = Define `
 cvar_writes_cond vars p = EVERY (\var. FST (no_writes_before_read var F p)) vars`;
*)
*)

(* No reads after writes to communication variables, inefficient version *)
val cvar_writes_cond_def = tDefine "cvar_writes_cond" `
 (cvar_writes_cond vars (Seq p q) =
  (EVERY (\var. MEM var (vwrites p) ==> ~MEM var (vreads q)) vars /\
  cvar_writes_cond vars p /\ cvar_writes_cond vars q)) /\
 (cvar_writes_cond vars (IfElse _ p q) = (cvar_writes_cond vars p /\ cvar_writes_cond vars q)) /\
 (cvar_writes_cond vars (Case _ _ cs d) = (EVERY (\(_, p). cvar_writes_cond vars p) cs /\
                                           case d of SOME dp => cvar_writes_cond vars dp | NONE => T)) /\
 (cvar_writes_cond _ _ = T)`

 (WF_REL_TAC `measure (vprog_size o SND)` \\ rw [] \\
  imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

(* No writes after writes to communication variables *)
val cvar_writes_cond2_def = tDefine "cvar_writes_cond2" `
 (cvar_writes_cond2 vars (Seq p q) =
  (EVERY (\var. ~(MEM var (vwrites p) /\ MEM var (vwrites q))) vars /\
  cvar_writes_cond2 vars p /\ cvar_writes_cond2 vars q)) /\
 (cvar_writes_cond2 vars (IfElse _ p q) = (cvar_writes_cond2 vars p /\ cvar_writes_cond2 vars q)) /\
 (cvar_writes_cond2 vars (Case _ _ cs d) = (EVERY (\(_, p). cvar_writes_cond2 vars p) cs /\
                                            case d of SOME dp => cvar_writes_cond2 vars dp | NONE => T)) /\
 (cvar_writes_cond2 _ _ = T)`

 (WF_REL_TAC `measure (vprog_size o SND)` \\ rw [] \\
  imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

val Abbrev_SYM = Q.store_thm("Abbrev_SYM",
 `!x y. Abbrev (x = y) <=> Abbrev (y = x)`,
 metis_tac [markerTheory.Abbrev_def]);

(* TODO: Very slow and a little outdated w.r.t. semantics
val prun_untainted_state = Q.store_thm("prun_untainted_state",
 `!vars fext ver_s p ver_s' ver_s''.
  prun fext ver_s p = INR ver_s' /\

  (* Conditions on what programs can be lifted *)
  vnwrites p = [] /\
  cvar_writes_cond vars p /\
  (*(!var. MEM var vars /\ MEM var (vreads p) ==> ~MEM var (vwrites p)) /\*)
  cvar_writes_cond2 vars p /\

  (* Conditions on the environment *)
  (!var. MEM var (vreads p) \/ MEM var (vwrites p) ==>
         get_var ver_s'' var = get_var ver_s var) /\
  (!var. MEM var vars /\ MEM var (vwrites p) ==>
         (get_nbq_var ver_s'' var = get_var ver_s var \/
         get_nbq_var ver_s'' var = get_nbq_var ver_s var))
  ==>
  ?ver_s'''. prun fext ver_s'' (intro_cvars vars p) = INR ver_s''' /\
             (!var. ~MEM var vars /\ MEM var (vwrites p) ==>
                    get_var ver_s''' var = get_var ver_s' var) /\
             (!var. MEM var vars /\ MEM var (vwrites p) ==>
                    get_nbq_var ver_s''' var = get_var ver_s' var \/
                    (get_nbq_var ver_s''' var = get_nbq_var ver_s'' var) /\
                     get_var ver_s''' var = get_var ver_s' var /\
                     get_var ver_s' var = get_var ver_s var)`,
 gen_tac \\ recInduct prun_ind \\ rpt strip_tac
 >- (* Skip *)
 fs [intro_cvars_def, prun_def, vwrites_def, vreads_def]
 >- (* Seq *)
 (fs [intro_cvars_def, prun_Seq, vwrites_def, vnwrites_def, vreads_def, cvar_writes_cond_def, cvar_writes_cond2_def, EVERY_MEM] \\
 first_x_assum drule \\ disch_then (qspec_then `ver_s''` mp_tac) \\
 impl_tac >- (simp [] \\ metis_tac []) \\ strip_tac \\ simp [] \\
 first_x_assum drule \\ disch_then (qspec_then `ver_s'''` mp_tac) \\
 impl_tac \\ (* TOOD: inefficient but works: *)
 rpt strip_tac \\ `~MEM var (vnwrites p0)` by fs [] \\ `~MEM var (vnwrites p1)` by fs [] \\
 simp [] \\ metis_tac [prun_intro_cvars_same_after, prun_intro_cvars_same_after2, prun_same_after])

 >- (* IfElse *)
 (fs [intro_cvars_def, prun_IfElse, vwrites_def, vnwrites_def, vreads_def, cvar_writes_cond_def, cvar_writes_cond2_def, EVERY_MEM] \\
 first_x_assum drule \\ disch_then (qspec_then `ver_s''` mp_tac) \\
 (impl_tac >- (simp [] \\ metis_tac [])) \\ strip_tac \\ qexists_tac `ver_s'''` \\ simp [] \\
 (conj_tac >- metis_tac [erun_cong]) \\
 (* TODO: metis takes forever here *)
 conj_tac \\ gen_tac \\ metis_tac [prun_intro_cvars_same_after, prun_intro_cvars_same_after2, prun_same_after])

 >- (* Case *)
 (fs [intro_cvars_def, prun_Case, vwrites_def, vnwrites_def, vreads_def, cvar_writes_cond_def, cvar_writes_cond2_def, EVERY_MEM] \\
 last_x_assum drule \\ last_x_assum kall_tac \\
 TRY (disch_then drule) \\ disch_then (qspec_then `ver_s''` mp_tac) \\
 rpt (impl_tac >- (simp [] \\ metis_tac [])) \\
 strip_tac \\ simp [] \\
 `erun fext ver_s'' e = erun fext s e` by metis_tac [erun_cong] \\
 `erun fext ver_s'' ccond = erun fext s ccond` by metis_tac [erun_cong] \\ simp []
 >-
 (rveq \\ TRY strip_tac \\ metis_tac [prun_intro_cvars_same_after, prun_intro_cvars_same_after2, prun_same_after])
 >-
 (* UGLY, TODO, OMG: *)
 (qspecl_then [`fext`, `ver_s''`, `vars`, `Case e cs default`] mp_tac prun_intro_cvars_same_after \\
 simp [intro_cvars_def, vnwrites_def, vwrites_def] \\ strip_tac \\

 qpat_x_assum `prun _ s _ = _` assume_tac \\
 drule prun_same_after \\ strip_tac \\

 strip_tac \\ gen_tac \\ Cases_on `MEM var (vwrites (Case e cs default))` \\
 fs [vwrites_def] \\ metis_tac [])
 \\
 fs [intro_cvars_def, vnwrites_def, vwrites_def, vreads_def, prun_def,
     cvar_writes_cond_def, cvar_writes_cond2_def] \\
 first_x_assum match_mp_tac \\
 metis_tac [prun_intro_cvars_same_after, prun_intro_cvars_same_after2, prun_same_after])

 >- (* Case ii *)
 (fs [intro_cvars_def, prun_def, vwrites_def, vnwrites_def, vreads_def, cvar_writes_cond_def, cvar_writes_cond2_def, EVERY_MEM] \\
 last_x_assum (qspec_then `ver_s''` mp_tac) \\ impl_tac >- (simp [] \\ metis_tac []) \\
 strip_tac \\ asm_exists_tac \\ simp [] \\
 metis_tac [prun_intro_cvars_same_after, prun_intro_cvars_same_after2, prun_same_after])

 >- (* Case iii *)
 fs [intro_cvars_def, prun_def, vwrites_def, vnwrites_def, vreads_def]

 >- (* BlockingAssign *)
 (fs [intro_cvars_def, prun_def, vwrites_def, vnwrites_def, vreads_def] \\
 imp_res_tac sum_bind_INR_old \\ fs [sum_bind_def, prun_bassn_def] \\
 imp_res_tac sum_for_INR_old \\ fs [sum_for_def, sum_map_def] \\

 (* TODO: Can probably be done in better order: *)
 `erun fext ver_s'' rhs = erun fext s rhs` by metis_tac [erun_cong] \\
 qabbrev_tac `lhs_ = lhs` \\
 drule assn_INR \\ strip_tac \\ rveq \\ fs [Abbrev_SYM] \\

 `(!var. MEM var (evreads lhs) ==> get_var ver_s'' var = get_var s var)`
 by (unabbrev_all_tac \\ fs [evwrites_def, evreads_def, evreads_index_def] \\ metis_tac []) \\

 `assn fext ver_s'' lhs v' = assn fext s lhs v'` by metis_tac [assn_cong] \\

 unabbrev_all_tac \\

 simp [get_assn_var_def] \\ Cases_on `MEM name vars` \\
 simp [prun_def, sum_bind_def, sum_for_def, sum_map_def, prun_bassn_def, prun_nbassn_def] \\
 fs [evreads_def, evwrites_def, get_var_cleanup])

 \\ (* NonBlockingAssign *)
 fs [prun_def] \\ imp_res_tac sum_bind_INR_old \\ fs [sum_bind_def, prun_nbassn_def] \\
 imp_res_tac sum_for_INR_old \\ fs [sum_for_def, sum_map_def] \\ rveq \\
 drule assn_INR \\ strip_tac \\ rveq \\
 fs [vnwrites_def, evwrites_def]);

val relS_with_same_vars = Q.store_thm("relS_with_same_vars",
 `!s ver_s. relS s ver_s ==> relS s (ver_s with vars := ver_s.vars)`,
 rw [relS_def, relS_var_def, get_var_def]);

val pstate_vars_cleanup = Q.store_thm("pstate_vars_cleanup",
 `!(ver_s:pstate). ver_s with vars := ver_s.vars = ver_s`,
 rw [pstate_component_equality]);
*)
val mstep_no_writes = Q.store_thm("mstep_no_writes",
 `!ps fext var vars ver_s ver_s'.
  EVERY (\p. ~MEM var (vwrites p)) ps /\
  EVERY (\p. vnwrites p = []) ps /\
  mstep fext (MAP (intro_cvars vars) ps) ver_s = INR ver_s' ==>
  get_var ver_s' var = get_var ver_s var /\
  get_nbq_var ver_s' var = get_nbq_var ver_s var`,
 Induct >- rw [mstep_def, sum_foldM_def] \\
 rpt gen_tac \\ strip_tac \\ fs [mstep_step] \\
 metis_tac [prun_intro_cvars_same_after]);
(*
val mstep_untainted_state = Q.store_thm("mstep_untainted_state",
 `!vars fext ps fextv ver_s ver_s' s Penv.
  Penv ver_s.vars /\
  (* Conditions on what programs can be lifted *)
  (!p. MEM p ps ==> (?s'. !env. Penv env ==> EvalS fext s env s' p) /\
                    vnwrites p = [] /\
                    cvar_writes_cond vars p /\
                    cvar_writes_cond2 vars p) /\
  ALL_DISTINCT ps /\ (* <-- TODO: No longer needed *)

  (* Conditions on the environment *)
  relS s ver_s /\
  relS_fextv fextv fext /\
  all_idx (valid_ps_for_module vars) ps /\

  (!p. MEM p ps ==>
  (!var. MEM var (vreads p) \/ MEM var (vwrites p) ==>
         get_var ver_s' var = get_var ver_s var) /\
  (!var. MEM var (vwrites p) ==>
         get_nbq_var ver_s' var = get_nbq_var ver_s var))
  ==>
  ?ver_s''. mstep fextv (MAP (intro_cvars vars) ps) ver_s' = INR ver_s'' /\
            (!p. MEM p ps ==>
             (?ver_s_p. prun fextv ver_s p = INR ver_s_p /\
             (!var. MEM var (vwrites p) ==>
              if MEM var vars
              then get_nbq_var ver_s'' var = get_var ver_s_p var \/
                   (get_nbq_var ver_s'' var = get_nbq_var ver_s' var /\
                   get_var ver_s'' var = get_var ver_s_p var)
              else get_var ver_s'' var = get_var ver_s_p var /\
                   get_nbq_var ver_s'' var = get_nbq_var ver_s' var)))`,
 ntac 2 gen_tac \\ Induct >- rw [mstep_def, sum_foldM_def] \\
 simp [mstep_step] \\ Ho_Rewrite.ONCE_REWRITE_TAC [MEM_disj_impl] \\ rpt strip_tac \\ fs [] \\
 CONV_TAC (DEPTH_CONV LEFT_AND_EXISTS_CONV) \\

 first_x_assum drule \\ simp [EvalS_def] \\ imp_res_tac relS_with_same_vars \\
 rpt (disch_then drule) \\ simp [pstate_vars_cleanup] \\ strip_tac \\

 drule prun_untainted_state \\ rpt (disch_then drule) \\ simp [] \\ strip_tac \\
 asm_exists_tac \\ simp [] \\

 first_x_assum drule \\ disch_then (qspecl_then [`fextv`, `ver_s'''`, `s`] mp_tac) \\
 impl_tac >- (simp [] \\ metis_tac [valid_ps_for_module_tl, valid_ps_for_module_tl_vreads,
                                    valid_ps_for_module_tl_vwrites, prun_intro_cvars_same_after,
                                    prun_intro_cvars_same_after2]) \\ strip_tac \\
 asm_exists_tac \\ simp [] \\

 `EVERY (\p. vnwrites p = []) ps` by (simp [EVERY_MEM]) \\
 rpt strip_tac
 >- (`EVERY (\p. ~MEM var (vwrites p)) ps` by
     (simp [EVERY_MEM] \\ metis_tac [valid_ps_for_module_tl_vwrites]) \\
    metis_tac [prun_intro_cvars_same_after3, mstep_no_writes])

 \\ metis_tac [valid_ps_for_module_tl_vwrites, prun_intro_cvars_same_after]);

val mget_var_append = Q.store_thm("mget_var_append",
 `!var xs ys.
   mget_var (xs ⧺ ys) var = case mget_var xs var of INL _ => mget_var ys var | INR v => INR v`,
 rw [mget_var_def, alistTheory.ALOOKUP_APPEND] \\ EVERY_CASE_TAC \\ simp []);

val mget_var_get_nbq_var = Q.store_thm("mget_var_get_nbq_var",
 `!s var. mget_var s.nbq var = get_nbq_var s var`,
 simp [mget_var_def, get_nbq_var_def]);

val mget_var_get_var = Q.store_thm("mget_var_get_var",
 `!s var. mget_var s.vars var = get_var s var`,
 simp [mget_var_def, get_var_def]);

(* Variant of prun_intro_cvars_same_after2 *)
val mrun_intro_cvars_same_after2 = Q.store_thm("mrun_intro_cvars_same_after2",
 `!ps fext ver_s ver_s' var vars.
   mstep fext (MAP (intro_cvars vars) ps) ver_s = INR ver_s' /\ MEM var vars ==>
   get_var ver_s' var = get_var ver_s var`,
 Induct >- rw [mstep_def, sum_foldM_def] \\
 rw [mstep_step] \\ metis_tac [prun_intro_cvars_same_after2]);

(* mstep_untainted_state is very general because otherwise the induction does not work,
   this thm is a simpler version that is what we actually need in practice *)
val mstep_commit_lift_EvalSs = Q.store_thm("mstep_commit_lift_EvalSs",
 `!vars fext ps fextv vs s Penv.
  Penv vs /\ (* <-- always "Penv = vars_has_type ver_s.vars ty" *)
  (* Conditions on what programs can be lifted *)
  (!p. MEM p ps ==> (!s. ?s'. !env. Penv env ==> EvalS fext s env s' p) /\
                    vnwrites p = [] /\
                    cvar_writes_cond vars p /\
                    cvar_writes_cond2 vars p) /\
  ALL_DISTINCT ps /\ (* <-- TODO: No longer needed *)

  (* Conditions on the environment *)
  relM s vs /\
  relS_fextv fextv fext /\
  all_idx (valid_ps_for_module vars) ps
  ==>
  ?vs'. mstep_commit fextv (MAP (intro_cvars vars) ps) vs = INR vs' /\
        (!p. MEM p ps ==>
             (?ver_s_p. prun fextv <| vars := vs; nbq := [] |> p = INR ver_s_p /\ (* relS hp ver_s' ... *)
                        (!var. MEM var (vwrites p) ==> mget_var vs' var = get_var ver_s_p var)))`,
 rpt strip_tac \\
 qspecl_then [`vars`, `fext`, `ps`, `fextv`,
              `<| vars := vs; nbq := [] |>`, `<| vars := vs; nbq := [] |>`,
              `s`, `Penv`] mp_tac mstep_untainted_state \\
 impl_tac >- simp [relM_relS] \\ strip_tac \\
 simp [mstep_commit_def, sum_map_def] \\ rpt strip_tac \\ drule_last \\ drule_first \\
 fs [EvalS_def] \\ first_x_assum (qspec_then `s` strip_assume_tac) \\ drule_strip relM_relS \\
 drule_first \\ rpt strip_tac \\
 drule_first \\ simp [mget_var_append, mget_var_get_var, mget_var_get_nbq_var] \\
 pop_assum mp_tac \\ EVERY_CASE_TAC \\ fs [get_nbq_var_def] \\
 drule_strip mrun_intro_cvars_same_after2 \\ drule_strip prun_get_var_INL \\ metis_tac []);
*)
(* From mstep_commit to mrun *)

(* Work because step does not depend on fbits *)
val mstep_commit_mrun = Q.store_thm("mstep_commit_mrun",
 `!n vs ps fextv fbits step (*tys*).
   relM (step 0) vs /\
   (*vars_has_type vs tys /\*)
   (!n vs fbits fbits'.
     relM (step n) vs (*/\ vars_has_type vs tys*) ==>
     ?vs' fbits'. mstep_commit (fextv n) fbits ps vs = INR (vs', fbits') /\ relM (step (SUC n)) vs')
   ==>
   ?vs' fbits'. mrun fextv fbits ps vs n = INR (vs', fbits') /\ relM (step n) vs'`,
 Induct >- rw [mrun_def] \\ rpt strip_tac \\ drule_last \\
 (*drule_strip vars_has_type_mrun \\*) simp [mrun_step] \\ metis_tac []);

(* Useful for variables never written to *)
val mstep_intro_cvars_no_writes = Q.store_thm("mstep_intro_cvars_no_writes",
 `!fext ps var vars ver_s ver_s'.
  mstep fext (MAP (intro_cvars vars) ps) ver_s = INR ver_s' /\
  EVERY (\p. ~MEM var (vwrites p)) ps /\
  EVERY (\p. vnwrites p = []) ps /\
  get_nbq_var ver_s var = INL UnknownVariable ==>
  sum_alookup (ver_s'.nbq ++ ver_s'.vars) var = get_var ver_s var`,
 rw [sum_alookup_def, alistTheory.ALOOKUP_APPEND] \\ drule mstep_no_writes \\
 rpt (disch_then drule) \\ EVERY_CASE_TAC \\ fs [get_var_def, get_nbq_var_def]);

val mstep_commit_intro_cvars_no_writes = Q.store_thm("mstep_commit_intro_cvars_no_writes",
 `!fext fbits fbits' ps var vars vs vs'.
  mstep_commit fext fbits (MAP (intro_cvars vars) ps) vs = INR (vs', fbits') /\
  EVERY (\p. ~MEM var (vwrites p)) ps /\
  EVERY (\p. vnwrites p = []) ps ==>
  sum_alookup vs' var = sum_alookup vs var`,
 rw [mstep_commit_def] \\ drule_strip sum_map_INR_old \\ drule_strip mstep_intro_cvars_no_writes \\
 fs [get_nbq_var_def, sum_map_def, get_var_def, sum_alookup_def]);

(** For computing valid_ps_for_module **)

val all_idx_order_def = Define `
 all_idx_order P ps =
  !i j. 0 <= i /\ i < LENGTH ps /\ 0 <= j /\ j < LENGTH ps /\ i < j ==>
        let p = EL i ps;
            q = EL j ps in
         P p q /\ P q p`;

val all_idx_all_idx_order = Q.store_thm("all_idx_all_idx_order",
 `!xs P. all_idx P xs <=> all_idx_order P xs`,
 rpt gen_tac \\ eq_tac \\ rw [all_idx_def, all_idx_order_def] \\
 Cases_on `i < j` \\ fs []);

val comp_idx_iter_help_def = Define `
 (comp_idx_iter_help P x [] = T) /\
 (comp_idx_iter_help P x (y::ys) <=> P x y /\ P y x /\
                                     comp_idx_iter_help P x ys)`;

val comp_idx_iter_def = Define `
 (comp_idx_iter P [] = T) /\
 (comp_idx_iter P (x::xs) <=> comp_idx_iter_help P x xs /\ comp_idx_iter P xs)`;

val comp_idx_iter_tl = Q.store_thm("comp_idx_iter_tl",
 `!xs x P. comp_idx_iter P (x::xs) ==> comp_idx_iter P xs`,
 rw [comp_idx_iter_def]);

val comp_idx_iter_help_EL = Q.store_thm("comp_idx_iter_help_EL",
 `!xs x n P. comp_idx_iter_help P x xs /\ n < LENGTH xs ==> P x (EL n xs) /\ P (EL n xs) x`,
 Induct \\ rw [comp_idx_iter_help_def] \\
 Cases_on `n` \\ fs []);

val comp_idx_iter_all_idx = Q.store_thm("comp_idx_iter_all_idx",
 `!P xs. comp_idx_iter P xs ==> all_idx P xs`,
 rewrite_tac [all_idx_all_idx_order] \\
 gen_tac \\ Induct >- rw [all_idx_order_def] \\ rpt strip_tac \\
 last_x_assum mp_tac \\ impl_tac >- fs [comp_idx_iter_def] \\ disch_tac \\
 simp [all_idx_order_def] \\ rpt strip_tac' \\
 Cases_on `i`
 >- (Cases_on `j` \\ fs [comp_idx_iter_def, comp_idx_iter_help_EL])
 \\ Cases_on `j` \\ fs [all_idx_order_def]);

val _ = export_theory();
