open hardwarePreamble;

open sumExtraTheory verilogTheory verilogTranslatorTheory moduleTranslatorTheory;

open pred_setTheory;

open dep_rewrite;

val _ = new_theory "verilogPaper";

(*
Simple theory providing Verilog definitions without monadic combinators,
so people not familiar with functional programming can follow the definitions.

The theory also replaces the (currently, two-field) record type used for intermediate state
with a pair, because a pair looks cleaner in the paper.
*)

val prun'_def = Define `
 prun' fext sp p = sum_map (\sp'. (sp'.vars, sp'.nbq))
                           (prun fext <| vars := FST sp; nbq := SND sp |> p)`;

val mstep'_def = Define `
 (mstep' fext [] s = INR s) /\
 (mstep' fext (p::ps) s =
  case prun' fext s p of
     INL e => INL e
   | INR s' => mstep' fext ps s')`;

val mstep_commit'_def = Define `
 mstep_commit' fext ps Γ =
  case mstep' fext ps (Γ, []) of
     INL e => INL e
   | INR (Γ', Δ') => INR (Δ' ⧺ Γ')`;

val mrun'_def = Define `
 (mrun' fext ps Γ 0 = INR Γ) /\
 (mrun' fext ps Γ (SUC n) = (case mrun' fext ps Γ n of
                               INL e => INL e
                             | INR Γ' => mstep_commit' (fext n) ps Γ'))`;

(* Eq proofs *)

val sum_bind_as_case = Q.store_thm("sum_bind_as_case",
 `!f x. sum_bind x f = case x of
                         INL v => INL v
                       | INR v => f v`,
 Cases_on `x` \\ rw [sum_bind_def]);

val sum_map_as_case = Q.store_thm("sum_map_as_case",
 `!f x. sum_map f x = case x of
                         INL v => INL v
                       | INR v => INR (f v)`,
 Cases_on `x` \\ rw [sum_map_def]);

val pair_record_rel_def = Define `
 pair_record_rel sp sr <=> sp = (sr.vars, sr.nbq)`;

val sum_pair_record_rel_def = Define `
 (sum_pair_record_rel (INL e1) (INL e2) <=> e1 = e2) /\
 (sum_pair_record_rel (INR s1) (INR s2) <=> pair_record_rel s1 s2) /\
 (sum_pair_record_rel _ _ = F)`;

val pstate_all = Q.prove(
 `!s. <|vars := s.vars; nbq := s.nbq|> = s`,
 rw [pstate_component_equality]);

val pair_record_prun = Q.store_thm("pair_record_prun",
 `!fext p sp sr.
   pair_record_rel sp sr ==>
   sum_pair_record_rel (prun' fext sp p) (prun fext sr p)`,
 rw [prun'_def, pair_record_rel_def, pstate_all, sum_map_as_case] \\
 CASE_TAC \\ simp [sum_pair_record_rel_def, pair_record_rel_def]);

val pair_record_mstep = Q.store_thm("pair_record_mstep",
 `!ps fext sp sr.
   pair_record_rel sp sr ==>
   sum_pair_record_rel (mstep' fext ps sp) (mstep fext ps sr)`,
 Induct >- rw [mstep'_def, mstep_def, sum_foldM_def, sum_pair_record_rel_def] \\
 rw [mstep'_def, mstep_def, sum_foldM_def, sum_bind_as_case] \\
 drule_strip pair_record_prun \\ pop_assum (qspecl_then [`fext`, `h`] assume_tac) \\
 every_case_tac \\ rfs [mstep_def, sum_pair_record_rel_def]);

val mstep_commit'_mstep_commit = Q.store_thm("mstep_commit'_mstep_commit",
 `!ps fext s.
   mstep_commit' fext ps s = mstep_commit fext ps s`,
 rw [mstep_commit'_def, mstep_commit_def] \\

 qspecl_then [`ps`, `fext`, `(s, [])`, `<| vars := s; nbq := [] |>`]
             mp_tac
             pair_record_mstep \\

 impl_tac >- simp [pair_record_rel_def] \\ strip_tac \\
 simp [sum_map_as_case] \\ every_case_tac \\
 fs [sum_pair_record_rel_def, pair_record_rel_def]);

val mrun'_mrun = Q.store_thm("mrun'_mrun",
 `!fext ps Γ n. mrun' fext ps Γ n = mrun fext ps Γ n`,
 Induct_on `n` \\
 rw [mrun'_def, mrun_def, mstep_commit'_mstep_commit, sum_bind_as_case]);

(* Cleaner EvalS variant *)

val relS'_def = Define `
 relS' s Γ <=> relS s <| vars := Γ |>`;

val relS_rw = Q.prove(
 `!s ver_s Γ. relS s (ver_s with vars := Γ) = relS s <| vars := Γ |> /\
              relS s <|vars := ver_s.vars|> = relS s ver_s`,
 rw [relS_def, relS_var_def, get_var_def]);

val pstate_rw = Q.prove(
 `!vars ver_s. <|vars := vars; nbq := ver_s.nbq|> = ver_s with vars := vars`,
 rw [pstate_component_equality]);

val EvalS'_def = Define `
 EvalS' fext s Γ hp vp <=>
  !fextv Δ.
   relS' s Γ /\ relS_fextv fextv fext ==>
    ?Γ' Δ'. prun' fextv (Γ, Δ) vp = INR (Γ', Δ') /\ relS' hp Γ'`;

val EvalS'_EvalS = Q.store_thm("EvalS'_EvalS",
 `!fext s Γ hp vp. EvalS' fext s Γ hp vp <=> EvalS fext s Γ hp vp`,
 rw [EvalS'_def, EvalS_def, relS'_def, relS_rw] \\ eq_tac \\ rpt strip_tac \\ drule_first
 >- (pop_assum (qspec_then `ver_s.nbq` strip_assume_tac) \\
    fs [prun'_def] \\ drule_strip sum_map_INR \\
    fs [sum_map_def] \\ rveq \\ fs [pstate_rw, relS_rw])
 \\ pop_assum (qspec_then `<| nbq := Δ |>` strip_assume_tac) \\
    simp [prun'_def, sum_map_def, relS_rw]);

(* Cleaner module translator things *)

val valid_program_pred_def = Define `
 valid_program_pred p q <=>
  (DISJOINT (set (vreads p)) (set (vwrites q))) /\
  (DISJOINT (set (vnwrites p) UNION set (vwrites p))
            (set (vwrites q) UNION set (vnwrites q)))`;

val valid_program_def = Define `
 valid_program ps = all_idx valid_program_pred ps`;

val valid_ps_for_module_set_def = Define `
 valid_ps_for_module_set vars p q <=>
  DISJOINT ((set (vreads p)) DIFF (set vars)) (set (vwrites q)) /\
  DISJOINT (set (vwrites p)) (set (vwrites q))`;

val valid_ps_for_module_set_valid_ps_for_module =
 Q.store_thm("valid_ps_for_module_set_valid_ps_for_module",
 `valid_ps_for_module_set = valid_ps_for_module`,
 rpt (match_mp_tac EQ_EXT \\ gen_tac) \\ eq_tac \\
 rw [valid_ps_for_module_set_def, valid_ps_for_module_def, DISJOINT_ALT]);

val vreads_intro_cvars = Q.store_thm("vreads_intro_cvars",
 `!p vars. vreads (intro_cvars vars p) = vreads p`,
 recInduct vreads_ind \\ rpt conj_tac \\ rw [intro_cvars_def, vreads_def]
 >- (every_case_tac \\ fs [] \\
    Induct_on `cs` \\ rw [] \\ pairarg_tac \\ fs [] \\ pairarg_tac \\ fs [] \\ metis_tac [])
 \\ every_case_tac \\ fs [vreads_def]);

val union_diff_comm = Q.store_thm("union_diff_comm",
 `!a b c. (a UNION b) DIFF c = (a DIFF c) UNION (b DIFF c)`,
 rw [DIFF_DEF] \\ match_mp_tac EQ_EXT \\ rw [] \\ metis_tac []);

val bin_op_lem = Q.prove(
 `!f a b c d. a = c /\ b = d ==> f a b = f c d`,
 rw []);

val vwrites_intro_cvars = Q.store_thm("vwrites_intro_cvars",
 `!p vars. set (vwrites (intro_cvars vars p)) = set (vwrites p) DIFF set vars`,
 recInduct vwrites_ind \\ rpt conj_tac \\ rw [intro_cvars_def, vwrites_def]
 >- (match_mp_tac EQ_EXT \\ rw [] \\ metis_tac [])
 >- (match_mp_tac EQ_EXT \\ rw [] \\ metis_tac [])
 >- (rewrite_tac [union_diff_comm] \\ match_mp_tac bin_op_lem \\ reverse conj_tac
     >- (every_case_tac \\ fs [])
     \\ Induct_on `cs` \\ fs [] \\ rw [] \\
        rewrite_tac [union_diff_comm] \\ match_mp_tac bin_op_lem \\ conj_tac
        >- (pairarg_tac \\ fs [] \\ pairarg_tac \\ fs [] \\ metis_tac [])
        \\ metis_tac [])
 \\ every_case_tac \\ fs [vwrites_def] \\ Cases_on `e` \\ TRY (Cases_on `e'`) \\
    fs [evwrites_def, get_assn_var_def]);

val vnwrites_intro_cvars = Q.store_thm("vnwrites_intro_cvars",
 `!p vars.
   set (vnwrites (intro_cvars vars p)) =
   set (vnwrites p) UNION (set (vwrites p) INTER set vars)`,
 recInduct vnwrites_ind \\ rpt conj_tac \\ rw [intro_cvars_def, vnwrites_def, vwrites_def]
 >- (match_mp_tac EQ_EXT \\ rw [] \\ metis_tac [])
 >- (match_mp_tac EQ_EXT \\ rw [] \\ metis_tac [])
 >- (Induct_on `cs` >- (rw [] \\ every_case_tac \\ fs []) \\
    rw [] \\ PairCases_on `h` \\ fs [] \\
    qpat_x_assum `_ ==> _` mp_tac \\ impl_tac >- metis_tac [] \\
    strip_tac \\ simp [] \\
    pop_assum (fn th => simp [GSYM UNION_ASSOC, th]) \\
    every_case_tac \\ fs [] \\ match_mp_tac EQ_EXT \\ rw [] \\ metis_tac [])
 \\ every_case_tac \\ fs [vnwrites_def] \\ match_mp_tac EQ_EXT \\ rw [] \\
    Cases_on `v0` \\ TRY (Cases_on `e`) \\ fs [get_assn_var_def, evwrites_def] \\
    metis_tac []);

(* eq in one direction *)

val valid_program_pred_valid_ps_for_module_set =
 Q.store_thm("valid_program_pred_valid_ps_for_module_set",
 `!vars p q.
   valid_program_pred (intro_cvars vars p) (intro_cvars vars q) ==>
   valid_ps_for_module_set vars p q`,
 rewrite_tac [valid_program_pred_def, valid_ps_for_module_set_def] \\
 rpt strip_tac' \\ fs [vreads_intro_cvars, vwrites_intro_cvars, vnwrites_intro_cvars] \\
 fs [DISJOINT_ALT] \\ rw [] \\ metis_tac []);

val EL_MAP_CONS = Q.prove(
 `!n x xs. n < LENGTH (x::xs) ==> !f. EL n (f x :: MAP f xs) = f (EL n (x::xs))`,
 rpt strip_tac \\ rewrite_tac [GSYM MAP] \\ fs [EL_MAP]);

val valid_program_ok = Q.store_thm("valid_program_ok",
 `!ps vars.
   valid_program (MAP (intro_cvars vars) ps) ==>
   all_idx (valid_ps_for_module vars) ps`,
 rewrite_tac [GSYM valid_ps_for_module_set_valid_ps_for_module] \\
 Induct \\ rw [valid_program_def, all_idx_def] \\ rw [] \\
 first_x_assum (qspecl_then [`i`, `j`] mp_tac) \\ (impl_tac >- simp []) \\
 fs [EL_MAP_CONS, valid_program_pred_valid_ps_for_module_set]);

(* eq in other direction, need to assume no non-blocking writes (as in actual development) *)

val valid_ps_for_module_set_valid_program_pred =
 Q.store_thm("valid_ps_for_module_set_valid_program_pred",
 `!vars p q.
   valid_ps_for_module_set vars p q /\ vnwrites p = [] /\ vnwrites q = [] ==>
   valid_program_pred (intro_cvars vars p) (intro_cvars vars q)`,
 rewrite_tac [valid_program_pred_def, valid_ps_for_module_set_def] \\
 rpt strip_tac' \\ fs [vreads_intro_cvars, vwrites_intro_cvars, vnwrites_intro_cvars] \\
 fs [DISJOINT_ALT] \\ rw [] \\ metis_tac []);

val valid_program_ok_rev = Q.store_thm("valid_program_ok_rev",
 `!ps vars.
   EVERY (\p. vnwrites p = []) ps /\
   all_idx (valid_ps_for_module vars) ps ==>
   valid_program (MAP (intro_cvars vars) ps)`,
 rewrite_tac [GSYM valid_ps_for_module_set_valid_ps_for_module] \\
 Induct \\ rw [valid_program_def, all_idx_def] \\ rw [] \\
 first_x_assum (qspecl_then [`i`, `j`] mp_tac) \\ (impl_tac >- simp []) \\ strip_tac \\
 simp [EL_MAP_CONS] \\ match_mp_tac valid_ps_for_module_set_valid_program_pred \\
 simp [] \\ fs [EVERY_EL] \\ Cases_on `i` \\ Cases_on `j` \\ fs []);

(* For printing *)
val valid_program_print = save_thm("valid_program_print",
 valid_program_def |> REWRITE_RULE [all_idx_def, valid_program_pred_def]);

val _ = export_theory ();
