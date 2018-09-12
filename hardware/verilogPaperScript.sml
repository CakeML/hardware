open hardwarePreamble;

open verilogTheory;

open sumExtraTheory;

val _ = new_theory "verilogPaper";

(* Simple theory providing Verilog definitions without monadic combinators *)

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

val _ = export_theory ();
