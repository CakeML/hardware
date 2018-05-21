open preamble;

open verilogTheory;

val _ = new_theory "verilogPaper";

(* The same as mrun, but with a pair instead of a record *)

(* Printed as sum_map in the paper *)
val sum_map_alt_def = Define `
 sum_map_alt f x = sum_bind x (INR o f)`;

val sum_map_alt_alt = Q.prove(
 `sum_map_alt = sum_map`,
 rpt (match_mp_tac EQ_EXT \\ gen_tac) \\ Cases_on `x'` \\
 simp [sum_map_alt_def, sum_bind_def, sum_map_def]);

val step_def = Define `
 step s p = sum_map_alt (\(_, s). (s.vars, s.nbq)) (prun <| vars := (FST s); nbq := (SND s) |> p)`;

val run_ps_def = Define `
 run_ps ps Γ = sum_foldM step (Γ, []) ps`;

(* Just "UNCURRY $++", but that syntax might be difficult to read for non-HOL4 users *)
val run_commit_def = Define `
 run_commit (Γ, Δ) = Δ ++ Γ`;

val run_cycle_def = Define `
 run_cycle ps Γ = sum_map_alt run_commit (run_ps ps Γ)`;

val run_def = Define `
 run ps Γ n = sum_funpowM (run_cycle ps) n Γ`;

(* Should maybe be moved to some general file *)
val sum_lift_eq_def = Define `
 (sum_lift_eq eq (INR x) (INR y) = eq x y) /\
 (sum_lift_eq eq (INL x) (INL y) = (x = y)) /\
 (sum_lift_eq eq _ _ = F)`;

val pair_eq_def = Define `
 pair_eq (Γ, ∆) s = ((s.vars = Γ) /\ (s.nbq = ∆))`;

val pair_eq2_def = Define `
 pair_eq2 ps Γ s = ((s.ps = ps) /\ (s.vars = Γ))`;

(* Cong thms for above eqs *)

val sum_lift_eq_eq_cong = Q.store_thm("sum_lift_eq_eq_cong",
 `!x y. x = y ==> sum_lift_eq $= x y`,
 rpt strip_tac \\ Cases_on `x` \\ Cases_on `y` \\ fs [sum_lift_eq_def]);

val sum_foldM_cong = Q.store_thm("sum_foldM_cong",
`!eq f g x y xs.
  (!z x y. eq x y ==> sum_lift_eq eq (f x z) (g y z)) /\ eq x y ==>
  sum_lift_eq eq (sum_foldM f x xs) (sum_foldM g y xs)`,
 Induct_on `xs` \\ rw [sum_foldM_def, sum_lift_eq_def] \\
 first_assum (qspecl_then [`h`, `x`, `y`] mp_tac) \\ disch_then drule \\ strip_tac \\
 Cases_on `f x h` \\ Cases_on `g y h` \\ fs [sum_lift_eq_def, sum_bind_def]);

val sum_map_cong = Q.store_thm("sum_map_cong",
 `!eq eq' f g x y.
   (!y x. eq x y ==> eq' (f x) (g y)) /\ sum_lift_eq eq x y ==>
   sum_lift_eq eq' (sum_map f x) (sum_map g y)`,
 rpt gen_tac \\ Cases_on `x` \\ Cases_on `y` \\ simp [sum_lift_eq_def, sum_map_def]);

(*val sum_bind_cong = Q.store_thm("sum_bind_cong",
  `!eq f g x y.
   (!y x. eq x y ==> sum_lift_eq eq (f x) (g y)) /\ sum_lift_eq eq x y ==>
   sum_lift_eq eq (sum_bind x f) (sum_bind y g)`,
 rpt gen_tac \\ Cases_on `x` \\ Cases_on `y` \\ simp [sum_lift_eq_def, sum_bind_def]);*)

val sum_funpowM_cong = Q.store_thm("sum_funpowM_cong",
 `!eq f g n x y.
   (!x y. eq x y ==> sum_lift_eq eq (f x) (g y)) /\
   eq x y ==> sum_lift_eq eq (sum_funpowM f n x) (sum_funpowM g n y)`,
 ntac 3 gen_tac \\ Induct >- rw [sum_funpowM_def, sum_lift_eq_def] \\
 rpt strip_tac \\ simp [sum_funpowM_def] \\ first_assum drule \\
 Cases_on `f x` \\ Cases_on `g y` \\ simp [sum_bind_def, sum_lift_eq_def]);

val sum_lift_eq_run_mrun = Q.store_thm("sum_lift_eq_run_mrun",
 `!n s. sum_lift_eq (pair_eq2 s.ps) (run s.ps s.vars n) (mrun s n)`,
 simp [run_def, mrun_def] \\ rpt gen_tac \\
 match_mp_tac sum_funpowM_cong \\ rw [pair_eq2_def, run_cycle_def, mstep_commit_def, sum_map_alt_alt] \\
 match_mp_tac sum_map_cong \\ qexists_tac `pair_eq` \\ conj_tac
 >- (rpt gen_tac \\ PairCases_on `x` \\ simp [pair_eq_def, pair_eq2_def, nbq_commit_def, run_commit_def]) \\
 simp [run_ps_def, mstep_def] \\
 match_mp_tac sum_foldM_cong \\ rw [pair_eq_def, step_def, sum_map_alt_alt] \\
 match_mp_tac sum_map_cong \\ qexists_tac `($=)` \\
 conj_tac
 >- (rw [] \\ PairCases_on `x'` \\ simp [pair_eq_def])
 \\ match_mp_tac sum_lift_eq_eq_cong \\ PairCases_on `x` \\ fs [pair_eq_def] \\ BINOP_TAC \\ simp [pstate_component_equality]);

(* Clean variant, without pair_eq defs *)
val run_mrun = Q.store_thm("run_mrun",
 `!ps Γ n.
   run ps Γ n = (sum_map (\m'. m'.vars) (mrun <| vars := Γ; ps := ps |> n))`,
 rpt strip_tac \\
 qspecl_then [`n`, `<| vars := Γ; ps := ps |>`] assume_tac sum_lift_eq_run_mrun \\
 Cases_on `run ps Γ n` \\ Cases_on `mrun <|vars := Γ; ps := ps|> n` \\
 fs [sum_lift_eq_def, pair_eq2_def, sum_map_def]);

val _ = export_theory ();
