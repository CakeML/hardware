open hardwarePreamble;

val _ = new_theory "circuitExample";

prefer_num ();

val _ = Datatype `state = <| count : word8; done : bool |>`;
val _ = Datatype `ext_state = <| pulse : bool |>`;

val A_def = Define `
 A (fext:ext_state) (s:state) =
  if fext.pulse then
   s with count := s.count + 1w
  else
   s`;

val B_def = Define `
 B (s:state) =
  if 10w <+ s.count then
   s with done := T
  else
   s`;

val AB_def = Define `
 (AB fext init 0 = init) /\
 (AB fext init (SUC n) =
  let s' = AB fext init n in <| count := (A (fext n) s').count; done := (B s').done |>)`;

val pulse_spec_def = Define `
 pulse_spec fext = !n. ?m. (fext (n + m)).pulse`;

val pulse_later = Q.store_thm("pulse_later",
 `!f t1 t2.
   (!t3. t3 < t2 ==> ~(f (t1 + t3)).pulse) \/
   (?t3. t3 < t2 /\ (!t4. t4 < t3 ==> ~(f (t1 + t4)).pulse) /\ (f (t1 + t3)).pulse)`,
 rpt gen_tac \\ Induct_on `t2` >- simp [] \\ pop_assum strip_assume_tac
 >- (Cases_on `(f (t1 + t2)).pulse`
  >- (disj2_tac \\ qexists_tac `t2` \\ simp [])
  \\ (disj1_tac \\ gen_tac \\ Cases_on `t3 = t2` \\ simp []))
 \\ disj2_tac \\ qexists_tac `t3` \\ simp []);

val pulse_spec_alt = Q.store_thm("pulse_spec_alt",
 `!fext. pulse_spec fext =
   !t1. ?t2. (!t3. t3 < t2 ==> ~(fext (t1 + t3)).pulse) /\ (fext (t1 + t2)).pulse`,
 metis_tac [pulse_spec_def, pulse_later]);

val AB_step_count_wait = Q.store_thm("AB_step_count_wait",
 `!n m fext init.
   (∀t3. t3 < m ⇒ ¬(fext (n + t3)).pulse) ==>
   (AB fext init (n + m)).count = (AB fext init n).count`,
 rpt strip_tac \\ Induct_on `m` \\ rpt strip_tac >- simp [] \\
 rewrite_tac [GSYM arithmeticTheory.ADD_SUC] \\
 fs [AB_def, A_def]);

val AB_step_count_1 = Q.store_thm("AB_step_count_1",
 `!n init fext.
   pulse_spec fext ==>
   ?m. (AB fext init (n + m)).count = (AB fext init n).count + 1w`,
 rewrite_tac [pulse_spec_alt] \\ rpt strip_tac \\ pop_assum (qspec_then `n` strip_assume_tac) \\
 drule_strip AB_step_count_wait \\ qexists_tac `SUC t2` \\
 rewrite_tac [GSYM arithmeticTheory.ADD_SUC] \\ simp [AB_def, A_def]);

val AB_step_count_n = Q.store_thm("AB_step_count_n",
 `!l n init fext.
   pulse_spec fext ==>
   ?m. (AB fext init (n + m)).count = (AB fext init n).count + n2w l`,
 rpt strip_tac \\ Induct_on `l`
 >- (qexists_tac `0` \\ rw [AB_def])
 \\ pop_assum strip_assume_tac \\ drule_strip AB_step_count_1 \\
    pop_assum (qspecl_then [`n + m`, `init`] strip_assume_tac) \\
    qexists_tac `m + m'` \\ fs [n2w_SUC]);

val AB_spec = Q.store_thm("AB_spec",
 `!fext init.
  pulse_spec fext ==>
  ?n. (AB fext init n).done`,
 rpt strip_tac \\ Cases_on `10w <+ init.count`
 >- (qexists_tac `SUC 0` \\ simp [AB_def, B_def]) \\
 drule_strip AB_step_count_n \\
 pop_assum (qspecl_then [`11`, `0`, `init`] strip_assume_tac) \\
 fs [] \\ qexists_tac `SUC m` \\
 simp [AB_def, B_def] \\ IF_CASES_TAC >- simp [] \\
 WORD_DECIDE_TAC);

val _ = Datatype `R_state = <| a : word8; b : word8; c : word8 |>`;

val R_def = Define `
 R s = (let s' = s with <| a := 1w; b := 2w |> in
        let s'' = s' with a := s'.a + 1w in
        let tmp = 1w in
        case s''.c of 0w => s'' with c := tmp | _ => s'' with c := 0w)`;

val _ = export_theory ();
