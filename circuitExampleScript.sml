open preamble;

open wordsTheory;

val _ = new_theory "circuitExample";

val _ = Datatype `cstate = <| a : word8; b : word8; c : word8; d : word8 |>`;

val P_def = Define `
 P s = s with c := s.a + s.b`;

val Q_def = Define `
 Q s = if s.c <=+ 10w then (s with d := s.c) else (s with d := 0w)`;

val PQ_def = Define `
 PQ s = s with <| c := (P s).c; d := (Q s).d |>`;

val PQ_ok = Q.store_thm("PQ_ok",
 `!n s. n >= 2 /\ s.a <=+ 5w /\ s.b <=+ 5w ==> ((FUNPOW PQ n s).d = s.b + s.a)`,
 Cases >- simp [] \\ Cases_on `n'` >- simp [] \\ Induct_on `n` \\ rpt strip_tac
 >- (EVAL_TAC \\ IF_CASES_TAC >- simp [] \\ blastLib.FULL_BBLAST_TAC)
 \\ once_rewrite_tac [arithmeticTheory.FUNPOW] \\ fs [PQ_def]);

(* More complex example *)

val R_def = Define `
 R s = (let s' = s with <| a := 1w; b := 2w |> in
        let s'' = s' with a := s'.a + 1w in
        let tmp = 1w in
        case s''.c of 0w => s'' with c := tmp | _ => s'' with c := 0w)`;

val _ = export_theory ();
