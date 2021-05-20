open hardwarePreamble;

open balanced_mapTheory;

open verilogTheory verilogTypeTheory verilogMetaTheory;

val _ = new_theory "verilogWriteChecker";

Definition compute_writes_size_def:
 (compute_writes_size (INL (_, _, _, p)) = vprog_size p) ∧
 (compute_writes_size (INR (INL (_, _, _, ps))) = vprog1_size ps) ∧
 (compute_writes_size (INR (INR (_, _, _, p))) = vprog3_size p)
End

Definition compute_writes_def:
 (compute_writes bw nbw ws Skip = ws) ∧
 (compute_writes bw nbw ws (Seq p1 p2) = compute_writes bw nbw (compute_writes bw nbw ws p1) p2) ∧
 (compute_writes bw nbw ws (IfElse _ p1 p2) = compute_writes bw nbw (compute_writes bw nbw ws p1) p2) ∧
 (compute_writes bw nbw ws (Case _ _ cs ds) = compute_writes_opt bw nbw (compute_writes_Case bw nbw ws cs) ds) ∧
 (compute_writes bw nbw ws (BlockingAssign lhs _) =
  if bw then insert string_cmp (evwrites lhs) () ws else ws) ∧
 (compute_writes bw nbw ws (NonBlockingAssign lhs _) =
  if nbw then insert string_cmp (evwrites lhs) () ws else ws) ∧

 (compute_writes_Case bw nbw ws [] = ws) ∧
 (compute_writes_Case bw nbw ws ((_, p) :: xs) = compute_writes_Case bw nbw (compute_writes bw nbw ws p) xs) ∧

 (compute_writes_opt bw nbw ws NONE = ws) ∧
 (compute_writes_opt bw nbw ws (SOME p) = compute_writes bw nbw ws p)
Termination
 WF_REL_TAC `measure compute_writes_size` \\ rw [compute_writes_size_def, vprog_size_def]
End

val member_thm_string_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) (SPEC_ALL member_thm)) comparisonTheory.string_cmp_good;

val insert_thm_string_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) (SPEC_ALL insert_thm)) comparisonTheory.string_cmp_good;

Triviality member_insert:
 good_cmp cmp ∧ invariant cmp t ⇒
 member cmp k (insert cmp k' v t) =
 if cmp k k' = Equal then T else member cmp k t
Proof
 rw [member_thm, insert_thm] \\ metis_tac [key_set_eq, comparisonTheory.cmp_thms]
QED

val member_insert_string_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) member_insert) comparisonTheory.string_cmp_good
 |> REWRITE_RULE [comparisonTheory.string_cmp_antisym];

(*Triviality compute_writes_sound1:
 (∀bw nbw ws p.
  invariant string_cmp ws ∧
  (∀var. member string_cmp var ws ⇒
         (bw ∧ MEM var (FLAT (MAP vwrites allcombs)) ∨
         (nbw ∧ MEM var (FLAT (MAP vnwrites allcombs))))) ∧

  (∀var. MEM var (vwrites p) ⇒ MEM var (FLAT (MAP vwrites allcombs))) ∧
  (∀var. MEM var (vnwrites p) ⇒ MEM var (FLAT (MAP vnwrites allcombs))) ⇒

  invariant string_cmp (compute_writes bw nbw ws p) ∧
  (∀var. member string_cmp var (compute_writes bw nbw ws p) ⇒
         (bw ∧ MEM var (FLAT (MAP vwrites allcombs))) ∨
         (nbw ∧ MEM var (FLAT (MAP vnwrites allcombs))))) ∧

 (∀bw nbw ws ps.
  invariant string_cmp ws ∧
  (∀var. member string_cmp var ws ⇒
         (bw ∧ MEM var (FLAT (MAP vwrites allcombs)) ∨
         (nbw ∧ MEM var (FLAT (MAP vnwrites allcombs))))) ∧

  (∀var. MEM var (FLAT (MAP (λ(_, p). vwrites p) ps)) ⇒ MEM var (FLAT (MAP vwrites allcombs))) ∧
  (∀var. MEM var (FLAT (MAP (λ(_, p). vnwrites p) ps)) ⇒ MEM var (FLAT (MAP vnwrites allcombs))) ⇒

  invariant string_cmp (compute_writes_Case bw nbw ws ps) ∧
  (∀var. member string_cmp var (compute_writes_Case bw nbw ws ps) ⇒
         (bw ∧ MEM var (FLAT (MAP vwrites allcombs))) ∨
         (nbw ∧ MEM var (FLAT (MAP vnwrites allcombs))))) ∧

 (∀bw nbw ws ps.
  invariant string_cmp ws ∧
  (∀var. member string_cmp var ws ⇒
         (bw ∧ MEM var (FLAT (MAP vwrites allcombs)) ∨
         (nbw ∧ MEM var (FLAT (MAP vnwrites allcombs))))) ∧

  OPTION_ALL (λp. ∀var. MEM var (vwrites p) ⇒ MEM var (FLAT (MAP vwrites allcombs))) ps ∧
  OPTION_ALL (λp. ∀var. MEM var (vnwrites p) ⇒ MEM var (FLAT (MAP vnwrites allcombs))) ps ⇒

  invariant string_cmp (compute_writes_opt bw nbw ws ps) ∧
  (∀var. member string_cmp var (compute_writes_opt bw nbw ws ps) ⇒
         (bw ∧ MEM var (FLAT (MAP vwrites allcombs))) ∨
         (nbw ∧ MEM var (FLAT (MAP vnwrites allcombs)))))
Proof
 ho_match_mp_tac compute_writes_ind \\ simp [compute_writes_def, vwrites_def, vnwrites_def] \\
 rpt conj_tac \\ rpt strip_tac'
 >- (Cases_on ‘ps'’ \\ fs [])
 \\ TOP_CASE_TAC \\ fs [insert_thm_string_cmp, member_insert_string_cmp] \\ metis_tac []
QED

Triviality compute_writes_sound:
 ∀bw nbw combs ws.
 invariant string_cmp ws ∧
 (∀var. member string_cmp var ws ⇒
        (bw ∧ MEM var (FLAT (MAP vwrites allcombs)) ∨
        (nbw ∧ MEM var (FLAT (MAP vnwrites allcombs))))) ∧

 (∀var. MEM var (FLAT (MAP vwrites combs)) ⇒ MEM var (FLAT (MAP vwrites allcombs))) ∧
 (∀var. MEM var (FLAT (MAP vnwrites combs)) ⇒ MEM var (FLAT (MAP vnwrites allcombs))) ⇒

 invariant string_cmp (FOLDL (compute_writes bw nbw) ws combs) ∧
 (∀var. member string_cmp var (FOLDL (compute_writes bw nbw) ws combs) ⇒
        (bw ∧ MEM var (FLAT (MAP vwrites allcombs))) ∨
        (nbw ∧ MEM var (FLAT (MAP vnwrites allcombs))))
Proof
 ntac 2 gen_tac \\ Induct \\ simp [] \\ rpt strip_tac' \\ last_x_assum irule \\ 
 drule_strip (CONJUNCT1 compute_writes_sound1) \\ metis_tac []
QED*)

Triviality compute_writes_sound1:
 (∀bw nbw ws p.
  invariant string_cmp ws ⇒
  invariant string_cmp (compute_writes bw nbw ws p) ∧
  (∀var. member string_cmp var (compute_writes bw nbw ws p) ⇒
         member string_cmp var ws ∨
         (bw ∧ MEM var (vwrites p)) ∨
         (nbw ∧ MEM var (vnwrites p)))) ∧

 (∀bw nbw ws ps.
  invariant string_cmp ws ⇒
  invariant string_cmp (compute_writes_Case bw nbw ws ps) ∧
  (∀var. member string_cmp var (compute_writes_Case bw nbw ws ps) ⇒
         member string_cmp var ws ∨
         (bw ∧ MEM var (FLAT (MAP (λ(_, p). vwrites p) ps))) ∨
         (nbw ∧ MEM var (FLAT (MAP (λ(_, p). vnwrites p) ps))))) ∧

 (∀bw nbw ws ps.
  invariant string_cmp ws ⇒
  invariant string_cmp (compute_writes_opt bw nbw ws ps) ∧
  (∀var. member string_cmp var (compute_writes_opt bw nbw ws ps) ⇒
         member string_cmp var ws ∨
         (bw ∧ (case ps of NONE => F | SOME ps => MEM var (vwrites ps))) ∨
         (nbw ∧ (case ps of NONE => F | SOME ps => MEM var (vnwrites ps)))))
Proof
 ho_match_mp_tac compute_writes_ind \\ simp [compute_writes_def, vwrites_def, vnwrites_def] \\
 rpt conj_tac \\ rpt strip_tac' \\
 every_case_tac \\ fs [insert_thm_string_cmp, member_insert_string_cmp] \\ metis_tac []
QED

Triviality compute_writes_sound:
 ∀ps bw nbw ws.
 invariant string_cmp ws ⇒
 invariant string_cmp (FOLDL (compute_writes bw nbw) ws ps) ∧
 (∀var. member string_cmp var (FOLDL (compute_writes bw nbw) ws ps) ⇒
        member string_cmp var ws ∨
        (bw ∧ MEM var (FLAT (MAP vwrites ps))) ∨
        (nbw ∧ MEM var (FLAT (MAP vnwrites ps))))
Proof
 Induct \\ simp [] \\ metis_tac [compute_writes_sound1]
QED

Triviality compute_writes_mono1:
 (∀bw nbw ws p.
  invariant string_cmp ws ⇒

  invariant string_cmp (compute_writes bw nbw ws p) ∧
  (∀var. member string_cmp var ws ⇒ member string_cmp var (compute_writes bw nbw ws p))) ∧

 (∀bw nbw ws ps.
  invariant string_cmp ws ⇒

  invariant string_cmp (compute_writes_Case bw nbw ws ps) ∧
  (∀var. member string_cmp var ws ⇒ member string_cmp var (compute_writes_Case bw nbw ws ps))) ∧

 (∀bw nbw ws ps.
  invariant string_cmp ws ⇒

  invariant string_cmp (compute_writes_opt bw nbw ws ps) ∧
  (∀var. member string_cmp var ws ⇒ member string_cmp var (compute_writes_opt bw nbw ws ps)))
Proof
 ho_match_mp_tac compute_writes_ind \\ rw [compute_writes_def, insert_thm_string_cmp, member_insert_string_cmp]
QED

Triviality compute_writes_mono:
 ∀ps bw nbw ws.
 invariant string_cmp ws ⇒
 invariant string_cmp (FOLDL (compute_writes bw nbw) ws ps) ∧
 (∀var. member string_cmp var ws ⇒ member string_cmp var (FOLDL (compute_writes bw nbw) ws ps))
Proof
 Induct \\ simp [] \\ metis_tac [compute_writes_mono1]
QED

(* TODO: Why do we need a separate _mono1 here? Metis is happy, but why? *)
Triviality compute_writes_complete1:
 (∀bw nbw ws p.
  invariant string_cmp ws ⇒

  invariant string_cmp (compute_writes bw nbw ws p) ∧
  (∀var. bw ∧ MEM var (vwrites p) ⇒ member string_cmp var (compute_writes bw nbw ws p)) ∧
  (∀var. nbw ∧ MEM var (vnwrites p) ⇒ member string_cmp var (compute_writes bw nbw ws p)) ∧
  (∀var. member string_cmp var ws ⇒ member string_cmp var (compute_writes bw nbw ws p))) ∧

 (∀bw nbw ws ps.
  invariant string_cmp ws ⇒

  invariant string_cmp (compute_writes_Case bw nbw ws ps) ∧
  (∀var. bw ∧ MEM var (FLAT (MAP (λ(_, p). vwrites p) ps)) ⇒ member string_cmp var (compute_writes_Case bw nbw ws ps)) ∧
  (∀var. nbw ∧ MEM var (FLAT (MAP (λ(_, p). vnwrites p) ps)) ⇒ member string_cmp var (compute_writes_Case bw nbw ws ps)) ∧
  (∀var. member string_cmp var ws ⇒ member string_cmp var (compute_writes_Case bw nbw ws ps))) ∧

 (∀bw nbw ws ps.
  invariant string_cmp ws ⇒

  invariant string_cmp (compute_writes_opt bw nbw ws ps) ∧
  (OPTION_ALL (λp. ∀var. bw ∧ MEM var (vwrites p) ⇒ member string_cmp var (compute_writes bw nbw ws p)) ps) ∧
  (OPTION_ALL (λp. ∀var. nbw ∧ MEM var (vnwrites p) ⇒ member string_cmp var (compute_writes bw nbw ws p)) ps) ∧
  (∀var. member string_cmp var ws ⇒ member string_cmp var (compute_writes_opt bw nbw ws ps)))
Proof
 ho_match_mp_tac compute_writes_ind \\ simp [compute_writes_def, vwrites_def, vnwrites_def] \\
 rpt conj_tac \\ rpt strip_tac' \\ every_case_tac \\
 fs [compute_writes_def, insert_thm_string_cmp, member_insert_string_cmp] \\
 metis_tac [compute_writes_mono1]
QED

Triviality compute_writes_complete:
 ∀combs bw nbw ws.
 invariant string_cmp ws ⇒
 invariant string_cmp (FOLDL (compute_writes bw nbw) ws combs) ∧
 (∀var. bw ∧ MEM var (FLAT (MAP vwrites combs)) ⇒ member string_cmp var (FOLDL (compute_writes bw nbw) ws combs)) ∧
 (∀var. nbw ∧ MEM var (FLAT (MAP vnwrites combs)) ⇒ member string_cmp var (FOLDL (compute_writes bw nbw) ws combs)) ∧
 (∀var. member string_cmp var ws ⇒ member string_cmp var (FOLDL (compute_writes bw nbw) ws combs))
Proof
 Induct \\ simp [] \\ metis_tac [compute_writes_complete1]
QED

Definition compute_writes_bw_def:
 compute_writes_bw ps = FOLDL (compute_writes T F) empty ps
End

Theorem invariant_compute_writes_bw:
 ∀ps. invariant string_cmp (compute_writes_bw ps)
Proof
 simp [compute_writes_bw_def, compute_writes_complete, empty_def, invariant_def]
QED

Theorem compute_writes_bw_correct:
 ∀ps var. member string_cmp var (compute_writes_bw ps) ⇔ MEM var (FLAT (MAP vwrites ps))
Proof
 metis_tac [compute_writes_bw_def,
            compute_writes_sound, compute_writes_complete, empty_def, member_def, invariant_def]
QED

(* Temporary: *)
Definition compute_writes_bw_inc_def:
 compute_writes_bw_inc ws ps = FOLDL (compute_writes T F) ws ps
End

(*Triviality compute_writes_bw_inc_correct_lem:
 ∀ps ws.
 invariant string_cmp ws ⇒
 (* This assumption is needed for soundness thm, but we could probably remove it if needed: *)
 ∀var. member string_cmp var (compute_writes_bw_inc ws ps) ⇔
       (member string_cmp var ws ∨ MEM var (FLAT (MAP vwrites ps)))
Proof
 metis_tac [compute_writes_bw_inc_def,
            compute_writes_sound, compute_writes_complete, compute_writes_mono]
QED*)

Theorem compute_writes_bw_inc_correct:
 ∀ps ps' var.
 member string_cmp var (compute_writes_bw_inc (compute_writes_bw ps) ps') ⇔
 (MEM var (FLAT (MAP vwrites ps')) ∨ MEM var (FLAT (MAP vwrites ps)))
Proof
 metis_tac [compute_writes_bw_def, compute_writes_bw_inc_def,
            compute_writes_sound, compute_writes_complete, compute_writes_mono,
            empty_def, member_def, invariant_def]
QED

Definition compute_writes_bw_nbw_def:
 compute_writes_bw_nbw ps = FOLDL (compute_writes T T) empty ps
End

Theorem compute_writes_bw_nbw_correct:
 ∀ps var.
 member string_cmp var (compute_writes_bw_nbw ps) ⇔
 MEM var (FLAT (MAP vwrites ps)) ∨  MEM var (FLAT (MAP vnwrites ps))
Proof
 metis_tac [compute_writes_bw_nbw_def,
            compute_writes_sound, compute_writes_complete, empty_def, member_def, invariant_def]
QED

Definition check_forbidden_def:
 (check_forbidden bw nbw ws Skip ⇔ T) ∧
 (check_forbidden bw nbw ws (Seq p1 p2) ⇔ (check_forbidden bw nbw ws p1 ∧ check_forbidden bw nbw ws p2)) ∧
 (check_forbidden bw nbw ws (IfElse _ p1 p2) ⇔ (check_forbidden bw nbw ws p1 ∧ check_forbidden bw nbw ws p2)) ∧
 (check_forbidden bw nbw ws (Case _ _ cs ds) ⇔ (check_forbidden_Case bw nbw ws cs ∧ check_forbidden_opt bw nbw ws ds)) ∧
 (check_forbidden bw nbw ws (BlockingAssign lhs _) ⇔
  (~bw ∨ ~member string_cmp (evwrites lhs) ws)) ∧
 (check_forbidden bw nbw ws (NonBlockingAssign lhs _) ⇔
  (~nbw ∨ ~member string_cmp (evwrites lhs) ws)) ∧

 (check_forbidden_Case bw nbw ws [] ⇔ T) ∧
 (check_forbidden_Case bw nbw ws ((_, p) :: xs) ⇔ (check_forbidden bw nbw ws p ∧ check_forbidden_Case bw nbw ws xs)) ∧

 (check_forbidden_opt bw nbw ws NONE ⇔ T) ∧
 (check_forbidden_opt bw nbw ws (SOME p) ⇔ check_forbidden bw nbw ws p)
Termination
 WF_REL_TAC `measure compute_writes_size` \\ rw [compute_writes_size_def, vprog_size_def]
End

Theorem check_forbidden_correct1:
 (∀bw nbw (ws : (string, 'a) balanced_map) p.
  check_forbidden bw nbw ws p ⇔
  (∀var. bw ∧ member string_cmp var ws ⇒ ~MEM var (vwrites p)) ∧
  (∀var. nbw ∧ member string_cmp var ws ⇒ ~MEM var (vnwrites p))) ∧

 (∀bw nbw (ws : (string, 'a) balanced_map) ps.
  check_forbidden_Case bw nbw ws ps ⇔
  (∀var. bw ∧ member string_cmp var ws ⇒ ~MEM var (FLAT (MAP (λ(_, p). vwrites p) ps))) ∧
  (∀var. nbw ∧ member string_cmp var ws ⇒ ~MEM var (FLAT (MAP (λ(_, p). vnwrites p) ps)))) ∧

 (∀bw nbw (ws : (string, 'a) balanced_map) ps.
  check_forbidden_opt bw nbw ws ps ⇔
  OPTION_ALL (λp. ∀var. bw ∧ member string_cmp var ws ⇒ ~MEM var (vwrites p)) ps ∧
  OPTION_ALL (λp. ∀var. nbw ∧ member string_cmp var ws ⇒ ~MEM var (vnwrites p)) ps)
Proof
 ho_match_mp_tac check_forbidden_ind \\ simp [check_forbidden_def, vwrites_def, vnwrites_def] \\
 rpt conj_tac \\ rpt gen_tac \\ TRY CASE_TAC \\ simp [] \\ metis_tac []
QED

Theorem check_forbidden_correct:
 EVERY (check_forbidden bw nbw ws) ps ⇔
 (∀var. bw ∧ member string_cmp var ws ⇒ ~MEM var (FLAT (MAP vwrites ps))) ∧
 (∀var. nbw ∧ member string_cmp var ws ⇒ ~MEM var (FLAT (MAP vnwrites ps)))
Proof
 simp [GSYM EVERY_MEM_MEM_FLAT_MAP, EVERY_MEM] \\ metis_tac [check_forbidden_correct1]
QED

Triviality writes_ok_compute_old:
 !ps. writes_ok ps ⇔ EVERY (λvar. ~MEM var (FLAT (MAP vnwrites ps))) (FLAT (MAP vwrites ps))
Proof
 rw [writes_ok_def, EVERY_MEM] \\ metis_tac []
QED

(* An even more efficient way would be to have a map string -> {bw, nbw}
   and make sure all writes are of the same type... *)
Theorem writes_ok_compute:
 ∀ps. writes_ok ps ⇔ EVERY (check_forbidden F T (compute_writes_bw ps)) ps
Proof
 metis_tac [writes_ok_def, check_forbidden_correct, compute_writes_bw_correct]
QED

Definition check_module_def:
 check_module pseudos m =
  let ffs_bw = compute_writes_bw m.ffs in
  if EVERY (check_forbidden F T ffs_bw) m.ffs ∧
     EVERY (check_forbidden F T pseudos) m.combs ∧
     EVERY (check_forbidden T T pseudos) m.ffs then
   INR ()
  else
   INL InvalidProgram
End

Theorem check_module_correct:
 ∀m pseudos.
 check_module pseudos m = INR () ∧
 (∀var. member string_cmp var pseudos ⇔ MEM var (FLAT (MAP vwrites m.combs))) ⇒
 module_ok m
Proof
 rw [check_module_def, module_ok_def, writes_ok_compute] \\
 fs [writes_overlap_ok_def, check_forbidden_correct, compute_writes_bw_correct]
QED

val _ = export_theory ();
