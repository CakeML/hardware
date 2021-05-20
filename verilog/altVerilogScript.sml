open hardwarePreamble;

open alistTheory;

open sumExtraTheory verilogTheory verilogMetaTheory;

val _ = new_theory "altVerilog";

(* "Alternative" Verilog semantics with observable combinational state *)

Definition alt_mrun_def:
 (alt_mrun fext fbits cs ps vs 0 = INR (vs, fbits)) ∧
 (alt_mrun fext fbits cs ps vs (SUC n) = do
  (vs, fbits) <- alt_mrun fext fbits cs ps vs n;
  (vs, fbits) <- mstep_commit (fext n) fbits ps vs;
  (vs, fbits) <- mstep_commit (fext (SUC n)) fbits cs vs
 od)
End

Definition alt_run_def:
 alt_run fext fbits (Module fexttys decls cs ps mem) n = do
  (fbits', vs) <<- run_decls fbits decls [];
  (vs, fbits') <- mstep_commit (fext 0) fbits' cs vs;
  alt_mrun fext fbits' cs ps vs n
 od 
End

(* The two semantics are eq. *)

Definition all_writes_def:
 all_writes p = vwrites p ++ vnwrites p
End

Definition all_writes_list_def:
 all_writes_list ps = FLAT (MAP all_writes ps)
End

Triviality mstep_commit_cons:
 vnwrites p = [] ⇒
 (mstep_commit fext fbits (p::ps) vs = INR res ⇔
 ∃s. prun fext <| vars := vs; nbq := []; fbits := fbits |> p = INR s ∧
     mstep_commit fext s.fbits ps s.vars = INR res)
Proof
 simp [mstep_commit_def, mstep_def, sum_foldM_INR, sum_map_INR] \\ strip_tac \\ eq_tac \\ rpt strip_tac \\
 rename1 ‘prun _ _ _ = INR s''’ \\ drule_strip vnwrites_nil_correct \\
 ‘<|vars := s''.vars; nbq := []; fbits := s''.fbits|> = s''’ by simp [pstate_component_equality] \\
 fs []
QED

Triviality mstep_commit_append:
 ∀cs ps fext fbits vs res.
 mstep_commit fext fbits (cs ⧺ ps) vs = INR res ∧
 (FLAT (MAP vnwrites cs) = []) ⇒
 ∃vs' fbits'. mstep_commit fext fbits cs vs = INR (vs', fbits') ∧
              mstep_commit fext fbits' ps vs' = INR res
Proof
 Induct >- simp [mstep_commit_def, mstep_def, sum_foldM_def, sum_map_def] \\
 simp [] \\ rpt strip_tac \\ drule_strip mstep_commit_cons \\ fs []
QED

Theorem alt_mrun_mrun:
 ∀n fext fbits fbits' fbits'' alt_fbits cs ps vs vs' vs'' alt_vs.
 mrun fext fbits (cs ⧺ ps) vs n = INR (vs', fbits') ∧
 mstep_commit (fext n) fbits' cs vs' = INR (vs'', fbits'') ∧ (* ++ ps in orig *)
 mstep_commit (fext 0) fbits cs vs = INR (alt_vs, alt_fbits) ∧
 (FLAT (MAP vnwrites cs) = []) ⇒

 alt_mrun fext alt_fbits cs ps alt_vs n = INR (vs'', fbits'')
Proof
 Induct >- (simp [mrun_def, alt_mrun_def] \\ rpt strip_tac' \\ fs []) \\
 simp [mrun_def, alt_mrun_def, sum_bind_INR] \\ rpt strip_tac' \\
 pairarg_tac \\ fs [] \\ rveq \\

 drule_strip mstep_commit_append \\ drule_first \\ simp [sum_bind_def]
QED

Triviality MEM_all_writes_list:
 ∀ps var. MEM var (all_writes_list ps) ⇔
          MEM var (FLAT (MAP vwrites ps)) ∨ MEM var (FLAT (MAP vnwrites ps))
Proof
 simp [all_writes_list_def, MEM_FLAT, MEM_MAP] \\ rpt strip_tac \\ eq_tac \\
 strip_tac \\ rveq \\ fs [all_writes_def] \\ metis_tac [MEM_APPEND]
QED

Triviality MEM_all_writes_list_EVERY_MEM:
 ∀ps var. ¬MEM var (all_writes_list ps) ⇔
          EVERY (λp. ¬MEM var (vwrites p)) ps ∧ EVERY (λp. ¬MEM var (vnwrites p)) ps
Proof
 rw [MEM_all_writes_list, EVERY_MEM, MEM_FLAT, MEM_MAP] \\ metis_tac []
QED

Triviality mstep_commit_same_after:
 mstep_commit fext fbits ps vs = INR (vs', fbits') ⇒
 (!var. ¬MEM var (all_writes_list ps) ⇒ ALOOKUP vs' var = ALOOKUP vs var)
Proof
 rw [mstep_commit_def, sum_map_INR] \\ drule_strip mstep_same_after \\
 fs [MEM_all_writes_list_EVERY_MEM, ALOOKUP_APPEND,
     get_var_get_var_ALOOKUP_ALOOKUP, get_nbq_var_get_nbq_var_ALOOKUP_ALOOKUP]
QED

Theorem alt_run_run:
 ∀n fexttys decls cs ps mem fext fbits.
 let m = Module fexttys decls cs ps mem in
 (∀fext fbits n. ∃res. run fext fbits m n = INR res) ∧ (* never crashes (dynamic fact from corr thm.) *)

 (* no overlap between cs and ps, need to check this instead of having assumptions here: *)
 (∀var. MEM var (all_writes_list cs) ⇒ is_nostore_var decls var) ∧
 (∀var. MEM var (all_writes_list ps) ⇒ is_store_var decls var) ∧

 (FLAT (MAP vnwrites cs) = []) ⇒ (* combinational part should have no non-blocking writes... *)
 ∃vs vs_alt vs' vs'' fbits_alt fbits' fbits''.
  alt_run fext fbits m n = INR (vs_alt, fbits_alt) ∧

  run fext fbits m n = INR (vs', fbits') ∧
  run fext fbits m (SUC n) = INR (vs'', fbits'') ∧

  (∀var. ALOOKUP vs_alt var = if MEM var (all_writes_list ps) then ALOOKUP vs' var else ALOOKUP vs'' var)
Proof
 simp [] \\ rpt strip_tac \\
 first_assum (qspecl_then [‘fext’, ‘fbits’, ‘SUC 0’] strip_assume_tac) \\ pop_assum mp_tac \\
 first_x_assum (qspecl_then [‘fext’, ‘fbits’, ‘SUC n’] strip_assume_tac) \\ pop_assum mp_tac \\
 simp [run_def, mrun_def, alt_run_def] \\ pairarg_tac \\ simp [sum_bind_INR] \\
 rpt strip_tac \\ pairarg_tac \\ fs [] \\ rveq \\
      
 drule_strip mstep_commit_append \\ simp [] \\ PairCases_on ‘res'’ \\ simp [] \\
 qpat_x_assum ‘mstep_commit (fext n) _ _ _ = _’ assume_tac \\
 drule_strip mstep_commit_append \\ drule_strip alt_mrun_mrun \\ simp [] \\ rw []
 >- (‘~MEM var (all_writes_list cs)’ by cheat \\
     metis_tac [mstep_commit_same_after])
 >- metis_tac [mstep_commit_same_after]
QED

(* TODO: Write text about it... event-driven vs. snapshots... *)

val _ = export_theory ();
