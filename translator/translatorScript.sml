open hardwarePreamble;

open alistTheory wordsTheory stringTheory bitstringTheory sptreeTheory;
open wordsLib bitstringLib;

open oracleTheory sumExtraTheory verilogTheory verilogMetaTheory verilogTypeTheory;

open stringSyntax;

open translatorCoreLib;

val _ = new_theory "translator";

Definition mk_circuit_def:
 (mk_circuit sstep cstep s fext 0 = cstep (fext 0) s s) ∧
 (mk_circuit sstep cstep s fext (SUC n) = let
  s = mk_circuit sstep cstep s fext n;
  s = sstep (fext n) s s in
  cstep (fext (SUC n)) s s)
End

(* Might want to rename this... anyhow currently fbits handling is quite trivial... *)
Definition mk_module_def:
 mk_module sstep cstep s fext (fbits : num -> bool) n = mk_circuit sstep cstep (s fbits) fext n
End

(* mk_circuit with an extra cstep call so we don't have to carry around comb information *)
Definition mk_circuit_extra_def:
 (mk_circuit_extra sstep cstep s fext 0 = cstep (fext 0) s s) ∧
 (mk_circuit_extra sstep cstep s fext (SUC n) = let
  s = mk_circuit_extra sstep cstep s fext n;
  s = cstep (fext n) s s;
  s = sstep (fext n) s s in
  cstep (fext (SUC n)) s s)
End

Definition mk_module_extra_def:
 mk_module_extra sstep cstep s fext (fbits : num -> bool) n = mk_circuit_extra sstep cstep (s fbits) fext n
End

Theorem cstep_mk_circuit_extra:
 ∀n.
 (* can be relaxed to refer to outer fext: *)
 (∀fext s. cstep fext (cstep fext s s) (cstep fext s s) = cstep fext s s) ⇒
 cstep (fext n) (mk_circuit_extra sstep cstep s fext n) (mk_circuit_extra sstep cstep s fext n) =
 mk_circuit_extra sstep cstep s fext n
Proof
 Induct \\ rw [mk_circuit_extra_def]
QED

Theorem mk_circuit_mk_circuit_extra:
 (∀fext s. cstep fext (cstep fext s s) (cstep fext s s) = cstep fext s s) ⇒
 mk_circuit sstep cstep s = mk_circuit_extra sstep cstep s
Proof
 rpt strip_tac \\ simp [FUN_EQ_THM] \\ gen_tac \\ Induct >- EVAL_TAC \\
 simp [mk_circuit_extra_def, cstep_mk_circuit_extra, mk_circuit_def]
QED

Theorem mk_module_mk_module_extra:
 (∀fext s. cstep fext (cstep fext s s) (cstep fext s s) = cstep fext s s) ⇒
 mk_module sstep cstep s = mk_module_extra sstep cstep s
Proof
 simp [FUN_EQ_THM, mk_module_def, mk_module_extra_def, mk_circuit_mk_circuit_extra]
QED

(* Apply all processes in list of processes *)
Definition procs_def:
 (procs [] fext s s' = s') ∧
 (procs (p::ps) fext s s' = procs ps fext s (p fext s s'))
End

Theorem procs_sing:
 ∀p. procs [p] = p
Proof
 rw [procs_def, FUN_EQ_THM]
QED

(* "Generalized" GENLIST *)
Definition ggenlist_def:
 ggenlist f start len = GENLIST (λi. f (i + start)) len
End

(** Translator stuff **)

(* TODO: Move... *)
(* TODO: Generate at the same time as the above? *)
(* val comms = ["h0", "h1", "h2", "h3"]; *)

(** State relation **)

(* Externally provided things *)
(*Definition comms_def:
 comms = ["h0"; "h1"; "h2"; "h3"]
End

val state_var_def =
 TypeBase.fields_of state_ty
 |> map (fromMLstring o fst)
 |> (fn tms => listSyntax.mk_list (tms, string_ty))
 |> (fn tm => Define `state_var name = MEM name ^tm`);*)

(* "Non-communication" variable *)
Definition state_rel_var_def:
 state_rel_var hol_s ver_s var a accessf ⇔
  (∃v. get_var ver_s var = INR v ∧ a (accessf hol_s) v) ∧
  (get_nbq_var ver_s var = INL UnknownVariable)
End

Definition get_cvar_rel_def:
 get_cvar_rel s name =
  case ALOOKUP (s.nbq ++ s.vars) name of
    NONE => INL UnknownVariable
  | SOME v => INR v
End

Theorem get_cvar_rel_alt:
 ∀s name. get_cvar_rel s name = sum_alookup (s.nbq ⧺ s.vars) name
Proof
 rw [get_cvar_rel_def, sum_alookup_def]
QED

(* Ops, maybe could have simply used this one? *)
Theorem get_cvar_rel_get_use_nbq_var:
 ∀s name. get_cvar_rel s name = get_use_nbq_var s T name
Proof
 rw [get_cvar_rel_alt, get_use_nbq_var_sum_alookup]
QED

(* "Communication" variable *)
Definition state_rel_cvar_def:
 state_rel_cvar hol_s hol_s' ver_s var a accessf ⇔
  (∃v. get_var ver_s var = INR v ∧ a (accessf hol_s) v) ∧
  (∃v. get_cvar_rel ver_s var = INR v ∧ a (accessf hol_s') v)
End

(** State relation for modules **)

Definition module_state_rel_var_def:
 module_state_rel_var hol_s ver_s var a accessf ⇔
  (∃v. ALOOKUP ver_s var = SOME v ∧ a (accessf hol_s) v)
End

(** fext relation **)

Definition fext_rel_n_def:
 fext_rel_n fext_rel fextv fext = ∀n. fext_rel (fextv n) (fext n)
End

(** Expressions **)

Definition Eval_exp_def:
 Eval_exp fext_rel rel fext s s' env P exp ⇔
  ∀fextv ver_s.
   rel s s' (ver_s with vars := env) ∧ fext_rel fextv fext ⇒
   ∃res. erun fextv (ver_s with vars := env) exp = INR res ∧ P res
End

Theorem var_thm_BOOL:
 !fext_rel rel s s' b var.
 var_has_value env var (BOOL b) ==> Eval_exp fext_rel rel fext s s' env (BOOL b) (Var var)
Proof
 rw [var_has_value_def, Eval_exp_def, erun_def, erun_get_var_def, get_var_def] \\ rw []
QED

Theorem var_thm_WORD:
 !fext_rel rel s s' w var.
 var_has_value env var (WORD w) ==> Eval_exp fext_rel rel fext s s' env (WORD w) (Var var)
Proof
 rw [var_has_value_def, Eval_exp_def, erun_def, erun_get_var_def, get_var_def] \\ rw []
QED

Theorem Eval_exp_bool:
 !b fext_rel rel s s'. Eval_exp fext_rel rel fext s s' env (BOOL b) (Const (VBool b))
Proof
 rw [Eval_exp_def, erun_def, BOOL_def]
QED

Theorem Eval_exp_neg:
 !fext_rel rel s s' b bexp.
 Eval_exp fext_rel rel fext s s' env (BOOL b) bexp ⇒ Eval_exp fext_rel rel fext s s' env (BOOL ~b) (BUOp Not bexp)
Proof
 rw [BOOL_def, Eval_exp_def, erun_def, sum_bind_def, ver_liftVBool_def]
QED

Triviality Eval_exp_bbop:
 !fext_rel rel s s' b1 v1 b2 v2.
  Eval_exp fext_rel rel fext s s' env (BOOL b1) v1 /\
  Eval_exp fext_rel rel fext s s' env (BOOL b2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (BOOL (b1 /\ b2)) (BBOp v1 And v2) /\
  Eval_exp fext_rel rel fext s s' env (BOOL (b1 \/ b2)) (BBOp v1 Or v2) /\
  Eval_exp fext_rel rel fext s s' env (BOOL (b1 = b2)) (BBOp v1 Equal v2)
Proof
 rw [Eval_exp_def] \\ rpt drule_first \\
 fs [erun_def, BOOL_def, sum_bind_def, erun_bbop_def]
QED

Triviality Eval_exp_arith:
 !fext_rel rel s s' w1 v1 w2 v2.
  Eval_exp fext_rel rel fext s s' env (WORD w1) v1 /\
  Eval_exp fext_rel rel fext s s' env (WORD w2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (WORD (w1 - w2)) (Arith v1 Minus v2) /\
  Eval_exp fext_rel rel fext s s' env (WORD (w1 + w2)) (Arith v1 Plus v2) /\
  Eval_exp fext_rel rel fext s s' env (WORD (w1 * w2)) (Arith v1 Times v2)
Proof
 rw [Eval_exp_def, erun_def, WORD_def] \\ res_tac \\ PURE_REWRITE_TAC [GSYM WORD_NEG_MUL] \\
 rw [sum_bind_def, sum_map_def,
     w2ver_def, ver2n_def, n2ver_def, v2ver_def, ver2v_def, v2n_w2v, w2v_n2w,
     ver_mapVArray_def, sum_mapM_ver2bool_VBool, ver_liftVArray_def, erun_arith_def,
     ver_fixwidth_fixwidth,
     (* specific for add *) word_add_def, word_mul_def, word_2comp_def, dimword_def]
QED

Theorem Eval_exp_WORD_Minus:
 !fext_rel rel s s' w1 v1 w2 v2.
  Eval_exp fext_rel rel fext s s' env (WORD w1) v1 /\
  Eval_exp fext_rel rel fext s s' env (WORD w2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (WORD (w1 - w2)) (Arith v1 Minus v2)
Proof
 rw [Eval_exp_arith]
QED

Theorem Eval_exp_WORD_Plus:
 !fext_rel rel s s' w1 v1 w2 v2.
  Eval_exp fext_rel rel fext s s' env (WORD w1) v1 /\
  Eval_exp fext_rel rel fext s s' env (WORD w2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (WORD (w1 + w2)) (Arith v1 Plus v2)
Proof
 rw [Eval_exp_arith]
QED

Theorem Eval_exp_WORD_Times:
 !fext_rel rel s s' w1 v1 w2 v2.
  Eval_exp fext_rel rel fext s s' env (WORD w1) v1 /\
  Eval_exp fext_rel rel fext s s' env (WORD w2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (WORD (w1 * w2)) (Arith v1 Times v2)
Proof
 rw [Eval_exp_arith]
QED

(* UGLY: Everything with this proof is ugly *)
Theorem ver_msb_w2ver:
 !w. ver_msb (w2ver w) = INR (word_msb w)
Proof
 rw [w2ver_def] \\ bitstringLib.Cases_on_v2w `w` \\
 fs [w2v_v2w, word_msb_v2w, markerTheory.Abbrev_def] \\
 Cases_on `v` \\ fs [testbit_el, ver_msb_def]
QED

Theorem Eval_exp_WORD_cmp:
 !fext_rel rel s s' w1 v1 w2 v2.
  Eval_exp fext_rel rel fext s s' env (WORD w1) v1 /\
  Eval_exp fext_rel rel fext s s' env (WORD w2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (BOOL (w1 = w2)) (Cmp v1 ArrayEqual v2) /\
  (*Eval_exp fext_rel rel fext s s' env (BOOL (w1 <> w2)) (Cmp v1 ArrayNotEqual v2) /\*)
  Eval_exp fext_rel rel fext s s' env (BOOL (w1 < w2)) (Cmp v1 LessThan v2) /\
  Eval_exp fext_rel rel fext s s' env (BOOL (w1 <+ w2)) (Cmp v1 LowerThan v2) /\
  Eval_exp fext_rel rel fext s s' env (BOOL (w1 <= w2)) (Cmp v1 LessThanOrEqual v2) /\
  Eval_exp fext_rel rel fext s s' env (BOOL (w1 <=+ w2)) (Cmp v1 LowerThanOrEqual v2)
Proof
 rw [Eval_exp_def, erun_def, erun_cmp_def,
     WORD_def, BOOL_def, w2ver_bij, ver2n_w2ver,
     sum_bind_def, sum_for_def, sum_map_def]
 >- simp [get_VArray_data_def, w2ver_def, sum_bind_def, w2v_bij]
 \\ TRY (simp [ver_msb_w2ver, WORD_LT, WORD_LE, sum_bind_def, sum_map_def] \\ NO_TAC)
 \\ Cases_on_word `w1` \\ Cases_on_word `w2` \\ simp [w2n_n2w, word_lo_n2w, word_ls_n2w]
QED

Theorem Eval_exp_WORD_Equal:
 !fext_rel rel s s' w1 v1 w2 v2.
  Eval_exp fext_rel rel fext s s' env (WORD w1) v1 /\
  Eval_exp fext_rel rel fext s s' env (WORD w2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (BOOL (w1 = w2)) (Cmp v1 ArrayEqual v2)
Proof
 rw [Eval_exp_WORD_cmp]
QED

(*val Eval_WORD_NotEqual = Q.store_thm("Eval_WORD_NotEqual",
 `!s w1 v1 w2 v2.
   Eval fext s env (WORD w1) v1 /\
   Eval fext s env (WORD w2) v2 ==>
   Eval fext s env (BOOL (w1 <> w2)) (Cmp v1 ArrayNotEqual v2)`,
 rw [Eval_WORD_cmp]);*)

Theorem Eval_exp_WORD_LessThan:
 !fext_rel rel s s' w1 v1 w2 v2.
  Eval_exp fext_rel rel fext s s' env (WORD w1) v1 /\
  Eval_exp fext_rel rel fext s s' env (WORD w2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (BOOL (w1 < w2)) (Cmp v1 LessThan v2)
Proof
 rw [Eval_exp_WORD_cmp]
QED

Theorem Eval_exp_WORD_LowerThan:
 !fext_rel rel s s' w1 v1 w2 v2.
  Eval_exp fext_rel rel fext s s' env (WORD w1) v1 /\
  Eval_exp fext_rel rel fext s s' env (WORD w2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (BOOL (w1 <+ w2)) (Cmp v1 LowerThan v2)
Proof
 rw [Eval_exp_WORD_cmp]
QED

Theorem Eval_exp_WORD_LessThanOrEqual:
 !fext_rel rel s s' w1 v1 w2 v2.
  Eval_exp fext_rel rel fext s s' env (WORD w1) v1 /\
  Eval_exp fext_rel rel fext s s' env (WORD w2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (BOOL (w1 <= w2)) (Cmp v1 LessThanOrEqual v2)
Proof
 rw [Eval_exp_WORD_cmp]
QED

Theorem Eval_exp_WORD_LowerThanOrEqual:
 !fext_rel rel s s' w1 v1 w2 v2.
  Eval_exp fext_rel rel fext s s' env (WORD w1) v1 /\
  Eval_exp fext_rel rel fext s s' env (WORD w2) v2 ==>
  Eval_exp fext_rel rel fext s s' env (BOOL (w1 <=+ w2)) (Cmp v1 LowerThanOrEqual v2)
Proof
 rw [Eval_exp_WORD_cmp]
QED

(* Need to go through n -> w -> ver because we need to truncate the word in the same way as LHS *)
Theorem Eval_exp_word_const:
 !fext_rel rel s s' n.
  Eval_exp fext_rel rel fext s s' env (WORD ((n2w n) : 'a word)) (Const (w2ver ((n2w n) : 'a word)))
Proof
 rw [Eval_exp_def, WORD_def, erun_def, w2ver_def]
QED

Theorem Eval_exp_word_bit:
 !fext_rel rel s s' n (w:'a word) varexp.
  Eval_exp fext_rel rel fext s s' env (WORD w) varexp ⇒
  is_vervar varexp ∧ n < dimindex (:'a) ⇒
  Eval_exp fext_rel rel fext s s' env (BOOL (word_bit n w)) (ArrayIndex varexp 0 (Const (n2ver n)))
Proof
 rw [is_vervar_cases, Eval_exp_def, erun_def, WORD_def] \\ drule_first \\
 fs [erun_get_var_def, sum_bind_def, sum_mapM_def, erun_def, sum_map_def, ver2n_n2ver, w2ver_def,
     get_array_index_def, sum_revEL_def] \\
 Cases_on_v2w `w` \\
 fs [w2v_v2w, BOOL_def, sum_bind_def, sum_map_def, EL_MAP, bit_v2w, testbit, sum_EL_EL]
QED

(** Statements **)

Definition Eval_def:
 Eval fext_rel rel fext s s' env snew vp ⇔
  ∀fextv ver_s.
   rel s s' (ver_s with vars := env) ∧ fext_rel fextv fext ⇒
   ∃ver_s'. prun fextv (ver_s with vars := env) vp = INR ver_s' ∧ rel s snew ver_s'
End

Theorem update_step_lem:
 !exp p fextv ver_s ver_s'.
  (!var. MEM var (evreads exp) ==> ~MEM var (vwrites p)) /\
  prun fextv ver_s p = INR ver_s' ==>
  erun fextv ver_s' exp = erun fextv ver_s exp
Proof
 rpt strip_tac \\ match_mp_tac erun_cong \\ metis_tac [prun_same_after]
QED

Theorem get_cvar_rel_set_var_neq:
 ∀var var' s v.
 var ≠ var' ⇒ get_cvar_rel (set_var s var v) var' = get_cvar_rel s var'
Proof
 rw [get_cvar_rel_def, set_var_def, alistTheory.ALOOKUP_APPEND]
QED

Theorem get_cvar_rel_set_nbq_var:
 ∀var var' s v.
 get_cvar_rel (set_nbq_var s var v) var' = if var = var' then INR v else get_cvar_rel s var'
Proof
 rw [get_cvar_rel_def, set_nbq_var_def]
QED

Theorem Eval_Skip:
 !fext_rel rel s s'. Eval fext_rel rel fext s s' env s' Skip
Proof
 rw [Eval_def, prun_def]
QED

Theorem Eval_Seq_Skip:
 (∀fext_rel rel fext s s' env snew p. Eval fext_rel rel fext s s' env snew (Seq Skip p) =
                                      Eval fext_rel rel fext s s' env snew p) ∧
 (∀fext_rel rel fext s s' env snew p. Eval fext_rel rel fext s s' env snew (Seq p Skip) =
                                      Eval fext_rel rel fext s s' env snew p)
Proof
 rw [Eval_def, prun_def, sum_bind_def]
QED

Theorem Eval_IfElse:
 !fext_rel rel s s' C Cexp L Lvprog R Rvprog.
  Eval_exp fext_rel rel fext s s' env (BOOL C) Cexp /\
  Eval fext_rel rel fext s s' env L Lvprog /\
  Eval fext_rel rel fext s s' env R Rvprog ==>
  Eval fext_rel rel fext s s' env (if C then L else R) (IfElse Cexp Lvprog Rvprog)
Proof
 rewrite_tac [Eval_def, Eval_exp_def, prun_def] \\ rpt strip_tac \\ rpt drule_first \\
 fs [sum_bind_def, BOOL_def, get_VBool_data_def] \\ rw []
QED

Triviality pstate_vars_cleanup:
 !(s:pstate). (s with vars := s.vars) = s
Proof
 rw [pstate_component_equality]
QED

Theorem Eval_Eval:
 !fext_rel rel s s' f fv g gv.
 Eval fext_rel rel fext s s' env f fv ∧
 (∀s s' env. Eval fext_rel rel fext s s' env ((λs'. g s s') s') gv) ⇒
 Eval fext_rel rel fext s s' env (let s' = f in g s s') (Seq fv gv)
Proof
 rw [Eval_def, prun_def, sum_bind_INR] \\ last_x_assum drule \\ rpt (disch_then drule) \\ strip_tac \\ simp [] \\
 metis_tac [pstate_vars_cleanup]
QED

Theorem revLUPDATE_fcp_update:
 !(w : 'a word) i b. i < dimindex(:'a) ==> revLUPDATE b i (w2v w) = w2v ((i :+ b) w)
Proof
 rw [w2v_def, revLUPDATE_def, LUPDATE_GENLIST, GENLIST_FUN_EQ] \\
 rewrite_tac [fcpTheory.FCP_APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_THM] \\ simp [] \\
 qmatch_goalsub_abbrev_tac ‘COND c1 _ _ = _’ \\ qmatch_goalsub_abbrev_tac ‘_ = COND c2 _ _’ \\
 qsuff_tac ‘c1 = c2’ >- simp [] \\ unabbrev_all_tac \\ decide_tac
QED

(* Case handling *)

(* Note: Works for any program q rather than just ARB, but we only ever need ARB *)
Theorem Eval_Case_ARB:
 !fext_rel rel s s' x_max (x:'a word) xv p pv.
 Eval fext_rel rel fext s s' env p pv ⇒
 x_max = UINT_MAXw ⇒
 Eval_exp fext_rel rel fext s s' env (WORD x) xv ⇒
 x_max <=+ x ⇒
 Eval fext_rel rel fext s s' env (if x = x_max then p else ARB) (Case VBool_t xv [(Const (w2ver x_max), pv)] NONE)
Proof
 rpt strip_tac \\ rveq \\ TOP_CASE_TAC
 >- (fs [Eval_def, Eval_exp_def, prun_def, erun_def, WORD_def] \\ rpt strip_tac \\ res_tac \\
     simp [sum_bind_def])
 \\ (qspec_then `x` assume_tac WORD_LS_T \\ fs [WORD_LS] \\
    `w2n x = w2n (-1w:'a word)` by DECIDE_TAC \\ fs [])
QED

Triviality word_lo_word_ls_plus1:
 !x y. x <+ y ==> x + 1w <=+ y
Proof
 rpt strip_tac \\ qspec_then `x` mp_tac w2n_plus1 \\ TOP_CASE_TAC \\ WORD_DECIDE_TAC
QED

(* Accumulate thm for _Case_ARB *)
Theorem Eval_Case_ARB_new_case:
 !fext_rel rel s s' xbound_new xbound (x:'a word) xv p pv q cs defl ty.
 (xbound <=+ x ==> Eval fext_rel rel fext s s' env q (Case ty xv cs defl)) /\
 Eval fext_rel rel fext s s' env p pv ⇒
 (xbound = xbound_new + 1w) ⇒
 Eval_exp fext_rel rel fext s s' env (WORD x) xv ⇒
 (xbound_new <=+ x ==>
 Eval fext_rel rel fext s s' env (if x = xbound_new then p else q)
                                 (Case ty xv ((Const (w2ver xbound_new), pv)::cs) defl))
Proof
 rw [Eval_def, Eval_exp_def, WORD_def, prun_def, erun_def] \\ res_tac \\
 simp [sum_bind_def, w2ver_bij] \\
 `xbound_new <+ x` by WORD_DECIDE_TAC \\
 fs [word_lo_word_ls_plus1]
QED

Theorem word_ls_0:
 !x. 0w <=+ x
Proof
 WORD_DECIDE_TAC
QED

Theorem Eval_Case_catch_all_new_case:
 !fext_rel rel s s' xval x xv p pv q qv cs defl ty.
 Eval fext_rel rel fext s s' env q (Case ty xv cs defl) /\
 Eval fext_rel rel fext s s' env p pv ⇒
 Eval_exp fext_rel rel fext s s' env (WORD x) xv ⇒
 Eval fext_rel rel fext s s' env (if x = xval then p else q)
                  (Case ty xv ((Const (w2ver xval), pv)::cs) defl)
Proof
 rw [Eval_def, Eval_exp_def, erun_def, prun_def] \\ rpt drule_first \\ fs [sum_bind_def, WORD_def, w2ver_bij]
QED

Triviality Eval_Case_catch_all_help:
 !fext_rel rel s s' xval x xv p pv ty.
 Eval_exp fext_rel rel fext s s' env (WORD x) xv /\
 Eval fext_rel rel fext s s' env p pv ==>
 Eval fext_rel rel fext s s' env p (Case ty xv [] (SOME pv))
Proof
 rw [Eval_def, prun_def]
QED

Theorem Eval_Case_catch_all:
 !fext_rel rel s s' xval x xv p pv q qv.
 Eval fext_rel rel fext s s' env p pv /\
 Eval fext_rel rel fext s s' env q qv ==>
 Eval_exp fext_rel rel fext s s' env (WORD x) xv ⇒
 Eval fext_rel rel fext s s' env (if x = xval then p else q)
                                 (Case VBool_t xv [(Const (w2ver xval), pv)] (SOME qv))
Proof
 metis_tac [Eval_Case_catch_all_help, Eval_Case_catch_all_new_case]
QED

(** Processes **)

Definition Eval_list_def:
 Eval_list fext_rel rel fext s s' env snew vps ⇔
  ∀fextv ver_s.
   rel s s' (ver_s with vars := env) ∧ fext_rel fextv fext ⇒
   ∃ver_s'. sum_foldM (prun fextv) (ver_s with vars := env) vps = INR ver_s' ∧
            rel s snew ver_s'
End

Theorem Eval_list_nil:
 ∀fext_rel rel s s' env. Eval_list fext_rel rel fext s s' env (procs [] fext s s') []
Proof
 rw [Eval_list_def, sum_foldM_def, procs_def]
QED

Theorem Eval_Eval_list_base:
 (∀s s' env. Eval fext_rel rel fext s s' env (step fext s s') vstep) ⇒
 (∀s s' env. Eval_list fext_rel rel fext s s' env (procs [step] fext s s') [vstep])
Proof
 rw [Eval_def, Eval_list_def, sum_foldM_def, procs_def]
QED

Theorem Eval_Eval_list_step:
 (∀s s' env. Eval fext_rel rel fext s s' env (step1 fext s s') vstep) ∧
 (∀s s' env. Eval_list fext_rel rel fext s s' env (procs steps fext s s') vsteps) ⇒
 (∀s s' env. Eval_list fext_rel rel fext s s' env (procs (step1::steps) fext s s') (vstep :: vsteps))
Proof
 rw [Eval_def, Eval_list_def, sum_foldM_def, procs_def] \\ drule_last \\ simp [sum_bind_def] \\
 metis_tac [pstate_vars_cleanup]
QED

(*Triviality rel_with_env:
 ∀rel s s' ver_s. rel s s' ver_s ⇒ rel s s' (ver_s with vars := ver_s.vars)
Proof
 simp [pstate_vars_cleanup]
QED*)

Theorem Eval_lists_mrun:
 ∀n vs vfext fext fbits.
 (∀fext s s' env. Eval_list fext_rel rel fext s s' env (procs steps_ffs fext s s') vsteps_ffs) ∧
 (∀fext s s' env. Eval_list fext_rel rel fext s s' env (procs steps_combs fext s s') vsteps_combs) ∧

 (∀s env fbits. module_rel s env ⇒ rel s s <|vars := env; nbq := []; fbits := fbits|>) ∧
 (∀hol_s ver_s step. rel hol_s (step hol_s) ver_s ⇒ module_rel (step hol_s) (ver_s.nbq ++ ver_s.vars)) ⇒

 EVERY (λp. vnwrites p = []) vsteps_combs ⇒
 
 module_rel s vs ⇒
 fext_rel_n fext_rel vfext fext ⇒
 ∃vs' fbits'. mrun vfext fbits vsteps_ffs vsteps_combs vs n = INR (vs', fbits') ∧
              module_rel (mk_circuit (procs steps_ffs) (procs steps_combs) s fext n) vs'
Proof
 Induct \\ simp [mrun_def, mk_circuit_def]
 >- (rw [mstep_combs_def, Eval_list_def, fext_rel_n_def] \\
     first_x_assum (qspec_then ‘0’ assume_tac) \\
     drule_first \\ first_x_assum (qspec_then ‘fbits’ assume_tac) \\
     drule_first \\
     drule_first \\
     drule_strip EVERY_vnwrites_nil_correct \\
     fs [sum_bind_def]) \\
 
 rpt strip_tac \\
 drule_last \\ first_x_assum (qspec_then ‘fbits’ strip_assume_tac) \\
 fs [sum_bind_def, Eval_list_def] \\

 qpat_assum ‘fext_rel_n _ _ _’ (qspec_then ‘n’ assume_tac o REWRITE_RULE [fext_rel_n_def]) \\
 first_assum drule \\ disch_then (qspec_then ‘fbits'’ assume_tac) \\
 drule_last \\ simp [mstep_ffs_def, sum_bind_def] \\

 qpat_x_assum ‘fext_rel_n _ _ _’ (qspec_then ‘SUC n’ assume_tac o REWRITE_RULE [fext_rel_n_def]) \\
 first_assum drule \\ strip_tac \\
 qpat_x_assum ‘∀s env fbits. module_rel _ _ ⇒ _’ drule_strip \\
 first_x_assum (qspec_then ‘ver_s'.fbits’ assume_tac) \\
 drule_last \\ simp [mstep_combs_def, sum_bind_def] \\
 
 drule_first \\ drule_strip EVERY_vnwrites_nil_correct \\ fs []
QED

Theorem module_state_rel_var_state_rel_var:
 module_state_rel_var s env var P facc ⇒
 state_rel_var s <|vars := env; nbq := []; fbits := fbits|> var P facc
Proof
 rw [module_state_rel_var_def, state_rel_var_def] \\ simp [get_var_def, get_nbq_var_def]
QED

Theorem module_state_rel_var_state_rel_cvar:
 module_state_rel_var s env var P facc ⇒
 state_rel_cvar s s <|vars := env; nbq := []; fbits := fbits|> var P facc
Proof
 rw [module_state_rel_var_def, state_rel_cvar_def] \\ simp [get_var_def, get_cvar_rel_def]
QED

Theorem state_rel_var_module_state_rel_var:
 state_rel_var (step hol_s) ver_s var P facc ⇒
 module_state_rel_var (step hol_s) (ver_s.nbq ++ ver_s.vars) var P facc
Proof
 simp [state_rel_var_def, get_var_def, get_nbq_var_def,
       module_state_rel_var_def, ALOOKUP_APPEND, CaseEq"option"]
QED

Theorem state_rel_cvar_module_state_rel_var:
 state_rel_cvar hol_s (step hol_s) ver_s var P facc ⇒
 module_state_rel_var (step hol_s) (ver_s.nbq ++ ver_s.vars) var P facc
Proof
 simp [state_rel_cvar_def, get_var_def, get_cvar_rel_def,
       module_state_rel_var_def, ALOOKUP_APPEND, CaseEq"option"]
QED

(** Modules **)

Theorem mk_circuit_to_mk_module:
 ∀m.
 (∀n fbits' fbits.
   ∃vs' fbits''. mrun vfext fbits' seqs_v combs_v (SND (run_decls fbits decls [])) n = INR (vs', fbits'') ∧
                 module_rel (mk_circuit seqs combs (init fbits) fext n) vs') ⇒

 m.decls = decls ∧ m.ffs = seqs_v ∧ m.combs = combs_v ⇒
                                
 ∃vs' fbits'. run vfext fbits m n = INR (vs',fbits') ∧
              module_rel (mk_module seqs combs init fext fbits n) vs'
Proof
 rw [run_def] \\ pairarg_tac \\ simp [] \\
 first_x_assum (qspecl_then [‘n’, ‘fbits'’, ‘fbits’] strip_assume_tac) \\
 gs [mk_module_def]
QED

val _ = export_theory ();
