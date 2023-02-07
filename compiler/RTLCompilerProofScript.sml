open hardwarePreamble;

open ASCIInumbersTheory alistTheory wordsTheory stringTheory bitstringTheory sptreeTheory
     balanced_mapTheory;
open dep_rewrite wordsLib;

open sumExtraTheory oracleTheory verilogTheory verilogTypeTheory verilogMetaTheory;
open balanced_mapExtraTheory RTLTheory RTLTypeTheory RTLPropsTheory PreCompilerTheory RTLCompilerTheory;

open RTLLib;

val _ = new_theory "RTLCompilerProof";

infix THEN2;

val _ = type_abbrev ("extenvt", “:(string, vertype) alist”);

(** Phase 1 **)

(* Some lemmas, move later *)

Theorem LENGTH_cset_net:
 !bs k v. LENGTH (cset_net bs k v) = LENGTH bs
Proof
 Cases_on `bs` \\ simp [cset_net_def]
QED

Theorem TL_cset_net:
 !bs k v. TL (cset_net bs k v) = TL bs
Proof
 Cases_on `bs` \\ simp [cset_net_def]
QED

Theorem EVERY_invariant_cset_net:
 !env k v. EVERY (invariant string_cmp) env ==> EVERY (invariant string_cmp) (cset_net env k v)
Proof
 Cases \\ rw [cset_net_def, insert_thm, singleton_thm]
QED

Theorem cset_net_nil:
 !env k v. cset_net env k v = [] <=> env = []
Proof
 Cases \\ rw [cset_net_def]
QED

Theorem cget_net_var_singleton:
 !t var. cget_net_var [t] var = lookup string_cmp var t
Proof
 rw [cget_net_var_def] \\ CASE_TAC
QED

Theorem cget_net_cons_NONE:
 !b bs var. cget_net_var [b] var = NONE ==> cget_net (b::bs) var = cget_net bs var
Proof
 simp [cget_net_var_singleton] \\ rw [cget_net_def, cget_net_var_def]
QED

Theorem cget_net_cons_SOME:
 !b bs var inp. cget_net_var [b] var = SOME inp ==> cget_net (b::bs) var = inp
Proof
 simp [cget_net_var_singleton] \\ rw [cget_net_def, cget_net_var_def]
QED

Theorem cget_net_var_cons_SOME:
 !b bs var inp. cget_net_var [b] var = SOME inp ==> cget_net_var (b::bs) var = SOME inp
Proof
 simp [cget_net_var_singleton] \\ simp [cget_net_var_def]
QED

Theorem cget_net_var_SOME_cget_net:
 !env var inp. cget_net_var env var = SOME inp ==> cget_net env var = inp
Proof
 rw [cget_net_def]
QED

Theorem cget_net_var_SOME_cget_net_cons:
 !b bs var inp. cget_net_var [b] var = SOME inp ==> cget_net (b::bs) var = inp
Proof
 rw [cget_net_def, cget_net_var_singleton] \\ rw [cget_net_var_def]
QED

Theorem cget_net_var_NONE_cget_net_cons:
 !b bs var. cget_net_var [b] var = NONE ==> cget_net (b::bs) var = cget_net bs var
Proof
 rw [cget_net_def, cget_net_var_singleton] \\ rw [cget_net_var_def]
QED

Theorem cget_net_var_NONE_cget_net:
 !si var. cget_net_var si var = NONE ==> cget_net si var = VarInp (RegVar var 0) NoIndexing
Proof
 rw [cget_net_def]
QED

Theorem cget_net_VarInp_NetVar:
 !si var n idx. cget_net si var = VarInp (NetVar n) idx ==> cget_net_var si var = SOME (VarInp (NetVar n) idx)
Proof
 rw [cget_net_def] \\ every_case_tac \\ fs []
QED

Theorem cget_net_var_cget_net:
 !var env env'.
 cget_net_var env' var = cget_net_var env var ==> cget_net env' var = cget_net env var
Proof
 rw [cget_net_def]
QED

Theorem cget_net_var_cons_empty:
 !env var. cget_net_var (empty::env) var = cget_net_var env var
Proof
 rw [cget_net_var_def, empty_def, lookup_def]
QED

Theorem cget_net_cons_empty:
 !env var. cget_net (empty::env) var = cget_net env var
Proof
 rw [cget_net_def, cget_net_var_cons_empty]
QED

Theorem cget_net_var_alt:
 (!name. cget_net_var [] name = NONE) /\
 (!b bs name. cget_net_var (b::bs) name = case cget_net_var [b] name of
                                            NONE => cget_net_var bs name
                                          | SOME v => SOME v)
Proof
 conj_tac \\ rw [cget_net_var_def] \\ TOP_CASE_TAC
QED

Theorem cget_net_var_append:
 !si1 si2 var. cget_net_var (si1 ++ si2) var = case cget_net_var si1 var of
                                                 SOME v => SOME v
                                               | NONE => cget_net_var si2 var
Proof
 Induct \\ rw [cget_net_var_def] \\ every_case_tac \\ fs []
QED

Theorem cget_net_append:
 !si1 si2 var. cget_net (si1 ++ si2) var = case cget_net_var si1 var of
                                             SOME v => v
                                           | NONE => cget_net si2 var
Proof
 rw [cget_net_def, cget_net_var_append] \\ every_case_tac
QED

(** Invariants and other definitions needed to state and prove various correctness thms **)

(* Value-level definitions *)

val same_value_def = Define `
 (same_value (VBool b1) (CBool b2) <=> b1 = b2) /\
 (same_value (VArray l1) (CArray l2) <=> l1 = l2) /\
 (same_value _ _ = F)`;

val same_state_def = Define `
 same_state venv cenv =
  !var vv. sum_alookup venv var = INR vv ==>
   ?cv. cget_var cenv (RegVar var 0) = INR cv /\ same_value vv cv`;

val sum_same_value_def = Define `
 (sum_same_value (INR v1) (INR v2) <=> same_value v1 v2) /\
 (sum_same_value (INL e1) (INL e2) <=> e1 = e2) /\
 (sum_same_value _ _ <=> F)`;

val same_fext_n_def = Define `
 same_fext_n vfext rtlfext <=> !var. sum_same_value (vfext var) (rtlfext var)`;

Theorem same_fext_n_ver_INR:
 !fextv fext var v.
 same_fext_n fextv fext /\ fextv var = INR v ==> ?v'. fext var = INR v' /\ same_value v v'
Proof
 rw [same_fext_n_def] \\ first_x_assum (qspec_then ‘var’ mp_tac) \\
 Cases_on ‘fext var’ \\ simp [sum_same_value_def]
QED
 
val same_fext_def = Define `
 same_fext vfext rtlfext <=> !n var. sum_same_value (vfext n var) (rtlfext n var)`;

Theorem same_fext_same_fext_n:
 !vfext rtlfext. same_fext vfext rtlfext ⇔ (∀n. same_fext_n (vfext n) (rtlfext n))
Proof
 rw [same_fext_def, same_fext_n_def]
QED

(* Properties *)

Theorem same_value_cases:
 (!v b. same_value (VBool b) v <=> v = CBool b) /\ (!v b. same_value v (CBool b) <=> v = VBool b) /\
 (!v bs. same_value (VArray bs) v <=> v = CArray bs) /\
 (!v bs. same_value v (CArray bs) <=> v = VArray bs)
Proof
 rpt conj_tac \\ Cases \\ rw [same_value_def] \\ metis_tac []
QED

(* Less-than definitions *)

val si_lt_def = Define `
 si_lt si n <=> !var inp. cget_net_var si var = SOME inp ==> cell_input_lt inp n`;

Triviality OPTION_ALL_alt:
 ∀P x. OPTION_ALL P x ⇔ (∀x'. x = SOME x' ⇒ P x')
Proof
 gen_tac \\ Cases \\ simp []
QED

Theorem si_lt_alt:
 ∀si n. si_lt si n ⇔ ∀var. OPTION_ALL (λinp. cell_input_lt inp n) (cget_net_var si var)
Proof
 simp [si_lt_def, OPTION_ALL_alt]
QED

(* Properties *)

Theorem si_lt_empty:
 !n. si_lt [empty] n
Proof
 rw [si_lt_def, cget_net_var_empty]
QED

Theorem si_lt_cons_empty:
 !si n. si_lt si n ==> si_lt (empty::si) n
Proof
 rw [si_lt_def, cget_net_var_cons_empty]
QED

Theorem si_lt_append:
 !si1 si2 n. si_lt si1 n /\ si_lt si2 n ==> si_lt (si1 ++ si2) n
Proof
 rw [si_lt_def, cget_net_var_append] \\ every_case_tac \\ drule_first \\ fs [] \\ rw []
QED

Theorem si_lt_le:
 !si n m. si_lt si n /\ n <= m ==> si_lt si m
Proof
 rw [si_lt_def] \\ metis_tac [cell_input_lt_le]
QED

(* Specialization of si_lt_le, sometimes useful *)
Theorem si_lt_SUC:
 !si n. si_lt si n ==> si_lt si (SUC n)
Proof
 rpt strip_tac \\ match_mp_tac si_lt_le \\ asm_exists_tac \\ simp []
QED

Theorem cell_input_lt_neq_VarInp:
 !inp min n idx.
  cell_input_lt inp min /\ min <= n ==>
  inp <> VarInp (NetVar n) idx
Proof
 Cases \\ rw [cell_input_lt_def] \\ Cases_on `n` \\ fs [var_lt_def]
QED

Theorem si_lt_not_eq_border_NetVar:
 !si n var idx. si_lt si n ==> cget_net si var <> VarInp (NetVar n) idx
Proof
 rw [si_lt_def, cget_net_def] \\ CASE_TAC \\ drule_first \\
 match_mp_tac cell_input_lt_neq_VarInp \\ asm_exists_tac \\ simp []
QED

(* Compiler internals *)

val si_wf_def = Define `
 si_wf si <=> LENGTH si <> 0 /\ EVERY (invariant string_cmp) si`;

(* Same state w.r.t. bsi and nbsi *)
val same_state_bsi_def = Define `
 same_state_bsi fext venv cenv si <=>
  (!var vv. sum_alookup venv var = INR vv ==> ?cv. cell_inp_run fext cenv (cget_net si var) = INR cv /\
                                                   same_value vv cv)`;

val same_state_nbsi_def = Define `
 same_state_nbsi fext nbq cenv si <=>
  (!var vv. sum_alookup nbq var = INR vv ==>
            ?cv. cell_inp_run fext cenv (cget_net si var) = INR cv /\ same_value vv cv) /\
  (!var err. sum_alookup nbq var = INL err ==>
             cell_inp_run fext cenv (cget_net si var) = cell_inp_run fext cenv (VarInp (RegVar var 0) NoIndexing))`;

val writes_ok_sis_def = Define `
 writes_ok_sis ps cs <=>
  (!var inp. cget_net_var cs.bsi var = SOME inp ==> MEM var (FLAT (MAP vwrites ps))) /\
  (!var inp. cget_net_var cs.nbsi var = SOME inp ==> MEM var (FLAT (MAP vnwrites ps)))`;

(* Same state, but indirection through sis from compiler state *)
val same_state_sis_def = Define `
 same_state_sis fext vs cs cenv <=>
  same_state_bsi fext vs.vars cenv cs.bsi /\
  same_state_nbsi fext vs.nbq cenv cs.nbsi`;

(* Properties *)

Theorem si_wf_empty:
 si_wf [empty]
Proof
 EVAL_TAC
QED

Theorem HD_cset_net:
 ∀si k v. si_wf si ⇒ [HD (cset_net si k v)] = cset_net [HD si] k v
Proof
 Cases \\ rw [si_wf_def, cset_net_def]
QED

Theorem si_wf_cset_net:
 !si k inp. si_wf si ==> si_wf (cset_net si k inp)
Proof
 Cases \\ rw [si_wf_def, cset_net_def, insert_thm]
QED

Theorem si_wf_cons_empty:
 !si. si_wf si ==> si_wf (empty :: si)
Proof
 rw [si_wf_def, invariant_def, empty_def]
QED

Theorem si_wf_cons_hd:
 !b bs. si_wf (b::bs) ==> si_wf [b]
Proof
 rw [si_wf_def]
QED

(* Variant of si_wf_cons_hd *)
Theorem si_wf_HD:
 ∀si. si_wf si ⇒ si_wf [HD si]
Proof
 Cases \\ rw [si_wf_def]
QED

Theorem cget_net_var_cset_net:
 !si k1 k2 v. si_wf si ==> cget_net_var (cset_net si k1 v) k2 = if k1 = k2 then SOME v else cget_net_var si k2
Proof
 Cases \\ rw [si_wf_def, cset_net_def, cget_net_var_def, lookup_insert]
QED

Theorem cget_net_cset_net:
 !si k1 k2 v. si_wf si ==> cget_net (cset_net si k1 v) k2 = if k1 = k2 then v else cget_net si k2
Proof
 rw [cget_net_def, cget_net_var_cset_net]
QED

Theorem si_lt_cset_net:
 !si n inp s. si_wf si /\ si_lt si n /\ cell_input_lt inp n ==> si_lt (cset_net si s inp) n
Proof
 rw [si_lt_def, cget_net_var_cset_net] \\ every_case_tac \\ metis_tac []
QED

Theorem si_lt_cset_net_SUC:
 !si n m inp s idx. si_wf si /\ si_lt si n ==> si_lt (cset_net si s (VarInp (NetVar n) idx)) (SUC n)
Proof
 rw [si_lt_def, cget_net_var_cset_net] \\ every_case_tac
 >- rw [cell_input_lt_def, var_lt_def]
 \\ drule_first \\ match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp []
QED

(*Theorem same_state_si_cget_net_var:
 !var vs cenv si si'.
 same_state_si vs cenv si /\
 (!var. cget_net_var si' var = cget_net_var si var) ==>
 same_state_si vs cenv si
Proof
 rw [same_state_si_def, cget_net_var_cget_net]
QED*)

Theorem cell_inp_run_cset_var_cget_net_var:
 !si n m v cenv var inp fext.
 si_lt si n /\ cget_net_var si var = SOME inp ∧ n ≤ m ==>
 cell_inp_run fext (cset_var cenv (NetVar m) v) inp = cell_inp_run fext cenv inp
Proof
 rw [si_lt_def] \\ drule_first \\
 Cases_on `inp` \\ fs [cell_input_lt_def, cell_inp_run_def, cget_var_cset_var] \\
 Cases_on `v'` \\ fs [var_lt_def]
QED

Theorem cell_inp_run_cset_var_cget_net:
 !si n m v cenv var fext.
 si_lt si n ∧ n ≤ m ==>
 cell_inp_run fext (cset_var cenv (NetVar m) v) (cget_net si var) = cell_inp_run fext cenv (cget_net si var)
Proof
 rw [cget_net_def] \\ CASE_TAC
 >- simp [cell_inp_run_cset_var]
 \\ metis_tac [cell_inp_run_cset_var_cget_net_var]
QED

Theorem cell_inp_run_cset_var_cget_net_spec:
 !si n v cenv var fext.
 si_lt si n ==>
 cell_inp_run fext (cset_var cenv (NetVar n) v) (cget_net si var) = cell_inp_run fext cenv (cget_net si var)
Proof
 metis_tac [cell_inp_run_cset_var_cget_net, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem same_state_bsi_cset_var_si_lt:
 !si n vs cenv si v fext.
 si_lt si n /\ same_state_bsi fext vs cenv si ==> same_state_bsi fext vs (cset_var cenv (NetVar n) v) si
Proof
 rw [same_state_bsi_def] \\ metis_tac [cell_inp_run_cset_var_cget_net, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem same_state_nbsi_cset_var_si_lt:
 !si n vs cenv si v fext.
 si_lt si n /\ same_state_nbsi fext vs cenv si ==> same_state_nbsi fext vs (cset_var cenv (NetVar n) v) si
Proof
 rw [same_state_nbsi_def] \\ drule_first \\ simp [cell_inp_run_cset_var] \\
 metis_tac [cell_inp_run_cset_var_cget_net, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem same_state_bsi_set_var:
 !vv vs var si inp cv cenv fext.
  same_state_bsi fext vs.vars cenv si /\ cell_inp_run fext cenv inp = INR cv /\ same_value vv cv /\ si_wf si ==>
  same_state_bsi fext (set_var vs var vv).vars cenv (cset_net si var inp)
Proof
 rw [same_state_bsi_def, cget_net_cset_net, cget_net_var_cset_net, sum_alookup_cleanup] \\
 every_case_tac \\ fs []
QED

Theorem same_state_nbsi_set_nbq_var:
 !vv vs var si inp cv cenv ps fext.
  same_state_nbsi fext vs.nbq cenv si /\ cell_inp_run fext cenv inp = INR cv /\ same_value vv cv /\ si_wf si ==>
  same_state_nbsi fext (set_nbq_var vs var vv).nbq cenv (cset_net si var inp)
Proof
 rw [same_state_nbsi_def, cget_net_cset_net, cget_net_var_cset_net, sum_alookup_cleanup] \\ 
 every_case_tac \\ fs []
QED

Theorem same_state_bsi_same_si:
 !si si' vars cenv fext.
 (!var. cget_net_var si' var = cget_net_var si var) /\
 same_state_bsi fext vars cenv si ==>
 same_state_bsi fext vars cenv si'
Proof
 rw [same_state_bsi_def] \\ metis_tac [cget_net_var_cget_net]
QED

Theorem same_state_nbsi_same_si:
 !si si' nbq cenv fext.
 (!var. cget_net_var si' var = cget_net_var si var) /\
 same_state_nbsi fext nbq cenv si ==>
 same_state_nbsi fext nbq cenv si'
Proof
 rw [same_state_nbsi_def] \\ metis_tac [cget_net_var_cget_net]
QED

Theorem same_state_sis_same_sis:
 !vs s s' cenv fext.
 (!var. cget_net_var s'.bsi var = cget_net_var s.bsi var) /\
 (!var. cget_net_var s'.nbsi var = cget_net_var s.nbsi var) /\
 same_state_sis fext vs s cenv ==>
 same_state_sis fext vs s' cenv
Proof
 rw [same_state_sis_def] \\ metis_tac [same_state_bsi_same_si, same_state_nbsi_same_si]
QED

Theorem same_state_sis_equal_sis:
 !vs s s' cenv fext.
 s'.bsi = s.bsi /\ s'.nbsi = s.nbsi /\
 same_state_sis fext vs s cenv ==>
 same_state_sis fext vs s' cenv
Proof
 rw [same_state_sis_def]
QED

(* Definitions mentioning types *)

val same_type_def = Define `
 (same_type VBool_t CBool_t <=> T) /\
 (same_type (VArray_t i) (CArray_t j) <=> i = j) /\
 (same_type _ _ <=> F)`;

val si_sound_def = Define `
 si_sound fext (EE : extenvt) E cenv si <=>
  !var inp. cget_net_var si var = SOME inp ==>
            (?cv t t'. cell_inp_run fext cenv inp = INR cv /\
                       E var = SOME t /\ same_type t t' /\ rtltype_v cv t') /\
            cell_input_covered_by_extenv EE inp`;

val si_complete_def = Define `
 si_complete fext E cenv si =
  !var t. E var = SOME t ==> ?cv t'. cell_inp_run fext cenv (cget_net si var) = INR cv /\
                                     same_type t t' /\ rtltype_v cv t'`;

Definition cstate_vertypes_sound_def:
 cstate_vertypes_sound E vertypes <=> !var t. decls_type vertypes var = INR t ==> E var = SOME t
End

val cstate_ok_def = Define `
 cstate_ok fext EE E cs cenv <=>
  si_wf cs.bsi /\ si_lt cs.bsi cs.tmpnum /\ si_sound fext EE E cenv cs.bsi /\ si_complete fext E cenv cs.bsi /\
  si_wf cs.nbsi /\ si_lt cs.nbsi cs.tmpnum /\ si_sound fext EE E cenv cs.nbsi /\ si_complete fext E cenv cs.nbsi /\
  cstate_vertypes_sound E cs.vertypes`;

(* Properties *)

Theorem same_type_array_bool:
 !l. ~same_type (VArray_t l) CBool_t
Proof
 Induct \\ rw [same_type_def]
QED

Theorem same_type_cases:
 (!t. same_type VBool_t t <=> t = CBool_t) /\
 (!t. same_type t CBool_t <=> t = VBool_t) /\
 (!t l. same_type (VArray_t l) t <=> t = CArray_t l) /\
 (!t l. same_type t (CArray_t l) <=> t = VArray_t l)
Proof
 rpt conj_tac \\ Cases \\ rw [same_type_def, same_type_array_bool]
QED

Theorem same_type_array_deterministic:
 !l n m. same_type (VArray_t l) (CArray_t n) /\ same_type (VArray_t l) (CArray_t m) ==> n = m
Proof
 Cases \\ TRY (Cases_on `t`) \\ rw [same_type_def]
QED

Theorem same_type_deterministic:
 !t t' t''. same_type t t' /\ same_type t t'' ==> t' = t''
Proof
 rpt Cases \\ rw [same_type_def, same_type_array_bool] \\ metis_tac [same_type_array_deterministic]
QED

Theorem vertype_v_rtltype_v:
 !v cv t t'. vertype_v v t /\ same_value v cv /\ same_type t t' ==> rtltype_v cv t'
Proof
 rw [vertype_v_cases] \\ fs [same_type_cases, same_value_cases] \\ simp [rtltype_v_cases]
QED

Theorem si_sound_empty:
 !fext EE E cenv. si_sound fext EE E cenv [empty]
Proof
 rw [si_sound_def, cget_net_var_def, empty_def, lookup_def]
QED

Theorem si_sound_cset_var:
 !fext EE E cenv si n m v.
 si_sound fext EE E cenv si /\ si_lt si n ∧ n ≤ m ==>
 si_sound fext EE E (cset_var cenv (NetVar m) v) si
Proof
 rw [si_sound_def] \\ drule_first \\ drule_strip cell_inp_run_cset_var_cget_net_var \\
 simp [] \\ asm_exists_tac \\ simp []
QED

Theorem si_sound_cset_var_spec:
 !fext EE E cenv si n var v t.
 si_sound fext EE E cenv si /\ si_lt si n ==>
 si_sound fext EE E (cset_var cenv (NetVar n) v) si
Proof
 metis_tac [si_sound_cset_var, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem si_sound_cset_net:
 !cenv si var EE E inp cv t t' fext.
 si_sound fext EE E cenv si /\ E var = SOME t /\
 cell_inp_run fext cenv inp = INR cv /\ rtltype_v cv t' /\ same_type t t' /\
 cell_input_covered_by_extenv EE inp /\ si_wf si ==>
 si_sound fext EE E cenv (cset_net si var inp)
Proof
 simp [si_sound_def, cget_net_var_cset_net] \\ rpt strip_tac' \\ every_case_tac \\ fs [] \\ 
 rpt asm_exists_tac \\ drule_first
QED

Theorem si_sound_cset_var_cset_net:
 !fext EE E cenv si tmpnum var v t t'.
 si_sound fext EE E cenv si /\ si_wf si /\ si_lt si tmpnum /\ E var = SOME t /\ same_type t t' /\ rtltype_v v t' ==>
 si_sound fext EE E (cset_var cenv (NetVar tmpnum) v) (cset_net si var (VarInp (NetVar tmpnum) NoIndexing))
Proof
 rw [si_sound_def, cget_net_var_cset_net] \\ every_case_tac >- (rw [cell_inp_run_cset_var] \\ rpt asm_exists_tac) \\
 fs [si_lt_def] \\ rpt drule_first \\ Cases_on ‘inp’ \\ fs [cell_inp_run_def, cget_var_cset_var] \\
 rw [] \\ fs [cell_input_lt_def, var_lt_def, cell_input_covered_by_extenv_def] \\ rpt asm_exists_tac
QED

Theorem si_complete_cset_var:
 !fext E cenv si n m var v t.
 si_complete fext E cenv si /\ si_lt si n ∧ n ≤ m ⇒
 si_complete fext E (cset_var cenv (NetVar m) v) si
Proof
 rw [si_complete_def] \\ drule_first \\
 drule_strip cell_inp_run_cset_var_cget_net \\ simp [] \\ asm_exists_tac \\ simp []
QED

Theorem si_complete_cset_var_spec:
 !fext E cenv si n var v t.
 si_complete fext E cenv si /\ si_lt si n ⇒
 si_complete fext E (cset_var cenv (NetVar n) v) si
Proof
 metis_tac [si_complete_cset_var, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem si_complete_cset_net:
 !cenv si var E cenv inp cv t t' fext.
 si_complete fext E cenv si /\ E var = SOME t /\ same_type t t' /\
 cell_inp_run fext cenv inp = INR cv /\ rtltype_v cv t' /\
 si_wf si ==>
 si_complete fext E cenv (cset_net si var inp)
Proof
 rw [si_complete_def, cget_net_cset_net] \\ every_case_tac \\ fs [] \\ rpt asm_exists_tac
QED

Theorem si_complete_cset_var_cset_net:
 !fext E cenv si tmpnum var v t t'.
 si_complete fext E cenv si /\ si_wf si /\ si_lt si tmpnum /\
 E var = SOME t /\ same_type t t' /\ rtltype_v v t' ==>
 si_complete fext E (cset_var cenv (NetVar tmpnum) v) (cset_net si var (VarInp (NetVar tmpnum) NoIndexing))
Proof
 rw [si_complete_def, cget_net_cset_net] \\ rw [] \\ fs [cell_inp_run_cset_var] \\ rpt asm_exists_tac \\ 
 metis_tac [cell_inp_run_cset_var_cget_net, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem si_sound_cons_empty:
 !EE E cenv si fext. si_sound fext EE E cenv (empty :: si) <=> si_sound fext EE E cenv si
Proof
 rw [si_sound_def, cget_net_var_cons_empty]
QED

Theorem si_complete_cons_empty:
 !E cenv si fext. si_complete fext E cenv (empty :: si) <=> si_complete fext E cenv si
Proof
 rw [si_complete_def, cget_net_cons_empty]
QED

Theorem si_sound_append:
 !EE E cenv si1 si2 fext. si_sound fext EE E cenv si1 /\ si_sound fext EE E cenv si2 ==> si_sound fext EE E cenv (si1 ++ si2)
Proof
 rw [si_sound_def, cget_net_var_append] \\ every_case_tac \\ drule_first \\ fs [] \\ rw [] \\ rpt asm_exists_tac
QED

Theorem si_complete_append:
 !EE E cenv si1 si2 fext.
 si_sound fext EE E cenv si1 /\ si_complete fext E cenv si2 ==> si_complete fext E cenv (si1 ++ si2)
Proof
 rw [si_sound_def, si_complete_def, cget_net_append] \\ CASE_TAC >- simp [] \\
 drule_last \\ fs [] \\ metis_tac []
QED

Theorem cstate_ok_vertypes:
 !fext EE E cs cenv var t t'. cstate_ok fext EE E cs cenv /\ E var = SOME t /\ decls_type cs.vertypes var = INR t' ==> t' = t
Proof
 rw [cstate_ok_def, cstate_vertypes_sound_def] \\ drule_first \\ fs []
QED

(** Progress definitions **)

val cstate_progress_def = Define `
 cstate_progress cs cs' <=> cs.tmpnum <= cs'.tmpnum`;

Definition si_progress_def:
 si_progress si si' <=>
 LENGTH si' = LENGTH si /\
 TL si' = TL si ∧
 (∀var. IS_SOME (cget_net_var [HD si] var) ⇒ IS_SOME (cget_net_var [HD si'] var))
End

val sis_progress_def = Define `
 sis_progress cs cs' <=> si_progress cs.bsi cs'.bsi /\ si_progress cs.nbsi cs'.nbsi`;

(* Properties *)

(*Theorem si_progress_singleton:
 !si b1. si_progress [b1] si <=> ?b2. si = [b2]
Proof
 Cases \\ rw [si_progress_def]
QED*)

Theorem si_progress_cset_net:
 !si k v. si_wf si ⇒ si_progress si (cset_net si k v)
Proof
 rw [si_progress_def, LENGTH_cset_net, TL_cset_net, cget_net_var_cset_net] \\
 Cases_on ‘si’ \\ fs [si_wf_def, cget_net_var_def, cset_net_def, lookup_insert] \\ rw []
QED

Theorem cstate_progress_trans:
 !a b c. cstate_progress a b /\ cstate_progress b c ==> cstate_progress a c
Proof
 rw [cstate_progress_def]
QED

(** Some fbits thms **)

Theorem same_state_fbits:
 !venv cenv fbits. same_state venv (cenv with fbits := fbits) = same_state venv cenv
Proof
 rw [same_state_def, cget_var_fbits]
QED

Theorem si_sound_fbits:
 !fext EE E s si fbits. si_sound fext EE E (s with fbits := fbits) si = si_sound fext EE E s si
Proof
 rw [si_sound_def, cell_inp_run_fbits]
QED

Theorem si_complete_fbits:
 !fext E s si fbits. si_complete fext E (s with fbits := fbits) si = si_complete fext E s si
Proof
 rw [si_complete_def, cell_inp_run_fbits]
QED

(* Bad name? *)
Theorem nd_reset_fbits:
 !v v' s s'. nd_reset s v = (s', v') ==> ?n. s'.fbits = shift_seq n s.fbits /\
                                             verlength v = n /\ verlength v' = n
Proof
 Cases \\ simp [nd_reset_def] \\ rpt strip_tac'
 >- (fs [oracle_bit_def, shift_seq_def] \\ rw [verlength_def])
 \\ pairarg_tac \\ drule_strip oracle_bits_correct \\ fs [] \\ rw [verlength_def]
QED

Theorem nd_reset_cong:
 !v v' v'' s s' s'' fbits n.
 init_seq_eq s.fbits fbits n /\ verlength v = n /\
 nd_reset s v = (s', v') /\ nd_reset (s with fbits := fbits) v = (s'', v'') ==>
 v'' = v'
Proof
 Cases \\ simp [nd_reset_def, verlength_def] \\ rpt strip_tac' \\ rpt (pairarg_tac \\ fs []) \\ rveq
 >- (drule_strip oracle_bit_cong \\ simp [])
 \\ drule_strip oracle_bits_cong \\ simp []
QED
     
Triviality pull_exists_imp_rhs:
 ∀a b. (a ⇒ ∃n. b n) ⇔ ∃n. a ⇒ b n
Proof
 metis_tac []
QED

Theorem prun_fbits_alt:
 !fext vs p. ?n. ∀vs'.
 prun fext vs p = INR vs' ==>
  vs'.fbits = shift_seq n vs.fbits /\
  (!fbits. init_seq_eq vs.fbits fbits n ==> prun fext (vs with fbits := fbits) p = INR (vs' with fbits := shift_seq n fbits))
Proof
 recInduct prun_ind \\ rw [prun_def]
 >- (qexists_tac `0` \\ rw [pstate_component_equality, shift_seq_0])
 >- (simp [sum_bind_INR] \\
     last_x_assum (qspec_then ‘OUTR (prun fext s p0)’ strip_assume_tac) \\
     qexists_tac `n + n'` \\ rpt strip_tac' \\ drule_first \\ fs [] \\
     conj_tac >- rfs [shift_seq_add] \\ rpt strip_tac \\
     first_x_assum (qspec_then `fbits` mp_tac) \\ impl_tac >- fs [init_seq_eq_def] \\ strip_tac \\
     asm_exists_tac \\ first_x_assum (qspec_then `shift_seq n fbits` mp_tac) \\
     impl_tac >- simp [init_seq_eq_shift_seq] \\ simp [shift_seq_add])
 >- (fs [sum_bind_INR] \\ qexists_tac ‘if (OUTR (get_VBool_data (OUTR (erun fext s c)))) then n else n'’ \\
     rpt strip_tac' \\ simp [] \\ IF_CASES_TAC \\ fs [erun_fbits])
 >- (fs [sum_bind_INR] \\ 
     first_x_assum (qspecl_then [‘OUTR (erun fext s e)’, ‘OUTR (erun fext s ccond)’]
                                (strip_assume_tac o Ho_Rewrite.REWRITE_RULE [pull_exists_imp_rhs])) \\
     qexists_tac ‘if OUTR (erun fext s e) = OUTR (erun fext s ccond) then n else n'’ \\
     rpt strip_tac' \\ fs [] \\ FULL_CASE_TAC \\ gvs [erun_fbits])
 >- (qexists_tac `0` \\ simp [shift_seq_0])
 \\ (Cases_on ‘rhs’ \\ fs [prun_assn_rhs_def, sum_bind_INR, sum_map_INR, erun_fbits] \\ rveq
    >- (Cases_on ‘lhs’ \\ fs [prun_assn_lhs_prev_def, prun_bassn_def, prun_nbassn_def] \\ 
        qexists_tac ‘verlength (OUTR $ get_var s s')’ \\ rpt strip_tac' \\ pairarg_tac \\
        fs [assn_def, sum_for_INR] \\ drule_strip nd_reset_fbits \\
        simp [set_var_fbits, set_nbq_var_fbits, get_var_fbits] \\ rpt strip_tac \\
        pairarg_tac \\ drule_strip nd_reset_cong \\ drule_strip nd_reset_fbits \\ imp_res_tac nd_reset_const \\
        simp [sum_for_INR, set_var_def, set_nbq_var_def, pstate_component_equality])
    \\ qexists_tac ‘0’ \\ rpt strip_tac' \\ gvs [prun_bassn_def, prun_nbassn_def, sum_for_INR] \\
       pairarg_tac \\ gvs [assn_fbits, set_var_fbits, set_nbq_var_fbits, shift_seq_0])
QED

Theorem prun_fbits:
 !fext vs p vs'.
 prun fext vs p = INR vs' ==>
 ?n.
  vs'.fbits = shift_seq n vs.fbits /\
  (!fbits. init_seq_eq vs.fbits fbits n ==> prun fext (vs with fbits := fbits) p = INR (vs' with fbits := shift_seq n fbits))
Proof
 metis_tac [prun_fbits_alt]
QED

Theorem pruns_fbits_alt:
 ∀ps fext s. ?n. ∀s'.
 sum_foldM (prun fext) s ps = INR s' ==>
  s'.fbits = shift_seq n s.fbits /\
  (!fbits. init_seq_eq s.fbits fbits n ==>
           sum_foldM (prun fext) (s with fbits := fbits) ps = INR (s' with fbits := shift_seq n fbits))
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_INR] >- (qexists_tac `0` \\ rw [shift_seq_0]) \\
 qspecl_then [‘fext’, ‘s’, ‘h’] strip_assume_tac prun_fbits_alt \\
 last_x_assum (qspecl_then [‘fext’, ‘OUTR (prun fext s h)’] strip_assume_tac) \\
 qexists_tac `n + n'` \\ rpt strip_tac' \\ fs [shift_seq_add] \\ rpt strip_tac' \\
 last_x_assum (qspec_then `fbits` mp_tac) \\ impl_tac >- fs [init_seq_eq_def] \\ strip_tac \\ simp [] \\
 first_x_assum (qspec_then `shift_seq n fbits` mp_tac) \\ simp [init_seq_eq_shift_seq]
QED

(* was mstep_fbits *)
Theorem pruns_fbits:
 !ps fext s s'.
 sum_foldM (prun fext) s ps = INR s' ==>
 ?n.
  s'.fbits = shift_seq n s.fbits /\
  (!fbits. init_seq_eq s.fbits fbits n ==>
           sum_foldM (prun fext) (s with fbits := fbits) ps = INR (s' with fbits := shift_seq n fbits))
Proof
 metis_tac [pruns_fbits_alt]
QED

Theorem mstep_ffs_fbits_alt:
 ∀fext fbits ps s. ?n. ∀s' fbits'.
 mstep_ffs fext fbits ps s = INR (s', fbits') ==>
  fbits' = shift_seq n fbits /\
  (!fbits''. init_seq_eq fbits fbits'' n ==>
             mstep_ffs fext fbits'' ps s = INR (s', shift_seq n fbits''))
Proof
 rw [mstep_ffs_def] \\ 
 qmatch_goalsub_abbrev_tac ‘sum_foldM _ init _’ \\
 qspecl_then [‘ps’, ‘fext’, ‘init’] strip_assume_tac pruns_fbits_alt \\
 unabbrev_all_tac \\
 qexists_tac ‘n’ \\ rpt gen_tac \\ simp [sum_bind_INR] \\ strip_tac \\ drule_first \\ fs []
QED

Theorem mstep_ffs_fbits:
 ∀fext fbits ps s s' fbits'.
 mstep_ffs fext fbits ps s = INR (s', fbits') ==>
 ?n. fbits' = shift_seq n fbits /\
     (!fbits''. init_seq_eq fbits fbits'' n ==>
                mstep_ffs fext fbits'' ps s = INR (s', shift_seq n fbits''))
Proof
 metis_tac [mstep_ffs_fbits_alt]
QED

Theorem mrun_fbits:
 !n fext fbits fbits' ffs combs vs vs'.
 mrun fext fbits ffs combs vs n = INR (vs', fbits') ==>
 ?m.
  fbits' = shift_seq m fbits /\
  (!fbits''. init_seq_eq fbits fbits'' m ==> mrun fext fbits'' ffs combs vs n = INR (vs', shift_seq m fbits''))
Proof
 Induct \\ rw [mrun_def, sum_bind_INR, mstep_combs_def, mstep_ffs_def]
 >- (drule_strip pruns_fbits \\ qexists_tac `n` \\ rw [] \\ fs []) \\

 pairarg_tac \\ rveq \\ drule_first \\ gvs [sum_bind_INR] \\
 imp_res_tac pruns_fbits \\ rfs [] \\
 qmatch_asmsub_rename_tac ‘init_seq_eq fbits _ n_mrun’ \\
 qmatch_asmsub_rename_tac ‘init_seq_eq (shift_seq n_mrun fbits) _ n_ffs’ \\
 qmatch_asmsub_rename_tac ‘init_seq_eq s.fbits _ n_combs’ \\

 qexists_tac `(n_mrun + n_ffs) + n_combs` \\ simp [shift_seq_add] \\ rpt strip_tac' \\
 last_x_assum (qspec_then `fbits''` mp_tac) \\
 impl_tac >- fs [init_seq_eq_def] \\ strip_tac \\ simp [] \\

 first_x_assum (qspec_then `shift_seq n_mrun fbits''` mp_tac) \\
 impl_tac >- fs [init_seq_eq_def, shift_seq_def] \\ strip_tac \\ simp [] \\

 first_x_assum (qspec_then `shift_seq (n_mrun + n_ffs) fbits''` mp_tac) \\
 impl_tac >- fs [init_seq_eq_def, shift_seq_def] \\ strip_tac \\

 fs [sum_bind_def, shift_seq_add]
QED

(** Correctness **)

Theorem cells_run_unchanged_netlist_ok_cget_var_NetVar:
 !nl cenv cenv' (extenv : extenvt) min max n fext.
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 netlist_ok extenv min max nl /\
 n < min ==>
 cget_var cenv' (NetVar n) = cget_var cenv (NetVar n)
Proof
 Induct \\ rw [sum_foldM_def, sum_bind_INR] \\ fs [netlist_ok_def] \\ drule_first \\
 Cases_on `h` \\ cell_run_tac fs \\ rveq \\ fs [cell_ok_def, cell_output_ok_def, cget_var_cset_var] \\
 (* NDet case: *)
 rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [cget_var_cset_var] \\ fs [cget_var_fbits]
QED

Theorem cells_run_unchanged_netlist_ok: (* TODO: old name = cells_run_same_cell_input_lt *)
 !inp cenv cenv' nl (extenv : extenvt) min max n fext.
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 netlist_ok extenv min max nl /\
 cell_input_lt inp n /\
 n <= min ==>
 cell_inp_run fext cenv' inp = cell_inp_run fext cenv inp
Proof
 rpt strip_tac \\ Cases_on `inp` \\ simp [cell_inp_run_def] \\ AP_THM_TAC \\ AP_TERM_TAC \\
 Cases_on `v`
 >- (match_mp_tac cells_run_cget_var_RegVar \\ asm_exists_tac)
 \\ match_mp_tac cells_run_unchanged_netlist_ok_cget_var_NetVar \\ rpt asm_exists_tac \\ 
    fs [cell_input_lt_def, var_lt_def]
QED

Theorem cell_input_idx_cell_input_lt:
 !inp inp' i tmpnum.
 cell_input_idx inp i = INR inp' /\ cell_input_lt inp tmpnum ==> cell_input_lt inp' tmpnum
Proof
 rpt strip_tac \\ drule_strip cell_input_idx_INR \\ fs [cell_input_idx_def] \\
 rveq \\ fs [cell_input_lt_def]
QED

Theorem cell_input_slice_cell_input_lt:
 !inp inp' i1 i2 tmpnum.
 cell_input_slice inp i1 i2 = INR inp' ∧ cell_input_lt inp tmpnum ⇒ cell_input_lt inp' tmpnum
Proof
 rpt strip_tac \\ drule_strip cell_input_slice_INR \\ fs [cell_input_slice_def] \\
 rveq \\ fs [cell_input_lt_def]
QED
        
Theorem si_lt_cell_input_lt_cget_net:
 !si min var. si_lt si min ==> cell_input_lt (cget_net si var) min
Proof
 rw [cget_net_def, si_lt_def] \\ CASE_TAC \\ simp [cell_input_lt_def, var_lt_def] \\ 
 first_x_assum match_mp_tac \\ asm_exists_tac
QED

(* NOTE: can be generalized if needed (see min) *)
Theorem cells_run_unchanged_netlist_ok_cget_net_var:
 !inp var si cenv cenv' nl (extenv : extenvt) min max fext.
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 netlist_ok extenv min max nl /\
 cget_net_var si var = SOME inp ∧
 si_lt si min ==>
 cell_inp_run fext cenv' inp = cell_inp_run fext cenv inp
Proof
 rw [si_lt_def] \\ drule_first \\ drule_strip cells_run_unchanged_netlist_ok \\ simp []
QED

(* NOTE: can be generalized if needed (see min) *)
Theorem cells_run_unchanged_netlist_ok_cget_net:
 !si cenv cenv' nl (extenv : extenvt) min max fext.
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 netlist_ok extenv min max nl /\
 si_lt si min ==>
 (!var. cell_inp_run fext cenv' (cget_net si var) = cell_inp_run fext cenv (cget_net si var))
Proof
 metis_tac [cells_run_unchanged_netlist_ok, si_lt_cell_input_lt_cget_net, arithmeticTheory.LESS_EQ_REFL]
QED

(* variant of the above *)
(*Theorem cells_run_unchanged_netlist_ok_cget_net_si_sound:
 !si cenv cenv' cenv'' nl min max E.
 sum_foldM cell_run cenv nl = INR cenv' /\
 netlist_ok min max nl /\
 si_sound E cenv'' si min ==>
 (!var. cell_inp_run cenv' (cget_net si var) = cell_inp_run cenv (cget_net si var))
Proof
 metis_tac [si_sound_si_lt, cells_run_unchanged_netlist_ok_cget_net]
QED*)

(* Shows that we can remove same_state_nbsi... *)
(*Theorem same_state_nbsi_is_redundant:
 !cenv bsi nbsi n Ec vars nbq.
 (* additional: *) si_lt bsi n /\
 same_state_bsi vars cenv bsi /\ nbsi_ok Ec n nbq cenv nbsi ==>
 same_state_nbsi n vars nbq cenv bsi nbsi
Proof
 rw [same_state_bsi_def, same_state_nbsi_def, nbsi_ok_def] \\
 first_x_assum (qspec_then `bsi` assume_tac) \\
 pairarg_tac \\ fs [] \\ rpt gen_tac \\ simp [cget_var_append, cget_net_append] \\
 TOP_CASE_TAC \\ strip_tac \\ rveq
 >- (drule_first \\ TOP_CASE_TAC
    >- metis_tac [atrees_postprocess_netlist_ok, cells_run_unchanged_netlist_ok_cget_net]
    \\ drule_strip cget_var_INL \\ drule_first \\
       pop_assum (assume_tac o GSYM) \\ rfs [si_lt_def] \\ drule_first \\ fs [cget_net_def] \\
       metis_tac [atrees_postprocess_netlist_ok, cells_run_unchanged_netlist_ok, arithmeticTheory.LESS_EQ_REFL])

 \\ drule_first \\ TOP_CASE_TAC \\ fs []
QED*)

Theorem cells_run_si_sound:
 !nl cenv cenv' (extenv : extenvt) n n' m EE E si fext.
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 netlist_ok extenv n m nl /\
 si_lt si n' /\ n' <= n /\ si_sound fext EE E cenv si ==>
 si_sound fext EE E cenv' si
Proof
 simp [si_sound_def, si_lt_def] \\ rpt strip_tac \\
 rpt drule_first \\ drule_strip cells_run_unchanged_netlist_ok \\ simp [] \\ rpt asm_exists_tac
QED

(* Merge with above sound thm? *)
Theorem cells_run_si_complete:
 !nl cenv cenv' (extenv : extenvt) n n' m EE E si fext.
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 netlist_ok extenv n m nl /\
 si_lt si n' /\ n' <= n /\ si_sound fext EE E cenv si /\ si_complete fext E cenv si ==>
 si_complete fext E cenv' si
Proof
 simp [si_lt_def, si_sound_def, si_complete_def, cget_net_def] \\ rpt strip_tac' \\
 drule_first \\ CASE_TAC \\ fs []
 >- (fs [cell_inp_run_def] \\ metis_tac [cells_run_cget_var_RegVar])
 \\ rpt drule_first \\ drule_strip cells_run_unchanged_netlist_ok \\ fs [] \\ rpt asm_exists_tac
QED

(** Compile values **)

Theorem compile_value_correct:
 !v. same_value v (compile_value v)
Proof
 Cases \\ rw [same_value_def, compile_value_def]
QED

Theorem compile_value_type_correct:
 !v t. vertype_v v t ==> ?t'. rtltype_v (compile_value v) t' /\ same_type t t'
Proof
 Cases \\ rw [compile_value_def, rtltype_v_cases, vertype_v_cases, same_type_def]
QED

(** Compile types **)

Theorem same_value_rtltype_v_vertype_v:
 !v v' t. same_value v v' ⇒ rtltype_v v' (compile_type t) = vertype_v v t
Proof
 Cases \\ Cases \\ Cases \\ rw [same_value_def, vertype_v_cases, rtltype_v_cases, compile_type_def]
QED

Theorem compile_type_correct:
 !t. same_type t (compile_type t)
Proof
 Cases \\ rw [same_type_def, compile_type_def]
QED

Theorem same_type_compile_type:
 !t1 t2. same_type t1 t2 ==> t2 = compile_type t1
Proof
 Cases \\ Cases \\ rw [same_type_def, compile_type_def]
QED

Theorem rtltype_v_compile_value_compile_type:
 !v t. vertype_v v t ==> rtltype_v (compile_value v) (compile_type t)
Proof
 Cases \\ rw [vertype_v_cases, rtltype_v_cases, compile_value_def, compile_type_def]
QED

(** Compile exps **)

Theorem cell_input_idx_cell_inp_run:
 !inp inp' n fext cenv bs.
 cell_input_idx inp n = INR inp' /\
 cell_inp_run fext cenv inp = INR $ CArray bs /\
 n < LENGTH bs ==>
 cell_inp_run fext cenv inp' = INR $ CBool $ revEL n bs
Proof
 rpt strip_tac \\ drule_strip cell_input_idx_INR \\ fs [cell_input_idx_def] \\ rveq \\
 fs [cell_inp_run_def, cget_fext_var_def, sum_bind_INR] \\
 simp [sum_revEL_def, sum_EL_EL, revEL_def, sum_map_def]
QED

Theorem cell_input_slice_cell_inp_run:
 !inp inp' i1 i2 fext cenv bs.
 cell_input_slice inp i1 i2 = INR inp' /\
 cell_inp_run fext cenv inp = INR $ CArray bs /\
 i1 < LENGTH bs ∧ i2 ≤ i1 ==>
 cell_inp_run fext cenv inp' = INR $ CArray $ rev_slice bs i1 i2
Proof
 rpt strip_tac \\ drule_strip cell_input_slice_INR \\ fs [cell_input_slice_def] \\ rveq \\
 fs [cell_inp_run_def, cget_fext_var_def, sum_bind_INR, rev_slice_def]
QED

Theorem same_fext_n_same_value:
 !fextv fext var vv cv. same_fext_n fextv fext /\ fextv var = INR vv /\ fext var = INR cv ==> same_value vv cv
Proof
 rw [same_fext_n_def] \\ first_x_assum (qspec_then `var` assume_tac) \\ rfs [sum_same_value_def]
QED

Theorem si_sound_cell_input_covered_by_extenv_cget_net:
 !fext EE E cenv si var.
 si_sound fext EE E cenv si ==> cell_input_covered_by_extenv EE (cget_net si var)
Proof
 rw [si_sound_def, cget_net_def] \\ TOP_CASE_TAC >- simp [cell_input_covered_by_extenv_def] \\ drule_first
QED

Theorem cell_input_idx_cell_input_covered_by_extenv:
 !inp inp' idx EE.
 cell_input_idx inp idx = INR inp' /\ cell_input_covered_by_extenv EE inp ==>
 cell_input_covered_by_extenv EE inp'
Proof
 Cases
 >- (Cases_on ‘v’ \\ fs [cell_input_idx_def, cell_input_covered_by_extenv_def])
 >- (rename1 ‘ExtInp _ idx’ \\ Cases_on ‘idx’ \\ fs [cell_input_idx_def, cell_input_covered_by_extenv_def])
 \\ rename1 ‘VarInp _ idx’ \\ Cases_on ‘idx’ \\ fs [cell_input_idx_def, cell_input_covered_by_extenv_def]
QED

Theorem cell_input_idx_cell_input_covered_by_extenv:
 !inp inp' idx EE.
 cell_input_idx inp idx = INR inp' /\ cell_input_covered_by_extenv EE inp ==>
 cell_input_covered_by_extenv EE inp'
Proof
 rpt strip_tac \\ drule_strip cell_input_idx_INR \\ fs [cell_input_idx_def] \\ rveq \\
 fs [cell_input_covered_by_extenv_def]
QED

Theorem cell_input_slice_cell_input_covered_by_extenv:
 !inp inp' i1 i2 EE.
 cell_input_slice inp i1 i2 = INR inp' /\ cell_input_covered_by_extenv EE inp ==>
 cell_input_covered_by_extenv EE inp'
Proof
 rpt strip_tac \\ drule_strip cell_input_slice_INR \\ fs [cell_input_slice_def] \\ rveq \\
 fs [cell_input_covered_by_extenv_def]
QED

Theorem cstate_ok_cset_var:
 ∀fext EEv Ev s cenv v.
 cstate_ok fext EEv Ev s cenv ⇒
 cstate_ok fext EEv Ev (s with tmpnum := SUC s.tmpnum) (cset_var cenv (NetVar s.tmpnum) v)
Proof
 rw [cstate_ok_def, si_lt_SUC, si_sound_cset_var_spec, si_complete_cset_var_spec]
QED

Theorem compile_exp_correct:
 !e EEv Ev cenv t cs cs' nl inp ps fext fextv.
  compile_exp cs e = INR (cs', nl, inp) /\
  vertype_exp EEv Ev e t /\
  no_array_read_dyn_exp Ev EEv e /\ (* <-- merge with other pre-processing maybe *)

  same_fext_n fextv fext /\
  vertype_fext_n EEv fextv /\

  writes_ok_sis ps cs /\
  cstate_ok fext EEv Ev cs cenv ==>

  cs'.bsi = cs.bsi /\
  cs'.nbsi = cs.nbsi /\
  writes_ok_sis ps cs' /\
  cstate_progress cs cs' /\
  netlist_ok EEv cs.tmpnum cs'.tmpnum nl /\
  netlist_sorted nl /\
  cell_input_lt inp cs'.tmpnum /\
  cell_input_covered_by_extenv EEv inp /\
  ?cenv'. sum_foldM (cell_run fext) cenv nl = INR cenv' /\
          cstate_ok fext EEv Ev cs' cenv' /\
          ?cv t'.
           cell_inp_run fext cenv' inp = INR cv /\
           rtltype_v cv t' /\ same_type t t' /\
           (!vs vv.
             erun fextv vs e = INR vv /\ same_state_sis fext vs cs cenv ==>
             same_state_sis fext vs cs' cenv' /\
             same_value vv cv)
Proof
 Induct \\ rpt strip_tac' \\
 qpat_x_assum `vertype_exp _ _ _ _`
              (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_exp_cases]) \\ rveq

 >- (* Const *)
 (fs [compile_exp_def] \\ rveq \\
  simp [cstate_progress_def, netlist_ok_def, netlist_sorted_def, sum_foldM_def, cell_inp_run_def, cell_input_lt_def, erun_def, compile_value_correct, cell_input_covered_by_extenv_def] \\
  drule_strip compile_value_type_correct \\ rpt asm_exists_tac)

 >- (* Var *)
 (fs [compile_exp_def] \\ rveq \\ 
  simp [cstate_progress_def, netlist_ok_def, netlist_sorted_def, sum_foldM_def] \\
  fs [cstate_ok_def, si_complete_def] \\ rpt drule_first \\ rpt conj_tac
  >- (fs [cget_net_def, si_lt_def] \\ CASE_TAC \\ fs [cell_input_lt_def, var_lt_def] \\ drule_first)
  >- (match_mp_tac si_sound_cell_input_covered_by_extenv_cget_net \\ asm_exists_tac) \\
  rpt asm_exists_tac \\
  simp [erun_def, erun_get_var_def, same_state_sis_def, same_state_bsi_def, GSYM get_var_sum_alookup] \\
  rpt strip_tac \\ drule_first \\ rfs [])

 >- (* InputVar *)
 (fs [compile_exp_def] \\ rveq \\
  simp [cstate_progress_def, netlist_ok_def, netlist_sorted_def, sum_foldM_def, cell_input_lt_def, cell_inp_run_def, cell_input_covered_by_extenv_def] \\
  fs [vertype_fext_n_def, GSYM sum_alookup_INR] \\ drule_first \\
  drule_strip same_fext_n_ver_INR \\ simp [sum_bind_def, cget_fext_var_def] \\
  drule_strip (GSYM same_value_rtltype_v_vertype_v) \\ fs [] \\ asm_exists_tac \\ simp [compile_type_correct] \\
  simp [erun_def, erun_get_var_def])

 THEN2 (* ArrayIndex *)
 (ntac 2 (last_x_assum kall_tac) \\
 fs [no_array_read_dyn_exp_def] \\ every_case_tac \\ fs [sum_bind_INR, get_const_INR, get_var_type_def, tenv_type_INR] \\
 Cases_on ‘i’ \\ fs [ver2n_def, ver2v_def, sum_map_def] \\ rveq \\
 qpat_x_assum `vertype_exp _ _ _ _`
  (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_exp_cases, vertype_v_cases]) \\ rveq \\
 fs [compile_exp_def, sum_bind_INR, sum_map_def, ver2n_def, ver2v_def] \\ rveq \\
 simp [cstate_progress_def, netlist_ok_def, netlist_sorted_def] \\ rpt conj_tac
 >- (simp [cell_input_lt_def] \\
     fs [cstate_ok_def] \\
     match_mp_tac cell_input_idx_cell_input_lt \\ asm_exists_tac \\
     match_mp_tac si_lt_cell_input_lt_cget_net \\ asm_exists_tac)
 >- (simp [cell_input_covered_by_extenv_def] \\
     fs [cstate_ok_def] \\
     match_mp_tac cell_input_idx_cell_input_covered_by_extenv \\ asm_exists_tac \\
     match_mp_tac si_sound_cell_input_covered_by_extenv_cget_net \\ asm_exists_tac) \\
 simp [sum_foldM_def] \\ fs [cstate_ok_def] \\

 (* InputVar case *)
 TRY (
  fs [vertype_fext_n_def, sum_alookup_INR] \\ drule_first \\
  drule_strip same_fext_n_ver_INR \\
  gvs [vertype_v_cases, same_value_cases] \\
  simp [cell_inp_run_def, sum_bind_def, cget_fext_var_def, sum_map_INR, sum_revEL_INR] \\
  simp [rtltype_v_cases, same_type_cases] \\ rpt strip_tac' \\
  gvs [erun_def, sum_bind_INR, erun_get_var_def, get_array_index_INR, ver2n_INR] \\
  simp [same_value_cases] \\
  NO_TAC) \\

 (* Var case *)
 fs [si_complete_def] \\ rpt drule_first \\ fs [same_type_cases] \\ rveq \\ fs [rtltype_v_CArray_t] \\ rveq \\
 simp [erun_def, erun_get_var_def] \\
 fs [alist_to_map_alookup, GSYM sum_alookup_INR] \\ rveq \\
 drule_strip cell_input_idx_cell_inp_run \\ simp [rtltype_v_cases] \\
 simp [sum_bind_INR, ver2n_VArray] \\ rpt strip_tac' \\
 fs [same_state_sis_def, same_state_bsi_def, GSYM get_var_sum_alookup] \\
 drule_first \\ fs [get_array_index_INR] \\ rveq \\ fs [same_value_def])

 >- (* ArraySlice - Var *)
 (last_x_assum kall_tac \\
  fs [compile_exp_def, sum_bind_INR] \\ rveq \\
  fs [netlist_ok_def, netlist_sorted_def, sum_foldM_def, cstate_progress_def, cstate_ok_def] \\
  rpt conj_tac
  >- (match_mp_tac cell_input_slice_cell_input_lt \\ asm_exists_tac \\
      match_mp_tac si_lt_cell_input_lt_cget_net \\ asm_exists_tac)
  >- (match_mp_tac cell_input_slice_cell_input_covered_by_extenv \\ asm_exists_tac \\
      match_mp_tac si_sound_cell_input_covered_by_extenv_cget_net \\ asm_exists_tac) \\

  qpat_x_assum ‘si_complete _ _ _ cs.nbsi’ kall_tac \\  
  fs [si_complete_def] \\ drule_first \\
  fs [same_type_cases] \\ rveq \\ fs [rtltype_v_CArray_t] \\ rveq \\
  drule_strip cell_input_slice_cell_inp_run \\ simp [] \\
  conj_tac >- simp [rev_slice_def] \\ rpt strip_tac \\
  fs [erun_def, erun_get_var_def, sum_bind_INR,
      same_state_sis_def, same_state_bsi_def, GSYM get_var_sum_alookup] \\
  drule_first \\ fs [get_array_slice_INR] \\ rveq \\ fs [same_value_def, rev_slice_def])

 >- (* ArraySlice - InputVar *)
 (last_x_assum kall_tac \\
  fs [compile_exp_def, sum_bind_INR] \\ rveq \\
  fs [netlist_ok_def, netlist_sorted_def, sum_foldM_def, cstate_progress_def, cstate_ok_def] \\
  rpt conj_tac
  >- simp [cell_input_lt_def]
  >- simp [cell_input_covered_by_extenv_def] \\

  fs [vertype_fext_n_def, sum_alookup_INR] \\ drule_first \\
  drule_strip same_fext_n_ver_INR \\
  gvs [vertype_v_cases, same_value_cases] \\
  simp [cell_inp_run_def, sum_bind_def, cget_fext_var_def, sum_map_INR] \\
  simp [rtltype_v_cases, same_type_cases] \\ rpt strip_tac' \\
  gvs [erun_def, sum_bind_INR, erun_get_var_def, get_array_slice_INR] \\
  simp [same_value_cases])

 >- (* BUOp *)
 (fs [compile_exp_def, sum_bind_INR, compile_new_name_def, no_array_read_dyn_exp_def] \\
  pairarg_tac \\ fs [] \\ drule_first \\ rw []
  >- fs [writes_ok_sis_def]
  >- fs [cstate_progress_def]
  >- (rw [netlist_ok_append]
      >- (match_mp_tac netlist_ok_le \\ asm_exists_tac \\ simp [])
      \\ fs [netlist_ok_def, cell_covered_by_extenv_def, cell_ok_def, cell_output_ok_def, cstate_progress_def])
  >- (drule_strip netlist_sorted_snoc \\ disch_then match_mp_tac \\ simp [cell_output_def])
  >- simp [cell_input_lt_def, var_lt_def]
  >- simp [cell_input_covered_by_extenv_def] \\
  
  fs [same_type_cases, rtltype_v_ground_cases, sum_foldM_append, sum_bind_def] \\
  simp [sum_foldM_def, cell_run_def, cell1_run_def, sum_bind_def,
        cstate_ok_cset_var, cget_var_cset_var, cell_inp_run_def, cget_fext_var_def] \\
  simp [erun_def, ver_liftVBool_INR, sum_bind_INR] \\ rpt strip_tac' \\ drule_first \\ rveq \\
  fs [cstate_ok_def, same_state_sis_def, same_value_def] \\
  metis_tac [same_state_bsi_cset_var_si_lt, same_state_nbsi_cset_var_si_lt])

 >- (* BBOp *)
 (fs [compile_exp_def, sum_bind_INR, compile_new_name_def, no_array_read_dyn_exp_def] \\
  rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\ drule_last \\ drule_first \\ rw []
  >- fs [writes_ok_sis_def]
  >- fs [cstate_progress_def]
  >- (simp [netlist_ok_append] \\ reverse (rpt conj_tac)
      >- (fs [netlist_ok_def, cell_covered_by_extenv_def, cell_ok_def, cell_output_ok_def, cstate_progress_def] \\
          match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])
      \\ match_mp_tac netlist_ok_le \\ asm_exists_tac \\ fs [cstate_progress_def])
 >- (qspec_then ‘EEv’ match_mp_tac netlist_sorted_append_snoc \\ rpt asm_exists_tac \\
     fs [cstate_progress_def, cell_output_def])
 >- simp [cell_input_lt_def, var_lt_def]
 >- simp [cell_input_covered_by_extenv_def] \\

 fs [same_type_cases, rtltype_v_ground_cases, sum_foldM_append, sum_bind_def] \\
 simp [sum_foldM_def, cell_run_def] \\

 qspec_then `inp1` assume_tac cells_run_unchanged_netlist_ok \\ drule_first \\
 simp [sum_bind_def] \\ strip_tac \\

 Cases_on ‘b’ \\ simp [compile_bbop_def, cell2_run_def, sum_bind_def, cstate_ok_cset_var,
                       cell_inp_run_def, cget_fext_var_def, cget_var_cset_var, erun_def, sum_bind_INR] \\
 rpt strip_tac' \\ drule_last \\ drule_first \\ every_case_tac \\ fs [] \\ rveq \\
 fs [cstate_ok_def, same_state_sis_def, same_value_def, erun_bbop_def] \\
 metis_tac [same_state_bsi_cset_var_si_lt, same_state_nbsi_cset_var_si_lt])

 >- (* Arith -- almost the same as BBOp *)
 (fs [compile_exp_def, sum_bind_INR, compile_new_name_def, no_array_read_dyn_exp_def] \\
  rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\ drule_last \\ drule_first \\ rw []
  >- fs [writes_ok_sis_def]
  >- fs [cstate_progress_def]
  >- (simp [netlist_ok_append] \\ reverse (rpt conj_tac)
      >- (fs [netlist_ok_def, cell_covered_by_extenv_def, cell_ok_def, cell_output_ok_def, cstate_progress_def] \\
          match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])
      \\ match_mp_tac netlist_ok_le \\ asm_exists_tac \\ fs [cstate_progress_def])
 >- (qspec_then ‘EEv’ match_mp_tac netlist_sorted_append_snoc \\ rpt asm_exists_tac \\
     fs [cstate_progress_def, cell_output_def])
 >- simp [cell_input_lt_def, var_lt_def]
 >- simp [cell_input_covered_by_extenv_def] \\

 fs [same_type_cases, rtltype_v_ground_cases, sum_foldM_append, sum_bind_def] \\
 simp [sum_foldM_def, cell_run_def] \\

 qspec_then `inp1` assume_tac cells_run_unchanged_netlist_ok \\ drule_first \\
 simp [sum_bind_def] \\ strip_tac \\
 (* Diff from here w.r.t BBOp: *)
 simp [compile_bbop_def, cell2_run_def, compile_arith_def, sum_bind_def, cstate_ok_cset_var,
       cell_inp_run_def, cget_fext_var_def, cget_var_cset_var, erun_def, erun_arith_def,
       sum_bind_INR, sum_check_INR, ver_liftVArray_INR, ver_mapVArray_INR, ver_fixwidth_fixwidth] \\
 rpt strip_tac' \\ drule_last \\ drule_first \\ rveq \\
 fs [cstate_ok_def, same_state_sis_def, n2ver_def, v2ver_def, ver2n_INR] \\ rveq \\ fs [same_value_def] \\
 metis_tac [same_state_bsi_cset_var_si_lt, same_state_nbsi_cset_var_si_lt])

 >- (* Cmp -- also similar to BBOp *)
 (fs [compile_exp_def, sum_bind_INR, compile_new_name_def, no_array_read_dyn_exp_def] \\
  rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\ drule_last \\ drule_first \\ rw []
  >- fs [writes_ok_sis_def]
  >- fs [cstate_progress_def]
  >- (simp [netlist_ok_append] \\ reverse (rpt conj_tac)
      >- (fs [netlist_ok_def, cell_covered_by_extenv_def, cell_ok_def, cell_output_ok_def, cstate_progress_def] \\
          match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])
      \\ match_mp_tac netlist_ok_le \\ asm_exists_tac \\ fs [cstate_progress_def])
 >- (qspec_then ‘EEv’ match_mp_tac netlist_sorted_append_snoc \\ rpt asm_exists_tac \\
     fs [cstate_progress_def, cell_output_def])
 >- simp [cell_input_lt_def, var_lt_def]
 >- simp [cell_input_covered_by_extenv_def] \\

 fs [same_type_cases, rtltype_v_ground_cases, sum_foldM_append, sum_bind_def] \\
 simp [sum_foldM_def, cell_run_def] \\

 qspec_then `inp1` assume_tac cells_run_unchanged_netlist_ok \\ drule_first \\
 simp [sum_bind_def] \\ strip_tac \\

 simp [cell2_run_def, sum_bind_def, cstate_ok_cset_var, cell_inp_run_def, cget_var_cset_var, cget_fext_var_def,
       erun_def, sum_bind_INR, sum_check_INR] \\
 rpt strip_tac' \\ drule_last \\ drule_first \\ rveq \\
 fs [same_value_cases, erun_cmp_def, sum_bind_INR, get_VArray_data_INR] \\ rveq \\
 fs [cstate_ok_def, same_state_sis_def] \\
 metis_tac [same_state_bsi_cset_var_si_lt, same_state_nbsi_cset_var_si_lt])
QED

Theorem new_block_correct:
 !s s' EE E cenv ps fext.
  new_block s = INR s' /\ cstate_ok fext EE E s cenv /\ writes_ok_sis ps s ==>
  cstate_ok fext EE E s' cenv /\ writes_ok_sis ps s' /\ cstate_progress s s' /\
  (!var. cget_net_var s'.bsi var = cget_net_var s.bsi var) /\
  (!var. cget_net_var s'.nbsi var = cget_net_var s.nbsi var)
Proof
 rw [new_block_def] \\
 fs [cstate_ok_def, si_wf_cons_empty, si_lt_cons_empty, si_sound_cons_empty, si_complete_cons_empty,
     writes_ok_sis_def, cstate_progress_def, cget_net_var_cons_empty]
QED

Theorem pop_block_correct_help:
 !s s' s'' s''' bsi nbsi.
  new_block s = INR s' /\
  sis_progress s' s'' /\
  pop_block s'' = INR (s''', bsi, nbsi) ==>
  s'.tmpnum = s.tmpnum /\ s'.vertypes = s.vertypes /\
  s'''.bsi = s.bsi /\ s'''.nbsi = s.nbsi /\ s'''.vertypes = s''.vertypes /\ s'''.tmpnum = s''.tmpnum /\
  bsi::s.bsi = s''.bsi /\ nbsi::s.nbsi = s''.nbsi
Proof
 simp [new_block_def, sis_progress_def, si_progress_def, pop_block_def] \\
 Cases_on `s''.bsi` \\ Cases_on `s''.nbsi` \\ simp []
QED

Theorem pop_block_correct:
 !s s' s'' s''' (extenv : extenvt) bsi nbsi EE E cenv cenv' nl ps fext.
  new_block s = INR s' /\
  writes_ok_sis ps s /\
  cstate_ok fext EE E s cenv /\

  cstate_progress s' s'' /\
  sis_progress s' s'' /\
  netlist_ok extenv s'.tmpnum s''.tmpnum nl /\
  sum_foldM (cell_run fext) cenv nl = INR cenv' /\
  cstate_ok fext EE E s'' cenv' /\

  pop_block s'' = INR (s''', bsi, nbsi) ==>
  s'''.bsi = s.bsi /\ s'''.nbsi = s.nbsi /\
  writes_ok_sis ps s''' /\
  cstate_ok fext EE E s''' cenv' /\
  cstate_progress s'' s''' /\
  sis_progress s s''' /\
  
  bsi::s.bsi = s''.bsi /\ nbsi::s.nbsi = s''.nbsi
Proof
 rpt strip_tac' \\ drule_strip pop_block_correct_help \\
 fs [writes_ok_sis_def, cstate_ok_def, cstate_progress_def, sis_progress_def, sis_progress_def, si_progress_def] \\
 metis_tac [si_lt_le, cells_run_si_sound, cells_run_si_complete, arithmeticTheory.LESS_EQ_REFL]
QED

val mux_input_ok_def = Define `
 mux_input_ok si inp <=> ?var. cget_net si var = inp`;

val mux_ok_def = Define `
 (mux_ok extenv cond min max tsi fsi (CellMux out in1 in2 in3) <=>
  cell_output_ok min max out /\
  (in1 = cond) ∧ (*mux_input_ok tsi in1 /\*) cell_input_lt in1 out ∧
  mux_input_ok tsi in2 /\ cell_input_lt in2 out /\
  mux_input_ok fsi in3 /\ cell_input_lt in3 out) /\
 (mux_ok extenv cond min max tsi fsi _ <=> F)`;

val muxlist_ok_def = Define `
 muxlist_ok extenv cond min max tsi fsi nl <=> EVERY (cell_covered_by_extenv extenv) nl ∧
                                               EVERY (mux_ok extenv cond min max tsi fsi) nl`;

Theorem muxlist_ok_nil:
 !extenv cond min max tsi fsi. muxlist_ok extenv cond min max tsi fsi []
Proof
 rw [muxlist_ok_def]
QED

Theorem muxlist_ok_singleton:
 !extenv cond min max tsi fsi cell.
 muxlist_ok extenv cond min max tsi fsi [cell] <=> mux_ok extenv cond min max tsi fsi cell ∧
                                                   cell_covered_by_extenv extenv cell
Proof
 rw [muxlist_ok_def] \\ eq_tac \\ rw []
QED

Theorem mux_ok_cell_ok:
 !cell extenv cond min max tsi fsi.
 mux_ok extenv cond min max tsi fsi cell ==> cell_ok min max cell
Proof
 Cases \\ rw [mux_ok_def, cell_ok_def]
QED

Theorem muxlist_ok_netlist_ok:
 !extenv cond min max tsi fsi nl.
 muxlist_ok extenv cond min max tsi fsi nl ==> netlist_ok extenv min max nl
Proof
 rw [muxlist_ok_def, netlist_ok_def] \\
 irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [] \\ drule_strip mux_ok_cell_ok
QED

Theorem mux_ok_le:
 !extenv cond min min' max max' tsi fsi cell.
  mux_ok extenv cond min' max' tsi fsi cell /\ min <= min' ∧ max' <= max ==>
  mux_ok extenv cond min max tsi fsi cell
Proof
 Cases_on `cell` \\ rw [mux_ok_def, cell_output_ok_def]
QED

Theorem muxlist_ok_le:
 !extenv cond min min' max max' tsi fsi nl.
  muxlist_ok extenv cond min' max' tsi fsi nl /\ min <= min' /\ max' <= max ==>
  muxlist_ok extenv cond min max tsi fsi nl
Proof
 (* Not sure why metis cannot solve this by itself? *)
 rw [muxlist_ok_def] \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ metis_tac [mux_ok_le]
QED

(*Theorem mux_input_ok_cons:
 !b bs inp. mux_input_ok [b] inp ==> mux_input_ok (b::bs) inp
Proof
 simp [mux_input_ok_def, cget_net_def]
QED

Theorem muxlist_ok_left_si_cons:
 !cond min max b bs si nl. muxlist_ok cond min max [b] si nl ==> muxlist_ok cond min max (b::bs) si nl
Proof
 rw [muxlist_ok_def] \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ Cases \\ rw [mux_ok_def, mux_input_ok_def]

 simp [mux_ok_def, mux_input_ok_def]
QED

Theorem muxlist_ok_EVERY_ge:
 !nl cond min max tsi fsi. muxlist_ok cond min max tsi fsi nl ==> EVERY (\c. min <= cell_output c) nl
Proof
 Induct \\ fs [muxlist_ok_def] \\ rpt strip_tac' \\ Cases_on `h` \\ 
 fs [mux_ok_def, cell_output_def, cell_output_ok_def] \\
 first_x_assum match_mp_tac \\ asm_exists_tac
QED*)

Theorem mux_ok_cons_empty: (* <-- generalize *)
 !cell extenv cond min max tsi fsi.
 mux_ok extenv cond min max tsi fsi cell ==> mux_ok extenv cond min max (empty::tsi) fsi cell
Proof
 Cases \\ rw [mux_ok_def, mux_input_ok_def, cget_net_cons_empty] \\ metis_tac []
QED

Theorem muxlist_ok_cons_empty: (* <-- generalize *)
 !nl extenv cond min max tsi fsi.
  muxlist_ok extenv cond min max tsi fsi nl ==> muxlist_ok extenv cond min max (empty::tsi) fsi nl
Proof
 rw [muxlist_ok_def] \\ metis_tac [EVERY_MONOTONIC, mux_ok_cons_empty]
QED

Theorem muxlist_ok_reverse:
 !nl extenv cond min max tsi fsi.
 muxlist_ok extenv cond min max tsi fsi (REVERSE nl) <=> muxlist_ok extenv cond min max tsi fsi nl
Proof
 simp [muxlist_ok_def, rich_listTheory.EVERY_REVERSE]
QED

Theorem muxlist_ok_cons:
 !cell nl extenv cond min max tsi fsi.
  muxlist_ok extenv cond min max tsi fsi (cell :: nl) <=>
  cell_covered_by_extenv extenv cell ∧ EVERY (cell_covered_by_extenv extenv) nl ∧
  mux_ok extenv cond min max tsi fsi cell /\ muxlist_ok extenv cond min max tsi fsi nl  
Proof
 rw [muxlist_ok_def] \\ eq_tac \\ rw []
QED

Theorem muxlist_ok_append:
 !nl1 nl2 extenv cond min max tsi fsi.
  muxlist_ok extenv cond min max tsi fsi (nl1 ++ nl2) <=>
  muxlist_ok extenv cond min max tsi fsi nl1 /\ muxlist_ok extenv cond min max tsi fsi nl2
Proof
 rw [muxlist_ok_def] \\ eq_tac \\ rw []
QED

Theorem cell_output_ok_min_max:
 !min max out. cell_output_ok min max out ==> min < max
Proof
 rw [cell_output_ok_def]
QED

Theorem muxlist_ok_merge:
 !nl1 nl2 cond min middle max tsi fsi fext.
  muxlist_ok fext cond min middle tsi fsi nl1 /\ muxlist_ok fext cond middle max tsi fsi nl2 /\
  min < middle /\ middle < max ==>
  muxlist_ok fext cond min max tsi fsi (nl1 ++ nl2)
Proof
 rw [muxlist_ok_append] \\ match_mp_tac muxlist_ok_le \\ asm_exists_tac \\ simp []
QED

Theorem cells_run_unchanged_muxlist_ok: (* old name = cells_run_same_cell_input_lt_mux *)
 !inp cenv cenv' nl cond min max tsi fsi n fext (EE : extenvt).
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 muxlist_ok EE cond min max tsi fsi nl /\
 cell_input_lt inp n /\
 n <= min ==>
 cell_inp_run fext cenv' inp = cell_inp_run fext cenv inp
Proof
 metis_tac [muxlist_ok_netlist_ok, cells_run_unchanged_netlist_ok]
QED

Theorem cells_run_unchanged_muxlist_ok_cget_net_var:
 !inp var si cenv cenv' nl cond min max tsi fsi fext (EE : extenvt).
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 muxlist_ok EE cond min max tsi fsi nl /\
 cget_net_var si var = SOME inp ∧
 si_lt si min ==>
 cell_inp_run fext cenv' inp = cell_inp_run fext cenv inp
Proof
 metis_tac [muxlist_ok_netlist_ok, cells_run_unchanged_netlist_ok_cget_net_var]
QED

Theorem cells_run_unchanged_muxlist_ok_cget_net:
 !si cenv cenv' nl cond min max tsi fsi fext (EE : extenvt).
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 muxlist_ok EE cond min max tsi fsi nl /\
 si_lt si min ==>
 (!var. cell_inp_run fext cenv' (cget_net si var) = cell_inp_run fext cenv (cget_net si var))
Proof
 metis_tac [muxlist_ok_netlist_ok, cells_run_unchanged_netlist_ok_cget_net]
QED

(*Theorem mux_input_lt:
 !inp cond min max tsi fsi cell EE.
 mux_ok EE cond min max tsi fsi cell /\
 cell_input_lt cond min /\
 si_lt tsi min /\
 si_lt fsi min /\
 cell_has_input cell inp ==>
 cell_input_lt inp min
Proof
 Cases
 >- simp [cell_input_lt_def]
 >- simp [cell_input_lt_def]
 \\ rpt strip_tac \\ Cases_on `cell` \\ fs [mux_ok_def, cell_has_input_def] \\ rveq \\
 fs [mux_input_ok_def, si_lt_def] \\ (Cases_on `v` >- simp [cell_input_lt_def, var_lt_def]) \\
 metis_tac [cget_net_VarInp_NetVar]
QED*)

Theorem cget_net_var_Bin_NONE:
 !n k v t t' var.
 si_wf [Bin n k v t t'] /\ cget_net_var [Bin n k v t t'] var = NONE ==>
  cget_net_var [t] var = NONE /\ k <> var /\ cget_net_var [t'] var = NONE
Proof
 simp [si_wf_def, cget_net_var_singleton] \\ metis_tac [lookup_Bin_NONE]
QED

Theorem cget_net_var_Bin_SOME_imp:
 !n k v t t' var x.
 si_wf [Bin n k v t t'] /\ cget_net_var [Bin n k v t t'] var = SOME x ==>
  (cget_net_var [t] var = SOME x ∧ cget_net_var [t'] var = NONE /\ var <> k) \/
  (cget_net_var [t] var = NONE /\ cget_net_var [t'] var = SOME x /\ var <> k) \/
  (cget_net_var [t] var = NONE /\ cget_net_var [t'] var = NONE /\ var = k /\ x = v)
Proof
 simp [si_wf_def, invariant_def, cget_net_var_singleton, lookup_def] \\
 rpt gen_tac \\ CASE_TAC \\ rpt strip_tac \\
 fs [] \\ rveq \\ metis_tac [lookup_key_Greater_x2, string_cmp_Greater_not_eq, lookup_key_Greater, 
                             lookup_key_Less_x2, string_cmp_Less_not_eq, lookup_key_Less]
QED

val lookup_thm_string_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) (SPEC_ALL lookup_thm)) comparisonTheory.string_cmp_good;

Theorem cget_net_var_Bin_SOME_eq:
 !n k v t t' var x.
 si_wf [Bin n k v t t'] ==>
  (cget_net_var [Bin n k v t t'] var = SOME x ⇔
  ((cget_net_var [t] var = SOME x) ∨
   (cget_net_var [t'] var = SOME x) ∨
   (var = k /\ x = v)))
Proof
 simp [si_wf_def, cget_net_var_singleton, lookup_thm_string_cmp] \\
 rw [invariant_eq, pred_setTheory.DISJOINT_ALT, lookup_thm_string_cmp] \\
 rw [to_fmap_def, finite_mapTheory.FLOOKUP_UPDATE]
 >- (fs [finite_mapTheory.FLOOKUP_DEF, key_set_eq] \\ metis_tac []) \\
 simp [finite_mapTheory.FLOOKUP_FUNION] \\ TOP_CASE_TAC >- metis_tac [] \\
 eq_tac \\ rw [] \\ fs [finite_mapTheory.FLOOKUP_DEF] \\ metis_tac []
QED

Theorem si_wf_Bin:
 !n k v t t'. si_wf [Bin n k v t t'] ==> si_wf [t] /\ si_wf [t']
Proof
 rw [si_wf_def, invariant_def]
QED

val si_subset_def = Define `
 si_subset si1 si2 <=> !var inp. cget_net_var si1 var = SOME inp ==> cget_net_var si2 var = SOME inp`;

Theorem si_subset_sym:
 !si. si_subset si si
Proof
 simp [si_subset_def]
QED

Theorem si_subset_cons:
 !b bs. si_subset [b] (b::bs)
Proof
 rw [si_subset_def, cget_net_var_singleton] \\ simp [cget_net_var_def]
QED

Theorem si_subset_Bin:
 !n k v t t' si.
 si_wf [Bin n k v t t'] /\ si_subset [Bin n k v t t'] si ==>
  si_subset [t] si /\ cget_net_var si k = SOME v /\ si_subset [t'] si
Proof
 simp [si_wf_def, invariant_def, si_subset_def, cget_net_var_singleton, lookup_def] \\ rpt strip_tac \\
 first_x_assum match_mp_tac
 >- (CASE_TAC \\ fs [] \\ rveq \\ metis_tac [lookup_key_Greater, lookup_key_Greater_x2, optionTheory.NOT_SOME_NONE])
 >- simp [string_cmp_sym]
 \\ (CASE_TAC \\ fs [] \\ rveq \\ metis_tac [lookup_key_Less, lookup_key_Less_x2, optionTheory.NOT_SOME_NONE])
QED

Theorem si_lt_si_subset_si_lt:
 !si bigsi n. si_lt bigsi n /\ si_subset si bigsi ==> si_lt si n
Proof
 rw [si_subset_def, si_lt_def] \\ rpt drule_first
QED

(*Theorem only_bools_for_now_si_sound_get_bool:
 !Ec si var inp cenv fext.
 only_bools_for_now Ec /\
 cget_net_var si var = SOME inp /\
 si_sound fext Ec cenv si ==>
 ?b. cell_inp_run fext cenv inp = INR (CBool b)
Proof
 rw [only_bools_for_now_def, si_sound_def] \\ rpt drule_first \\ rveq \\
 drule_strip rtltype_v_CBool_t \\ asm_exists_tac
QED

Theorem only_bools_for_now_si_complete_get_bool:
 !si' si Ec var inp cenv fext.
 only_bools_for_now Ec /\
 cget_net_var si var = SOME inp /\
 si_sound fext Ec cenv si /\
 si_complete fext Ec cenv si' ==>
 ?b. cell_inp_run fext cenv (cget_net si' var) = INR (CBool b)
Proof
 rw [only_bools_for_now_def, si_sound_def, si_complete_def] \\ rpt drule_first \\ rveq \\
 drule_strip rtltype_v_CBool_t \\ asm_exists_tac
QED*)

Theorem cellMux_run_same_type:
 ∀v v' b t.
 rtltype_v v t ∧ rtltype_v v' t ⇒
 cellMux_run (CBool b) v v' = INR (if b then v else v') ∧ rtltype_v (if b then v else v') t
Proof
 Cases_on ‘t’ \\ simp [rtltype_v_cases] \\ rpt strip_tac' \\ rw [cellMux_run_def, sum_check_def, sum_bind_def]
QED

Theorem compile_merge_if_left_correct:
 !cond othersi k v cs si nl cs' si' nl' min bigsi EE E cenv cenv' b fext.
 compile_merge_if_left cond othersi k v (cs, si, nl) = (cs', si' , nl') /\

 muxlist_ok EE cond min cs.tmpnum bigsi othersi nl /\
 netlist_sorted nl ∧
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 cstate_ok fext EE E cs cenv' /\
 cell_input_lt cond min /\
 cell_inp_run fext cenv cond = INR (CBool b) /\
 cell_input_covered_by_extenv EE cond ∧

 cget_net_var bigsi k = SOME v /\
 si_sound fext EE E cenv' bigsi /\ si_lt bigsi min /\
 si_sound fext EE E cenv' othersi /\ si_lt othersi min /\ si_complete fext E cenv' othersi /\
 si_wf si /\ si_sound fext EE E cenv' si /\ si_lt si cs.tmpnum /\ si_complete fext E cenv' si /\
 
 min <= cs.tmpnum
 ==>
 cs'.bsi = cs.bsi /\ cs'.nbsi = cs.nbsi /\
 (!var. cget_net_var si' var = if var = k then SOME (VarInp (NetVar cs.tmpnum) NoIndexing) else cget_net_var si var) /\
 IS_SOME (cget_net_var [HD si'] k) ∧
 (*cstate_progress cs cs' <-- too weak here *) cs.tmpnum < cs'.tmpnum /\
 si_progress si si' /\
 muxlist_ok EE cond min cs'.tmpnum bigsi othersi nl' /\
 netlist_sorted nl' ∧
 (?mcell. nl' = SNOC mcell nl /\ mux_ok EE cond cs.tmpnum cs'.tmpnum bigsi othersi mcell) /\
 ?cenv''.
  sum_foldM (cell_run fext) cenv nl' = INR cenv'' /\
  cstate_ok fext EE E cs' cenv'' /\

  si_sound fext EE E cenv'' bigsi /\
  si_sound fext EE E cenv'' othersi /\ si_complete fext E cenv'' othersi /\
  si_wf si' /\ si_sound fext EE E cenv'' si' /\ si_lt si' cs'.tmpnum /\ si_complete fext E cenv'' si' /\

  cell_inp_run fext cenv'' (VarInp (NetVar cs.tmpnum) NoIndexing) =
   (if b then cell_inp_run fext cenv v else cell_inp_run fext cenv (cget_net othersi k)) ∧

  (!inp. ~cell_input_is_var inp (NetVar cs.tmpnum) ⇒
         cell_inp_run fext cenv'' inp = cell_inp_run fext cenv' inp)
Proof
 simp [compile_merge_if_left_def, compile_new_name_def] \\ rpt strip_tac
 >- rw [cget_net_var_cset_net]
 >- simp [HD_cset_net, si_wf_HD, cget_net_var_cset_net]
 >- simp [si_progress_cset_net]
 >- (rw [muxlist_ok_append]
    >- (match_mp_tac muxlist_ok_le \\ asm_exists_tac \\ simp [])
    \\ rw [muxlist_ok_def]
       >- (rw [cell_covered_by_extenv_def] \\
           metis_tac [si_sound_def, si_sound_cell_input_covered_by_extenv_cget_net])
       \\ rw [mux_ok_def, cell_output_ok_def, mux_input_ok_def] \\
          metis_tac [cget_net_var_SOME_cget_net, 
                     si_lt_def, cell_input_lt_le, si_sound_def,
                     si_lt_cell_input_lt_cget_net])
 >- (drule_strip muxlist_ok_netlist_ok \\ drule_strip netlist_sorted_snoc \\ disch_then match_mp_tac \\
    simp [cell_output_def])
 >- (rw [mux_ok_def, cell_output_ok_def, mux_input_ok_def] \\
     metis_tac [cget_net_var_SOME_cget_net, cell_input_lt_le, si_lt_def, si_lt_cell_input_lt_cget_net]) \\

 simp [sum_foldM_append, sum_bind_def, sum_foldM_def, cell_run_def] \\
 drule_strip cells_run_unchanged_muxlist_ok \\ impl_tac >- simp [] \\ strip_tac \\
 qspec_then ‘v’ drule_strip cells_run_unchanged_muxlist_ok_cget_net_var \\
 qspec_then ‘othersi’ drule_strip cells_run_unchanged_muxlist_ok_cget_net \\

 qpat_assum ‘si_sound _ _ _ _ bigsi’ (drule_strip o SIMP_RULE (srw_ss()) [si_sound_def]) \\
 qpat_assum ‘si_complete _ _ _ othersi’ (drule_strip o SIMP_RULE (srw_ss()) [si_complete_def]) \\
 imp_res_tac same_type_deterministic \\ rveq \\

 simp [sum_bind_def] \\
 qspecl_then [‘cv’, ‘cv'’, ‘b’] assume_tac cellMux_run_same_type \\ pop_assum drule_strip \\
 simp [sum_bind_def] \\

 rpt conj_tac
 >- (fs [cstate_ok_def] \\ metis_tac [si_lt_SUC, si_sound_cset_var, si_complete_cset_var, arithmeticTheory.LESS_EQ_REFL])
 >- metis_tac [si_sound_cset_var]
 >- metis_tac [si_sound_cset_var]
 >- metis_tac [si_complete_cset_var]
 >- simp [si_wf_cset_net]
 >- metis_tac [si_sound_cset_var_cset_net]
 >- metis_tac [si_lt_cset_net_SUC]
 >- metis_tac [si_complete_cset_var_cset_net]
 >- (rfs [cell_inp_run_cset_var] \\ rw [])
 \\ Cases \\ simp [cell_inp_run_def, cell_input_is_var_def, cget_var_cset_var]
QED

Triviality TEMPORARY_HACK:
 (∀var idx. cget_net si var ≠ VarInp (NetVar n) idx) ⇒ (∀var. ¬cell_input_is_var (cget_net si var) (NetVar n))
Proof
 rw [] \\ Cases_on ‘cget_net si var’ \\ simp [cell_input_is_var_def] \\ metis_tac []
QED

val Case_option = TypeBase.case_pred_imp_of ``: 'a option`` |> Q.ISPEC `\x : bool. x` |> BETA_RULE;

Theorem foldrWithKey_compile_merge_if_left_correct:
 !bigsi min tblock cond othersi si si' nl nl' cs cs' EE E cenv cenv' b fext.
 foldrWithKey (compile_merge_if_left cond othersi) (cs, si, nl) tblock = (cs', si', nl') /\

 si_wf [tblock] /\
 si_sound fext EE E cenv' bigsi /\ si_lt bigsi min /\
 si_sound fext EE E cenv' othersi /\ si_lt othersi min /\ si_complete fext E cenv' othersi /\
 cell_input_lt cond min /\
 cell_input_covered_by_extenv EE cond ∧

 si_subset [tblock] bigsi /\
 muxlist_ok EE cond min cs.tmpnum bigsi othersi nl /\
 netlist_sorted nl ∧
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 
 cstate_ok fext EE E cs cenv' /\
 si_wf si /\ si_sound fext EE E cenv' si /\ si_lt si cs.tmpnum /\ si_complete fext E cenv' si /\

 cell_inp_run fext cenv cond = INR (CBool b) /\
 min <= cs.tmpnum
 ==>
 cs'.bsi = cs.bsi /\ cs'.nbsi = cs.nbsi /\
 cstate_progress cs cs' /\
 si_progress si si' /\
 muxlist_ok EE cond min cs'.tmpnum bigsi othersi nl' /\
 netlist_sorted nl' ∧
 (?nl''. nl' = nl ++ nl'' /\ muxlist_ok EE cond cs.tmpnum cs'.tmpnum bigsi othersi nl'') /\
 (!var. (∃inp. cget_net_var si' var = SOME inp) ⇔
        (?inp. cget_net_var [tblock] var = SOME inp) \/
        (?inp. cget_net_var si var = SOME inp)) /\
 (∀var. IS_SOME (cget_net_var [tblock] var) ⇒ IS_SOME (cget_net_var [HD si'] var)) ∧
 ?cenv''.
  sum_foldM (cell_run fext) cenv nl' = INR cenv'' /\

  si_sound fext EE E cenv'' bigsi /\
  si_sound fext EE E cenv'' othersi /\ si_complete fext E cenv'' othersi /\

  cstate_ok fext EE E cs' cenv'' /\
  si_wf si' /\ si_sound fext EE E cenv'' si' /\ si_lt si' cs'.tmpnum /\ si_complete fext E cenv'' si' /\
  !var. case cget_net_var [tblock] var of
            NONE => cget_net_var si' var = cget_net_var si var
          | SOME inp => cell_inp_run fext cenv'' (cget_net si' var) =
                         if b then cell_inp_run fext cenv' inp
                              else cell_inp_run fext cenv' (cget_net othersi var)
Proof
 ntac 2 gen_tac \\ Induct
 >- (rw [foldrWithKey_def, cstate_progress_def, si_progress_def, GSYM empty_def, cget_net_var_empty]
     >- simp []
     >- simp []
     >- simp [muxlist_ok_def]
     \\ rpt asm_exists_tac) \\

 rewrite_tac [foldrWithKey_def] \\ rpt strip_tac' \\
 drule_strip si_wf_Bin \\ drule_strip si_subset_Bin \\

 (* first: *)
 namedCases_on `foldrWithKey (compile_merge_if_left cond othersi) (cs, si, nl) tblock'`
               ["tblock'_cs tblock'_si tblock'_nl"] \\
 drule_first \\ rveq \\

 (* middle: *)
 namedCases_on `compile_merge_if_left cond othersi k v (tblock'_cs, tblock'_si, nl ++ nl'')`
               ["k_cs k_si k_nl"] \\
 drule_strip compile_merge_if_left_correct \\ impl_tac >- fs [cstate_progress_def] \\ strip_tac \\ rveq \\

 (* third: *)
 drule_first \\ impl_tac >- (fs [cstate_progress_def]) \\ strip_tac \\ rveq \\
 
 simp [] \\ rpt conj_tac
 >- fs [cstate_progress_def]
 >- fs [si_progress_def]
 >- (fs [muxlist_ok_append, SNOC_APPEND, muxlist_ok_cons, cstate_progress_def] \\
    metis_tac [mux_ok_le, muxlist_ok_le, muxlist_ok_nil,
               arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_TRANS,
               arithmeticTheory.LESS_IMP_LESS_OR_EQ])
 >- (simp [cget_net_var_Bin_SOME_eq] \\ metis_tac [])
 >- (gvs [cget_net_var_Bin_SOME_eq, optionTheory.IS_SOME_EXISTS, si_progress_def] \\ metis_tac []) \\

 strip_tac \\ rpt (first_x_assum (qspec_then `var` assume_tac)) \\ TOP_CASE_TAC

 >- (drule_strip cget_net_var_Bin_NONE \\ fs [])

 \\ drule_strip cget_net_var_Bin_SOME_imp \\ fs []

    >- (qspecl_then [`[tblock]`, `bigsi`] assume_tac si_lt_si_subset_si_lt \\ drule_first \\
        pop_assum (assume_tac o SIMP_RULE (srw_ss()) [si_lt_def]) \\ drule_first \\
        IF_CASES_TAC
        >- metis_tac [cells_run_unchanged_muxlist_ok, arithmeticTheory.LESS_EQ_REFL]
        \\ metis_tac [cells_run_unchanged_muxlist_ok_cget_net])

    >- (imp_res_tac cget_net_var_cget_net \\ rfs [sum_foldM_append, sum_bind_def] \\
       
       qspec_then `tblock'_si` assume_tac cells_run_unchanged_muxlist_ok_cget_net \\ drule_first \\
       impl_tac >- (match_mp_tac si_lt_le \\ asm_exists_tac \\ fs []) \\ strip_tac \\

       qspec_then `tblock'_si` assume_tac si_lt_not_eq_border_NetVar \\ drule_first \\ simp [] \\
       metis_tac [TEMPORARY_HACK])

    \\ imp_res_tac cget_net_var_SOME_cget_net \\ rfs [sum_foldM_append, sum_bind_def] \\

       qspec_then `VarInp (NetVar tblock'_cs.tmpnum) NoIndexing` assume_tac cells_run_unchanged_muxlist_ok \\
       drule_first \\

       disch_then (qspec_then `k_cs.tmpnum` mp_tac) \\
       impl_tac >- fs [cell_input_lt_def, var_lt_def, cstate_progress_def] \\ strip_tac \\ simp [] \\

       qspecl_then [`[Bin n k v tblock tblock']`, `bigsi`] assume_tac si_lt_si_subset_si_lt \\ drule_first \\
       pop_assum (assume_tac o SIMP_RULE (srw_ss()) [si_lt_def]) \\ drule_first \\
       metis_tac [cells_run_unchanged_muxlist_ok, arithmeticTheory.LESS_EQ_REFL,
                  cells_run_unchanged_muxlist_ok_cget_net]
QED

Triviality cget_net_var_NONE_cget_net_append_lem:
 ∀si1 si2 k. cget_net_var si1 k = NONE ⇒ ∃var. cget_net (si1 ⧺ si2) var = cget_net si2 k
Proof
 rpt strip_tac \\ qexists_tac ‘k’ \\ rw [cget_net_append]
QED

(* Might have some redundant assumptions... the thm stmt is based on the thm for _left, the proof as well *)
Theorem compile_merge_if_right_correct:
 !cond fallback othersi k v cs si nl cs' si' nl' min bigsi EE E cenv cenv' b fext.
 compile_merge_if_right cond fallback othersi k v (cs, si, nl) = (cs', si', nl') /\

 muxlist_ok EE cond min cs.tmpnum (othersi ++ fallback) bigsi nl /\
 netlist_sorted nl ∧
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 cstate_ok fext EE E cs cenv' /\
 cell_input_lt cond min /\
 cell_inp_run fext cenv cond = INR (CBool b) /\
 cell_input_covered_by_extenv EE cond ∧

 cget_net_var bigsi k = SOME v /\
 si_sound fext EE E cenv' bigsi /\ si_lt bigsi min /\
 si_sound fext EE E cenv' othersi /\ si_lt othersi min /\ (*si_complete fext E cenv' othersi /\*)
 si_wf si /\ si_sound fext EE E cenv' si /\ si_lt si cs.tmpnum /\ si_complete fext E cenv' si /\
 (* NEW: *) si_sound fext EE E cenv' fallback ∧ si_lt fallback min ∧ si_complete fext E cenv' fallback ∧
 
 min <= cs.tmpnum
 ==>
 cs'.bsi = cs.bsi /\ cs'.nbsi = cs.nbsi /\
 si_progress si si' /\
 cstate_progress cs cs' ∧
 muxlist_ok EE cond min cs'.tmpnum (othersi ++ fallback) bigsi nl' /\
 netlist_sorted nl' ∧
 ∃cenv''.
  sum_foldM (cell_run fext) cenv nl' = INR cenv'' /\
  cstate_ok fext EE E cs' cenv'' /\

  si_sound fext EE E cenv'' bigsi /\
  si_sound fext EE E cenv'' othersi /\ (*si_complete fext E cenv'' othersi /\*)
  si_sound fext EE E cenv'' fallback ∧ si_complete fext E cenv'' fallback ∧
  si_wf si' /\ si_sound fext EE E cenv'' si' /\ si_lt si' cs'.tmpnum /\ si_complete fext E cenv'' si' /\
  case cget_net_var othersi k of
    SOME _ => cs' = cs ∧ si' = si ∧ nl' = nl
  | NONE =>
   (!var. cget_net_var si' var =
          if var = k then SOME (VarInp (NetVar cs.tmpnum) NoIndexing) else cget_net_var si var) /\
   IS_SOME (cget_net_var [HD si'] k) ∧
   (* cstate_progress cs cs' <-- too weak here *) cs.tmpnum < cs'.tmpnum /\

   (?mcell. nl' = SNOC mcell nl /\ mux_ok EE cond cs.tmpnum cs'.tmpnum (othersi ++ fallback) bigsi mcell) /\

   cell_inp_run fext cenv'' (VarInp (NetVar cs.tmpnum) NoIndexing) =
    (if b then cell_inp_run fext cenv (cget_net fallback k) else cell_inp_run fext cenv v) ∧

   (!inp. ~cell_input_is_var inp (NetVar cs.tmpnum) ⇒
          cell_inp_run fext cenv'' inp = cell_inp_run fext cenv' inp)
Proof
 simp [compile_merge_if_right_def, compile_new_name_def] \\ rpt strip_tac' \\
 reverse TOP_CASE_TAC >- fs [si_progress_def, cstate_progress_def] \\ fs [] \\ rveq \\ simp [] \\ rpt strip_tac
 >- simp [si_progress_cset_net]
 >- simp [cstate_progress_def]
 >- (rw [muxlist_ok_append]
    >- (match_mp_tac muxlist_ok_le \\ asm_exists_tac \\ simp [])
    \\ rw [muxlist_ok_def]
       >- (rw [cell_covered_by_extenv_def] \\
           metis_tac [si_sound_def, si_sound_cell_input_covered_by_extenv_cget_net])
       \\ rw [mux_ok_def, cell_output_ok_def, mux_input_ok_def] \\
          metis_tac [cget_net_var_SOME_cget_net, 
                     si_lt_def, cell_input_lt_le, si_sound_def,
                     si_lt_cell_input_lt_cget_net,
                     cget_net_var_NONE_cget_net_append_lem])
 >- (drule_strip muxlist_ok_netlist_ok \\ drule_strip netlist_sorted_snoc \\ disch_then match_mp_tac \\
    simp [cell_output_def]) \\

 simp [sum_foldM_append, sum_bind_def, sum_foldM_def, cell_run_def] \\
 drule_strip cells_run_unchanged_muxlist_ok \\ impl_tac >- simp [] \\ strip_tac \\
 qspec_then ‘fallback’ assume_tac cells_run_unchanged_muxlist_ok_cget_net \\ drule_first \\
 qspec_then ‘v’ assume_tac cells_run_unchanged_muxlist_ok_cget_net_var \\ drule_first \\

 qpat_assum ‘si_sound _ _ _ _ bigsi’ (drule_strip o SIMP_RULE (srw_ss()) [si_sound_def]) \\
 qpat_assum ‘si_complete _ _ _ fallback’ (drule_strip o SIMP_RULE (srw_ss()) [si_complete_def]) \\
 imp_res_tac same_type_deterministic \\ rveq \\

 simp [sum_bind_def] \\
 qspecl_then [‘cv'’, ‘cv’, ‘b’] assume_tac cellMux_run_same_type \\ pop_assum drule_strip \\
 simp [sum_bind_def] \\

 rpt conj_tac
 >- (fs [cstate_ok_def] \\ metis_tac [si_lt_SUC, si_sound_cset_var, si_complete_cset_var, arithmeticTheory.LESS_EQ_REFL])
 >- metis_tac [si_sound_cset_var]
 >- metis_tac [si_sound_cset_var]
 >- metis_tac [si_sound_cset_var]
 >- metis_tac [si_complete_cset_var]
 >- simp [si_wf_cset_net]
 >- metis_tac [si_sound_cset_var_cset_net]
 >- metis_tac [si_lt_cset_net_SUC]
 >- metis_tac [si_complete_cset_var_cset_net]
 >- rw [cget_net_var_cset_net]
 >- rw [cget_net_var_cset_net, si_wf_HD, HD_cset_net]
 >- (rw [mux_ok_def, cell_output_ok_def, mux_input_ok_def] \\
     metis_tac [cget_net_var_SOME_cget_net, cell_input_lt_le, si_lt_def, si_lt_cell_input_lt_cget_net, cget_net_var_NONE_cget_net_append_lem])
 >- (rfs [cell_inp_run_cset_var] \\ rw [])
 \\ Cases \\ simp [cell_inp_run_def, cell_input_is_var_def, cget_var_cset_var]
QED

Theorem foldrWithKey_compile_merge_if_right_correct:
 !bigsi min fblock cond oldsi tblock si si' nl nl' cs cs' EE E cenv cenv' b fext.
 foldrWithKey (compile_merge_if_right cond oldsi [tblock]) (cs, si, nl) fblock = (cs', si', nl') /\

 (* have re-ordered assumptions here: *)
 sum_foldM (cell_run fext) cenv nl = INR cenv' /\
 cell_inp_run fext cenv cond = INR (CBool b) /\
 cell_input_covered_by_extenv EE cond ∧
 cstate_ok fext EE E cs cenv' /\
 muxlist_ok EE cond min cs.tmpnum (tblock::oldsi) bigsi nl /\
 netlist_sorted nl ∧
 cell_input_lt cond min /\

 si_wf [fblock] /\
 si_sound fext EE E cenv' bigsi /\ si_lt bigsi min /\
 si_sound fext EE E cenv' [tblock] /\ si_lt [tblock] min /\
 si_complete fext E cenv' oldsi /\ (* NEW: *) si_sound fext EE E cenv' oldsi ∧ si_lt oldsi min ∧
 si_subset [fblock] bigsi /\
 
 si_wf si /\ si_sound fext EE E cenv' si /\ si_lt si cs.tmpnum /\ si_complete fext E cenv' si /\

 min <= cs.tmpnum
 ==>
 cs'.bsi = cs.bsi /\ cs'.nbsi = cs.nbsi /\
 cstate_progress cs cs' /\
 si_progress si si' /\
 muxlist_ok EE cond min cs'.tmpnum (tblock::oldsi) bigsi nl' /\
 netlist_sorted nl' ∧
 (?nl''. nl' = nl ++ nl'' /\ muxlist_ok EE cond cs.tmpnum cs'.tmpnum (tblock::oldsi) bigsi nl'') /\
 (!var. (∃inp. cget_net_var si' var = SOME inp) ⇔
         (?inp. cget_net_var [tblock] var = NONE ∧ cget_net_var [fblock] var = SOME inp) \/
         (?inp. cget_net_var si var = SOME inp)) /\
 (∀var. cget_net_var [tblock] var = NONE ∧ IS_SOME (cget_net_var [fblock] var) ⇒ IS_SOME (cget_net_var [HD si'] var)) ∧
 ?cenv''.
  sum_foldM (cell_run fext) cenv nl' = INR cenv'' /\

  si_sound fext EE E cenv'' bigsi /\
  si_sound fext EE E cenv'' [tblock] /\
  si_sound fext EE E cenv'' oldsi /\
  si_complete fext E cenv'' oldsi /\

  cstate_ok fext EE E cs' cenv'' /\
  si_wf si' /\ si_sound fext EE E cenv'' si' /\ si_lt si' cs'.tmpnum /\ si_complete fext E cenv'' si' /\

  !var. case cget_net_var [fblock] var of
          NONE => cget_net_var si' var = cget_net_var si var
        | SOME inp => case cget_net_var [tblock] var of
                             NONE => cell_inp_run fext cenv'' (cget_net si' var) =
                                      if b then cell_inp_run fext cenv' (cget_net oldsi var)
                                           else cell_inp_run fext cenv' inp
                           | SOME inp => cget_net_var si' var = cget_net_var si var
Proof
 (* Essentially copy of above _left proof, except much messier *)
 ntac 2 gen_tac \\ Induct
 >- (rw [foldrWithKey_def, cstate_progress_def, si_progress_def, GSYM empty_def, cget_net_var_empty] \\
     simp [muxlist_ok_def]) \\

 rewrite_tac [foldrWithKey_def] \\ rpt strip_tac' \\
 drule_strip si_wf_Bin \\ drule_strip si_subset_Bin \\

 (* first: *)
 namedCases_on `foldrWithKey (compile_merge_if_right cond oldsi [tblock]) (cs,si,nl) fblock'`
               ["fblock'_cs fblock'_si fblock'_nl"] \\
 drule_first \\ rveq \\

 (* middle: *)
 namedCases_on `compile_merge_if_right cond oldsi [tblock] k v (fblock'_cs,fblock'_si,nl ⧺ nl'')`
               ["k_cs k_si k_nl"] \\
 drule_strip compile_merge_if_right_correct \\ simp [] \\ disch_then drule_strip \\
 impl_tac >- fs [cstate_progress_def] \\ strip_tac \\

 (* third: *)
 drule_first \\ impl_tac >- fs [cstate_progress_def] \\ strip_tac \\ rveq \\
 
 simp [] \\ rpt conj_tac
 >- fs [cstate_progress_def]
 >- fs [si_progress_def]
 >- (Cases_on ‘cget_net_var [tblock] k’ \\ fs [] \\ rveq \\
     fs [muxlist_ok_append, SNOC_APPEND, muxlist_ok_cons, cstate_progress_def] \\
     metis_tac [mux_ok_le, muxlist_ok_le, muxlist_ok_nil,
                arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_TRANS,
                arithmeticTheory.LESS_IMP_LESS_OR_EQ])
 >- (rpt strip_tac \\ Cases_on ‘cget_net_var [tblock] k’ \\ fs [] \\ rveq \\
     simp [cget_net_var_Bin_SOME_eq] >- metis_tac [] \\
     eq_tac \\ rw [] \\ gvs [Case_option] \\ metis_tac [])
 >- (rpt strip_tac \\ gs [cget_net_var_Bin_SOME_eq, optionTheory.IS_SOME_EXISTS, si_progress_def]) \\

 strip_tac \\ rpt (first_x_assum (qspec_then `var` assume_tac)) \\ TOP_CASE_TAC

 >- (drule_strip cget_net_var_Bin_NONE \\ Cases_on ‘cget_net_var [tblock] k’ \\ fs [])

 \\ drule_strip cget_net_var_Bin_SOME_imp \\ fs []

 >- (qspecl_then [`[fblock]`, `bigsi`] assume_tac si_lt_si_subset_si_lt \\ drule_first \\
     pop_assum (assume_tac o SIMP_RULE (srw_ss()) [si_lt_def]) \\ drule_first \\
     TOP_CASE_TAC
     >- (IF_CASES_TAC \\ fs []
         >- (qspecl_then [‘oldsi’, ‘cenv’, ‘cenv'⁵'’] assume_tac cells_run_unchanged_muxlist_ok_cget_net \\
             drule_first \\
             qspecl_then [‘oldsi’, ‘cenv’, ‘cenv'’] assume_tac cells_run_unchanged_muxlist_ok_cget_net \\
             drule_first \\ simp [])
         >- metis_tac [cells_run_unchanged_muxlist_ok, arithmeticTheory.LESS_EQ_REFL])
     \\ Cases_on ‘cget_net_var [tblock] k’ \\ fs [])

 >- (imp_res_tac cget_net_var_cget_net \\
     ‘cget_net k_si var = cget_net fblock'_si var’
     by (Cases_on ‘cget_net_var [tblock] k’ \\ fs [cget_net_def]) \\
     rfs [sum_foldM_append, sum_bind_def] \\

     qspec_then `fblock'_si` assume_tac cells_run_unchanged_muxlist_ok_cget_net \\ drule_first \\
     impl_tac >- (match_mp_tac si_lt_le \\ asm_exists_tac \\ fs [cstate_progress_def]) \\ strip_tac \\

     qspec_then `fblock'_si` assume_tac si_lt_not_eq_border_NetVar \\ drule_first \\ simp [] \\
     Cases_on ‘cget_net_var [tblock] k’ \\ fs [] \\ rveq \\ rfs [sum_foldM_append, sum_bind_def] \\
     metis_tac [TEMPORARY_HACK])

 \\ TOP_CASE_TAC \\ fs [] \\ rveq \\
    imp_res_tac cget_net_var_SOME_cget_net \\ rfs [sum_foldM_append, sum_bind_def] \\

    qspec_then `VarInp (NetVar fblock'_cs.tmpnum) NoIndexing` assume_tac cells_run_unchanged_muxlist_ok \\
    drule_first \\

    disch_then (qspec_then `k_cs.tmpnum` mp_tac) \\
    impl_tac >- fs [cell_input_lt_def, var_lt_def, cstate_progress_def] \\ strip_tac \\ simp [] \\

    qspecl_then [`[Bin n k v fblock fblock']`, `bigsi`] assume_tac si_lt_si_subset_si_lt \\ drule_first \\
    pop_assum (assume_tac o SIMP_RULE (srw_ss()) [si_lt_def]) \\ drule_first \\
    metis_tac [cells_run_unchanged_muxlist_ok, arithmeticTheory.LESS_EQ_REFL,
               cells_run_unchanged_muxlist_ok_cget_net]
QED

(*Theorem si_wf_cons:
 !b bs. si_wf (b::bs) ==> si_wf [b] /\ si_wf bs
Proof
 rw [si_wf_def]
QED*)

Theorem si_sound_cons:
 !fext EE E cenv b bs.
  si_sound fext EE E cenv [b] /\ si_sound fext EE E cenv bs ==> si_sound fext EE E cenv (b::bs)
Proof
 simp [si_sound_def, cget_net_var_singleton] \\ simp [cget_net_var_def] \\ rpt strip_tac' \\
 pop_assum mp_tac \\ TOP_CASE_TAC \\ strip_tac \\ rveq \\ drule_first \\ simp [] \\ rpt asm_exists_tac
QED

Theorem si_sound_cons_hd:
 !fext EE E cenv b bs. si_sound fext EE E cenv (b::bs) ==> si_sound fext EE E cenv [b]
Proof
 simp [si_sound_def, cget_net_var_singleton] \\ simp [cget_net_var_def] \\ rpt strip_tac' \\
 first_x_assum (qspec_then `var` mp_tac) \\ simp []
QED

Theorem si_lt_cons_hd:
 !b bs n. si_lt (b::bs) n ==> si_lt [b] n
Proof
 simp [si_lt_def, cget_net_var_singleton] \\ simp [cget_net_var_def] \\ rpt strip_tac' \\
 first_x_assum (qspec_then `var` mp_tac) \\ simp []
QED

Theorem si_sound_cons_si_complete_si_complete:
 !fext EE E cenv b bs.
  si_sound fext EE E cenv [b] /\ si_complete fext E cenv bs ==> si_complete fext E cenv (b::bs)
Proof
 simp [si_sound_def, si_complete_def] \\ rpt strip_tac' \\
 simp [cget_net_def, cget_net_var_def] \\ every_case_tac
 >- (drule_first \\ rfs [cget_net_def] \\ rpt asm_exists_tac)
 >- (drule_first \\ drule_strip cget_net_var_SOME_cget_net \\ simp [] \\ rpt asm_exists_tac)
 \\ (drule_first \\ fs [cget_net_var_singleton] \\ drule_first \\ fs [] \\ rfs [] \\ rpt asm_exists_tac)
QED

Theorem compile_merge_if_correct:
 !cs cenv si cond tblock fblock cs' si' nl EE E b fext.
 compile_merge_if cs si cond tblock fblock = (cs', si', nl) /\

 cell_inp_run fext cenv cond = INR (CBool b) /\
 cell_input_lt cond cs.tmpnum /\
 cell_input_covered_by_extenv EE cond ∧

 si_wf (tblock::si) /\ (* <-- more than needed *)
 si_wf (fblock::si) /\ (* <-- more than needed *)
 si_wf si /\

 si_lt (tblock::si) cs.tmpnum /\ (* <-- more than needed *)
 si_lt (fblock::si) cs.tmpnum /\ (* <-- more than needed *)
 si_lt si cs.tmpnum /\

 si_sound fext EE E cenv (tblock::si) /\
 si_sound fext EE E cenv (fblock::si) /\
 si_sound fext EE E cenv si /\

 si_complete fext E cenv si /\

 cstate_ok fext EE E cs cenv ==>
 cs'.bsi = cs.bsi /\ cs'.nbsi = cs.nbsi /\ (* <-- are these two needed? probably instead for sis_progress *)
 cstate_progress cs cs' /\
 si_progress si si' /\
 muxlist_ok EE cond cs.tmpnum cs'.tmpnum (tblock::si) (fblock::si) nl /\
 netlist_sorted nl ∧
 (!var inp. cget_net_var si' var = SOME inp ==>
            (?inp. cget_net_var [tblock] var = SOME inp) \/
            (?inp. cget_net_var [fblock] var = SOME inp) \/
            (?inp. cget_net_var si var = SOME inp)) /\
 (∀var. IS_SOME (cget_net_var [tblock] var) ∨ IS_SOME (cget_net_var [fblock] var) ⇒
        IS_SOME (cget_net_var [HD si'] var)) ∧
 ?cenv'. sum_foldM (cell_run fext) cenv nl = INR cenv' /\
         cstate_ok fext EE E cs' cenv' /\
         si_wf si' /\ si_lt si' cs'.tmpnum /\ si_sound fext EE E cenv' si' /\ si_complete fext E cenv' si' /\
         (!var. cell_inp_run fext cenv' (cget_net si' var) =
            if b then
             cell_inp_run fext cenv (cget_net (tblock::si) var)
            else
             cell_inp_run fext cenv (cget_net (fblock::si) var))
Proof
 simp [compile_merge_if_def] \\ rpt strip_tac' \\ pairarg_tac \\ fs [] \\
 imp_res_tac si_wf_cons_hd \\

 qspec_then `tblock::si` assume_tac foldrWithKey_compile_merge_if_left_correct \\ drule_first \\
 simp [sum_foldM_def, muxlist_ok_nil, si_subset_cons, netlist_sorted_nil] \\
 impl_tac >- metis_tac [si_sound_cons_hd, si_sound_cons_si_complete_si_complete] \\ strip_tac \\
 
 drule_strip foldrWithKey_compile_merge_if_right_correct \\ impl_tac
 >- (fs [cstate_progress_def, si_subset_cons] \\
     metis_tac [si_sound_cons_hd, si_lt_cons_hd,
                cells_run_si_complete, cells_run_si_sound, 
                muxlist_ok_netlist_ok, arithmeticTheory.LESS_EQ_REFL]) \\ strip_tac \\
 fs [] \\ rveq \\ rfs [sum_foldM_append, sum_bind_def] \\

 rpt conj_tac
 >- fs [cstate_progress_def]
 >- fs [si_progress_def]
 >- metis_tac []
 >- (rpt strip_tac \\ Cases_on ‘cget_net_var [tblock] var’ \\ fs [si_progress_def, optionTheory.IS_SOME_EXISTS]) \\
 
 gen_tac \\
 rpt (first_x_assum (qspec_then `var` assume_tac)) \\
 Cases_on `cget_net_var [tblock] var` \\ Cases_on `cget_net_var [fblock] var` \\
 imp_res_tac cget_net_cons_NONE \\ imp_res_tac cget_net_cons_SOME \\ fs [] \\
 imp_res_tac cget_net_var_cget_net \\ simp [] \\
 metis_tac [cells_run_unchanged_muxlist_ok_cget_net]
QED

Theorem ndetcell_run_nd_reset_same_fbits:
 !t cenv cenv' rtlv vs vs' v v'.
 ndetcell_run cenv (compile_type t) = (cenv', rtlv) /\
 nd_reset (vs with fbits := cenv.fbits) v = (vs', v') /\
 vertype_v v t ==>
 (?fbits. vs' = vs with fbits := fbits) /\ same_value v' rtlv
Proof
 Cases \\ simp [ndetcell_run_def, compile_type_def, vertype_v_cases] \\
 rpt strip_tac' \\ rveq \\ fs [nd_reset_def] \\ pairarg_tac \\ fs [] \\ rw [same_value_def] \\
 metis_tac []
QED

Triviality writes_ok_with_vnwrites_so_bsi_is_NONE:
 !ps cs var.
 writes_ok ps /\ writes_ok_sis ps cs /\ MEM var (FLAT (MAP vnwrites ps)) ==> cget_net_var cs.bsi var = NONE
Proof
 rw [writes_ok_def, writes_ok_sis_def] \\ Cases_on ‘cget_net_var cs.bsi var’ >- simp [] \\ drule_first \\ metis_tac []
QED

Theorem same_state_sis_get_use_nbq_var:
 !b var ps cs fext vs vv rv_bsi rv_nbsi cenv.
 writes_ok ps /\
 writes_ok_sis ps cs /\
 
 same_state_sis fext vs cs cenv /\
 get_use_nbq_var vs b var = INR vv /\
 cell_inp_run fext cenv (cget_net cs.bsi var) = INR rv_bsi /\
 cell_inp_run fext cenv (cget_net cs.nbsi var) = INR rv_nbsi ==>
 if ~b then
  same_value vv rv_bsi
 else if MEM var (FLAT (MAP vnwrites ps)) then
  same_value vv rv_nbsi
 else
  T
Proof
 rw [same_state_sis_def, same_state_bsi_def, same_state_nbsi_def,
     GSYM get_var_sum_alookup, GSYM get_nbq_var_sum_alookup, get_use_nbq_var_def, CaseEq "sum"] \\
 rpt drule_first
 >- (drule_strip writes_ok_with_vnwrites_so_bsi_is_NONE \\ drule_strip cget_net_var_NONE_cget_net \\ fs [] \\ rfs [])
 \\ rfs []
QED

(*Triviality allowed_to_fail_rewrite:
 ∀P x. (case x of INL e => T | INR x => P x) ⇔ ∀x'. x = INR x' ⇒ P x'
Proof
 rpt gen_tac \\ TOP_CASE_TAC
QED*)

Theorem compile_stmt_correct:
 !ps p cenv EEv Ev cs cs' nl vfext rtlfext.
  compile_stmt cs p = INR (cs', nl) /\
  vertype_stmt EEv Ev p /\
  vertype_fext_n EEv vfext /\
  no_array_write_dyn Ev p /\
  no_array_read_dyn Ev EEv p /\
  no_Case p /\

  same_fext_n vfext rtlfext /\

  cstate_ok rtlfext EEv Ev cs cenv /\

  (!var. MEM var (vwrites p) ==> MEM var (FLAT (MAP vwrites ps))) /\
  (!var. MEM var (vnwrites p) ==> MEM var (FLAT (MAP vnwrites ps))) /\
  writes_ok ps /\
  writes_ok_sis ps cs
  ==>
  cstate_progress cs cs' /\
  sis_progress cs cs' /\
  writes_ok_sis ps cs' /\
  (∀var. MEM var (vwrites p) ⇒ IS_SOME (cget_net_var [HD cs'.bsi] var)) ∧
  netlist_ok EEv cs.tmpnum cs'.tmpnum nl /\
  netlist_sorted nl /\
  ?cenv'. sum_foldM (cell_run rtlfext) cenv nl = INR cenv' /\
          cstate_ok rtlfext EEv Ev cs' cenv' /\
          (!vs. ?fbits.
            case prun vfext (vs with fbits := fbits) p of
              INL e => T
            | INR vs' => same_state_sis rtlfext vs cs cenv /\ vertype_env Ev vs ==>
                         same_state_sis rtlfext vs' cs' cenv')
Proof
 gen_tac \\ Induct

 >- (* Skip *)
 (rw [prun_def, compile_stmt_def, vwrites_def] \\
 rw [cstate_progress_def, sis_progress_def, si_progress_def, netlist_ok_def, netlist_sorted_def, sum_foldM_def] \\
 qexists_tac `vs.fbits` \\ rw [pstate_fbits_fbits] \\ simp [])

 >- (* Seq *)
 (simp [compile_stmt_def, sum_bind_INR, no_array_write_dyn_def, no_array_read_dyn_def, no_Case_def, vwrites_def, vnwrites_def] \\
 rpt strip_tac' \\
 qpat_x_assum `vertype_stmt _ _ _`
              (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\ rveq \\
 rpt (pairarg_tac \\ rveq \\ fs [sum_bind_INR]) \\ drule_last \\ drule_first \\ rveq \\
 rpt conj_tac
 >- fs [cstate_progress_def]
 >- fs [sis_progress_def, si_progress_def]
 >- fs [writes_ok_sis_def]
 >- (fs [sis_progress_def, si_progress_def] \\ metis_tac [])
 >- (fs [cstate_progress_def, netlist_ok_append] \\ 
    conj_tac \\ match_mp_tac netlist_ok_le \\ asm_exists_tac \\ DECIDE_TAC)
 >- metis_tac [netlist_sorted_append] \\

 simp [sum_foldM_append, sum_bind_def] \\ rw [prun_def] \\
 last_x_assum (qspec_then `vs` strip_assume_tac) \\
 pop_assum mp_tac \\ TOP_CASE_TAC >- (qexists_tac `fbits` \\ simp [sum_bind_def]) \\ strip_tac \\
 drule_strip prun_fbits \\
 first_x_assum (qspec_then `y` strip_assume_tac) \\
 qexists_tac `\t. if t < n then fbits t else fbits' (t - n)` \\
 first_x_assum (qspec_then `\t. if t < n then fbits t else fbits' (t - n)` mp_tac) \\
 impl_tac >- simp [init_seq_eq_def] \\ simp [pstate_component_equality, sum_bind_def, shift_seq_if_lt] \\
 strip_tac \\ CASE_TAC \\ fs [] \\ metis_tac [vertype_stmt_prun, vertype_env_fbits])
    
 >- (* IfElse *)
 (rename1 `IfElse _ tb fb` \\
 simp [compile_stmt_def, sum_bind_INR, no_array_write_dyn_def, no_array_read_dyn_def, no_Case_def, vwrites_def, vnwrites_def] \\
 rpt strip_tac' \\
 qpat_x_assum `vertype_stmt _ _ _`
              (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\

 rpt (pairarg_tac \\ rveq \\ fs [sum_bind_INR]) \\
 drule_strip compile_exp_correct \\
 fs [same_type_cases, rtltype_v_ground_cases] \\ rveq \\

 (* push *)
 qspec_then `s'` assume_tac new_block_correct \\ drule_first \\
 (* compile true branch *)
 drule_last \\
 drule_strip cells_run_unchanged_netlist_ok \\ impl_tac >- fs [cstate_progress_def] \\ strip_tac \\
 (* pop *)
 qspec_then `s'` assume_tac pop_block_correct \\ drule_first \\
 (* push *)
 drule_strip new_block_correct \\
 (* compile false branch *)
 drule_first \\
 drule_strip cells_run_unchanged_netlist_ok \\ impl_tac >- fs [cstate_progress_def] \\ strip_tac \\
 (* pop *)
 drule_strip pop_block_correct \\

 rfs [] \\

 (* blocking merge if *)
 qspec_then `s'⁶'` assume_tac compile_merge_if_correct \\ drule_first \\ 
 disch_then (qspecl_then [‘EEv’, ‘Ev’] mp_tac) \\ impl_tac
 >- (fs [cstate_progress_def, cstate_ok_def] \\ rpt conj_tac
  >- (match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])
  >- (match_mp_tac si_lt_le \\ asm_exists_tac \\ simp [])
  >- (match_mp_tac si_lt_le \\ asm_exists_tac \\ simp [])
  \\ match_mp_tac cells_run_si_sound \\ rpt asm_exists_tac \\ simp []) \\ strip_tac \\
 drule_strip cells_run_unchanged_muxlist_ok \\ impl_tac >- fs [cstate_progress_def] \\ simp [] \\ strip_tac \\
 drule_strip muxlist_ok_netlist_ok \\

 (* non-blocking merge if, TODO: ugly automation here... *)
 drule_strip compile_merge_if_correct \\ disch_then (qspecl_then [‘EEv’, ‘Ev’] mp_tac) \\ impl_tac
 >- (fs [cstate_progress_def, cstate_ok_def] \\ imp_res_tac muxlist_ok_netlist_ok \\
     rpt conj_tac \\
     rpt (TRY (match_mp_tac si_lt_append) \\
     TRY (match_mp_tac si_sound_append) \\
     TRY (match_mp_tac si_complete_append) \\
     TRY (match_mp_tac cells_run_si_sound) \\
     TRY (match_mp_tac cells_run_si_complete) \\
     TRY (match_mp_tac si_lt_le) \\
     TRY (match_mp_tac cell_input_lt_le) \\
     rpt conj_tac \\ rpt asm_exists_tac \\ simp [])) \\ strip_tac \\
 drule_strip muxlist_ok_netlist_ok \\

 rpt conj_tac
 >- fs [cstate_progress_def]
 >- rfs [sis_progress_def]
 >- (fs [writes_ok_sis_def] \\ rpt strip_tac \\ drule_first \\ metis_tac [cget_net_var_cons_SOME])
 >- (gvs [sis_progress_def, si_progress_def] \\ metis_tac [HD])
 >- (fs [netlist_ok_append, cstate_progress_def] \\
     rpt conj_tac \\ match_mp_tac netlist_ok_le \\ asm_exists_tac \\ DECIDE_TAC)
 >- (rpt (match_mp_tac (INST_TYPE [alpha |-> “:vertype”] netlist_sorted_append) \\ rpt asm_exists_any_tac \\
         qexists_tac ‘cs.tmpnum’ \\
         simp [netlist_ok_append] \\
         rpt conj_tac \\ TRY (match_mp_tac netlist_ok_le \\ asm_exists_tac \\ fs [cstate_progress_def]))) \\

 simp [sum_foldM_append, sum_bind_def] \\

 conj_tac
 >- (fs [cstate_ok_def, cstate_progress_def] \\ rpt conj_tac
     >- metis_tac [si_lt_le] (* overkill? *)
     >- (match_mp_tac cells_run_si_sound \\ rpt asm_exists_tac \\ simp [])
     \\ match_mp_tac cells_run_si_complete \\ rpt asm_exists_any_tac \\ simp []) \\

 rpt strip_tac \\

 simp [prun_def, erun_fbits] \\ Cases_on `erun vfext vs e` \\ simp [sum_bind_def] \\
 (* could probably use type information here if we wanted to: *)
 Cases_on `y` \\ fs [get_VBool_data_def, sum_bind_def] \\
 drule_first \\ strip_tac \\ Cases_on `b'` \\

 simp [] >| [last_x_assum (qspec_then `vs` strip_assume_tac),
             first_x_assum (qspec_then `vs` strip_assume_tac)] \\
 qexists_tac `fbits` \\ CASE_TAC \\ strip_tac \\
 drule_first \\ fs [same_value_def] \\ rveq \\

 qpat_x_assum `_ ==> _` mp_tac \\ fs [same_state_sis_def]

 (* messy "lifting" proof: *)
 (*Cases_on `b` \\ fs []*)
 >-
 ((*drule_first \\*)
 impl_tac >- (fs [cstate_progress_def] \\ metis_tac [same_state_bsi_same_si, same_state_nbsi_same_si]) \\
 strip_tac \\ rfs [] \\

 qspecl_then [`bsi`, `cenv'⁴'`] assume_tac cells_run_unchanged_netlist_ok_cget_net \\ drule_first \\
 (*impl_tac >- (fs [cstate_ok_def, cstate_progress_def] \\ metis_tac [si_sound_si_lt, si_lt_le]) \\ strip_tac \\*)

 qspecl_then [`s'³'.nbsi`, `cenv'³'`] assume_tac cells_run_unchanged_netlist_ok_cget_net \\ drule_first \\
 impl_tac >- (fs [cstate_ok_def, cstate_progress_def] \\ metis_tac [si_lt_le]) \\ strip_tac \\

 qspecl_then [`s'³'.bsi`, `cenv''`] assume_tac cells_run_unchanged_netlist_ok_cget_net \\ drule_first \\
 impl_tac >- (fs [cstate_ok_def, cstate_progress_def] \\ metis_tac [si_lt_le]) \\ strip_tac \\
 
 qspecl_then [`s'³'.nbsi`, `cenv''`] assume_tac cells_run_unchanged_netlist_ok_cget_net \\ drule_first \\
 impl_tac >- (fs [cstate_ok_def, cstate_progress_def] \\ metis_tac [si_lt_le]) \\ strip_tac \\

 fs [same_state_bsi_def, same_state_nbsi_def] \\
 simp [cell_inp_run_def] \\ metis_tac [cells_run_cget_var_RegVar])

 \\
 ((*drule_first \\*) impl_tac >- 
 (qspecl_then [`cs.bsi`, `cenv'`] assume_tac cells_run_unchanged_netlist_ok_cget_net \\ drule_first \\
 impl_tac >- (fs [cstate_ok_def, cstate_progress_def] \\ metis_tac [si_lt_le]) \\ strip_tac \\

 qspecl_then [`cs.nbsi`, `cenv'`] assume_tac cells_run_unchanged_netlist_ok_cget_net \\ drule_first \\
 impl_tac >- (fs [cstate_ok_def, cstate_progress_def] \\ metis_tac [si_lt_le]) \\ strip_tac \\

 fs [same_state_bsi_def, same_state_nbsi_def] \\
 metis_tac [cell_inp_run_def, cells_run_cget_var_RegVar, cget_net_var_cget_net]) \\ strip_tac \\

 qspecl_then [`bsi`, `cenv'⁴'`] assume_tac cells_run_unchanged_netlist_ok_cget_net \\ drule_first \\
 (*impl_tac >- (fs [cstate_ok_def, cstate_progress_def] \\ metis_tac [si_lt_le]) \\ strip_tac \\*)

 qspecl_then [`s.nbsi`, `cenv'³'`] assume_tac cells_run_unchanged_netlist_ok_cget_net \\ drule_first \\
 impl_tac >- (fs [cstate_ok_def, cstate_progress_def] \\ metis_tac [si_lt_le]) \\ strip_tac \\

 fs [same_state_bsi_def, same_state_nbsi_def] \\
 simp [cell_inp_run_def] \\ metis_tac [cells_run_cget_var_RegVar]))

 >- (* Case *)
 simp [no_Case_def]

 \\ (* BlockingAssign and NonBlockingAssign *)
 (rpt strip_tac' \\ TRY (rename1 ‘BlockingAssign wspec _’) \\ TRY (rename1 ‘NonBlockingAssign wspec _’) \\ Cases_on ‘wspec’

 >- (* NoIndexing *)
 (qpat_x_assum `vertype_stmt _ _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\ rveq \\
 fs [compile_stmt_def, compile_new_name_def, sum_bind_INR, no_array_write_dyn_def, no_array_read_dyn_def] \\
 TRY (pairarg_tac \\ rveq \\ fs [] \\ drule_strip compile_exp_correct) \\ rveq \\
  
 (rpt conj_tac
 >- fs [cstate_progress_def]
 >- (fs [cstate_ok_def, sis_progress_def, si_progress_cset_net] \\ simp [si_progress_def]) 
 >- (fs [writes_ok_sis_def, vwrites_def, vnwrites_def, evwrites_def, cstate_ok_def, cget_net_var_cset_net] \\ rw [] \\ rw [])
 >- fs [cstate_ok_def, vwrites_def, evwrites_def, HD_cset_net, cget_net_var_cset_net, si_wf_HD]
 >- fs [netlist_ok_def, cell_ok_def, cell_output_ok_def, cell_covered_by_extenv_def]
 >- fs [netlist_sorted_def, cell_output_def])

 >- (* X case *)
 (drule_strip cstate_ok_vertypes \\
 simp [sum_foldM_def, cell_run_def] \\ qspecl_then [‘compile_type t’, ‘cenv’] strip_assume_tac ndetcell_run_type \\
 simp [sum_bind_def] \\ conj_tac
 >- (fs [cstate_ok_def, cset_var_fbits, si_sound_fbits, si_complete_fbits] \\ rpt conj_tac \\
     metis_tac [si_wf_cset_net, si_lt_cset_net_SUC, si_lt_SUC,
                compile_type_correct, si_sound_cset_var_cset_net, si_complete_cset_var_cset_net,
                si_sound_cset_var, si_complete_cset_var, arithmeticTheory.LESS_EQ_REFL]) \\
 gen_tac \\ qexists_tac `cenv.fbits` \\ CASE_TAC \\ rpt strip_tac \\
 fs [prun_def, sum_bind_INR, sum_map_INR, prun_assn_rhs_def, prun_assn_lhs_prev_def, get_var_fbits] \\
 pairarg_tac \\ rveq \\ fs [] \\ drule_strip vertype_env_get_var_type \\
 drule_strip ndetcell_run_nd_reset_same_fbits \\
 fs [prun_bassn_def, prun_nbassn_def, sum_for_INR, assn_def] \\ rveq \\
 fs [same_state_sis_def, same_state_bsi_def, same_state_nbsi_def,
     GSYM get_var_sum_alookup, GSYM get_nbq_var_sum_alookup, get_var_cleanup,
     cstate_ok_def, cget_net_cset_net] \\
 fs [cset_var_fbits, cell_inp_run_fbits, get_var_fbits, get_nbq_var_fbits] \\
 rw [cell_inp_run_cset_var_cget_net_spec, cell_inp_run_def, cget_var_cset_var, sum_bind_def, cget_fext_var_def] \\
 rw [])

 \\ (* value case: *)
 asm_exists_tac \\
 conj_tac >- (fs [cstate_ok_def] \\
              metis_tac [si_wf_cset_net, si_lt_cset_net, si_sound_cset_net, si_complete_cset_net]) \\

 rpt strip_tac \\ qexists_tac ‘vs.fbits’ \\ simp [pstate_fbits_fbits] \\ TOP_CASE_TAC \\ strip_tac \\
 fs [prun_def, prun_assn_rhs_def, prun_bassn_def, prun_nbassn_def, assn_def, sum_bind_INR, sum_map_INR, sum_for_def, sum_map_def] \\
 rveq \\ fs [] \\ rveq \\
 drule_first \\ fs [cstate_ok_def, same_state_sis_def, set_var_const, set_nbq_var_const] \\
 metis_tac [same_state_bsi_set_var, same_state_nbsi_set_nbq_var])

 >- (* Indexing *)
 (qpat_x_assum `vertype_stmt _ _ _`
               (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]) \\ rveq \\
 fs [no_array_write_dyn_def, no_array_read_dyn_def] \\
 every_case_tac \\ fs [sum_bind_INR, get_const_INR] \\ rveq \\
 fs [compile_stmt_def, sum_bind_INR] \\
 pairarg_tac \\ rveq \\ drule_strip compile_exp_correct \\
 fs [compile_new_name_def, sum_bind_def] \\ rveq \\

 (* Copied from NoIndexing case (except netlist_ok+netlist_sorted case): *)
 (rpt conj_tac
 >- fs [cstate_progress_def]
 >- (fs [cstate_ok_def, sis_progress_def, si_progress_cset_net] \\ simp [si_progress_def])
 >- (fs [writes_ok_sis_def, vwrites_def, vnwrites_def, evwrites_def, cstate_ok_def,
        cget_net_var_cset_net] \\ rw [] \\ rw [])
 >- fs [cstate_ok_def, vwrites_def, evwrites_def, HD_cset_net, cget_net_var_cset_net, si_wf_HD]
 >- (simp [netlist_ok_append] \\ conj_tac
     >- (match_mp_tac netlist_ok_le \\ asm_exists_tac \\ simp [])
     \\ fs [netlist_ok_def, cell_ok_def, cell_output_ok_def, cstate_progress_def, cell_covered_by_extenv_def, cstate_ok_def] \\
        metis_tac [si_sound_cell_input_covered_by_extenv_cget_net, si_lt_cell_input_lt_cget_net])
 >- (qspec_then ‘EEv’ match_mp_tac netlist_sorted_snoc \\ asm_exists_tac \\ simp [cell_output_def])) \\

 simp [sum_foldM_append, sum_bind_def] \\
 fs [sum_foldM_def, cell_run_def, sum_bind_INR, cstate_ok_def] \\
 qpat_assum ‘si_complete _ _ _ s'.bsi’ (assume_tac o SIMP_RULE (srw_ss()) [si_complete_def]) \\ drule_first \\
 qpat_assum ‘si_complete _ _ _ s'.nbsi’ (assume_tac o SIMP_RULE (srw_ss()) [si_complete_def]) \\ drule_first \\
 rfs [same_type_cases] \\ rveq \\ fs [rtltype_v_cases] \\ rveq \\
 simp [cellArrayWrite_run_def] \\

 simp [si_wf_cset_net, si_lt_cset_net_SUC, si_lt_SUC, si_sound_cset_var_spec, si_complete_cset_var_spec] \\ rpt conj_tac
 >- (match_mp_tac si_sound_cset_var_cset_net \\ rpt asm_exists_tac \\ rw [rtltype_v_cases, same_type_def])
 >- (match_mp_tac si_complete_cset_var_cset_net \\ rpt asm_exists_tac \\ rw [rtltype_v_cases, same_type_def]) \\
 
 rpt strip_tac \\ qexists_tac `vs''.fbits` \\ simp [pstate_fbits_fbits] \\ TOP_CASE_TAC \\
 fs [prun_def, prun_assn_rhs_def, sum_bind_INR, sum_map_INR] \\ rveq \\
 fs [prun_bassn_def, prun_nbassn_def, assn_def, sum_for_INR, sum_bind_INR, erun_def] \\
 fs [get_VBool_data_INR, get_VArray_data_INR] \\ pairarg_tac \\ rveq \\
 fs [prun_set_var_index_INR] \\ rveq \\ strip_tac \\ drule_first \\ fs [same_value_def] \\ rveq \\

 fs [vnwrites_def, evwrites_def] \\ drule_strip same_state_sis_get_use_nbq_var \\ simp [same_value_def] \\ strip_tac \\ rveq \\

 fs [same_state_sis_def] \\ conj_tac
 >- (fs [same_state_bsi_def, GSYM get_var_sum_alookup, get_var_cleanup] \\ rpt gen_tac \\
    qpat_x_assum ‘si_lt cs.bsi cs.tmpnum’ assume_tac \\ drule_strip cells_run_unchanged_netlist_ok_cget_net \\
    (* For blocking case: *)
    TRY (IF_CASES_TAC \\ simp [] \\ strip_tac \\ rveq
         >- (fs [cget_net_cset_net, cell_inp_run_cset_var] \\ simp [same_value_def])
         \\ simp [cget_net_cset_net, cell_inp_run_cset_var_cget_net]) \\
    (* For non-blocking case: *)
    simp [cell_inp_run_cset_var_cget_net_spec, cell_inp_run_cset_var] \\
    drule_strip cells_run_cell_inp_run_RegVar \\ simp [])
 \\ fs [same_state_nbsi_def, GSYM get_nbq_var_sum_alookup, get_var_cleanup, set_var_const, set_nbq_var_const] \\
    qpat_x_assum ‘si_lt cs.nbsi cs.tmpnum’ assume_tac \\ drule_strip cells_run_unchanged_netlist_ok_cget_net \\
    (* For non-blocking case: *)
    TRY (conj_tac \\ rw []
         >- (fs [cget_net_cset_net, cell_inp_run_cset_var] \\ simp [same_value_def])
         >- simp [cget_net_cset_net, cell_inp_run_cset_var_cget_net_spec]
         \\ fs [cget_net_cset_net, cell_inp_run_cset_var] \\
            qpat_x_assum ‘si_lt cs.nbsi s'.tmpnum’ assume_tac \\
            drule_strip cell_inp_run_cset_var_cget_net \\ drule_first \\ rfs []) \\
    (* For blocking case: *)
    simp [cell_inp_run_cset_var_cget_net_spec, cell_inp_run_cset_var] \\
    drule_strip cells_run_cell_inp_run_RegVar \\ simp [])

 >- (* SliceIndexing *)
 qpat_x_assum `vertype_stmt _ _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [Once vertype_stmt_cases]))
QED

Theorem compile_stmts_correct_cells_run:
 !ps psall cs cs' nl cenv vfext rtlfext Ev EEv.
 compile_stmts cs ps = INR (cs', nl) /\

 memsublist ps psall /\
 writes_ok psall /\
 EVERY (preprocessed Ev EEv) ps /\
 EVERY (vertype_stmt EEv Ev) ps /\

 same_fext_n vfext rtlfext /\
 vertype_fext_n EEv vfext /\

 writes_ok_sis psall cs /\
 cstate_ok rtlfext EEv Ev cs cenv
 ==>
 cstate_progress cs cs' /\
 sis_progress cs cs' /\
 writes_ok_sis psall cs' /\
 (∀var. MEM var (FLAT (MAP vwrites ps)) ⇒ IS_SOME (cget_net_var [HD cs'.bsi] var)) ∧
 netlist_ok EEv cs.tmpnum cs'.tmpnum nl /\
 netlist_sorted nl /\
 ?cenv'.
  sum_foldM (cell_run rtlfext) cenv nl = INR cenv' /\
  cstate_ok rtlfext EEv Ev cs' cenv' /\
  !vs. ?fbits.
   case sum_foldM (prun vfext) (vs with fbits := fbits) ps of
     INL e => T
   | INR vs' => same_state_sis rtlfext vs cs cenv /\ vertype_env Ev vs ==> same_state_sis rtlfext vs' cs' cenv'
Proof
 rewrite_tac [EVERY_preprocessed] \\ (* <-- backwards compat. should probably be moved *)
 Induct
 >- (rw [compile_stmts_def, sum_foldM_def, cstate_progress_def, sis_progress_def, si_progress_def, netlist_ok_def, netlist_sorted_def] \\
     rw [sum_foldM_def] \\ metis_tac [pstate_fbits_fbits]) \\

 rpt strip_tac' \\ fs [compile_stmts_def, sum_bind_INR] \\ rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\

 drule_strip compile_stmt_correct \\ disch_then (qspec_then `psall` mp_tac) \\
 impl_tac >- (fs [memsublist_def] \\ first_x_assum (qspec_then `h` (assume_tac o SIMP_RULE (srw_ss()) [])) \\
             fs [writes_ok_def, MEM_FLAT, MEM_MAP] \\ metis_tac []) \\ strip_tac \\

 drule_strip memsublist_tl \\ drule_first \\ rpt conj_tac
 >- fs [cstate_progress_def]
 >- fs [sis_progress_def, si_progress_def]
 >- simp []
 >- (fs [sis_progress_def, si_progress_def] \\ metis_tac [])
 >- (simp [netlist_ok_append] \\ conj_tac \\ match_mp_tac netlist_ok_le \\ asm_exists_tac \\ fs [cstate_progress_def])
 >- metis_tac [netlist_sorted_append] \\

 simp [sum_foldM_append, sum_bind_def] \\
 gen_tac \\ last_x_assum (qspec_then ‘vs’ strip_assume_tac) \\
 pop_assum mp_tac \\ TOP_CASE_TAC >- (qexists_tac ‘fbits’ \\ TOP_CASE_TAC \\ gs [sum_foldM_INR]) \\ strip_tac \\
 drule_strip prun_fbits \\

 first_x_assum (qspec_then ‘y’ strip_assume_tac) \\ qexists_tac ‘replace_prefix fbits' fbits n’ \\ pop_assum mp_tac \\
 first_x_assum (qspec_then ‘replace_prefix fbits' fbits n’ mp_tac) \\ 
 simp [init_seq_eq_replace_prefix, shift_seq_replace_prefix] \\ strip_tac \\

 TOP_CASE_TAC >- (TOP_CASE_TAC \\ gs [sum_foldM_INR]) \\ strip_tac \\

 TOP_CASE_TAC \\ gvs [sum_foldM_INR] \\ strip_tac \\ rpt drule_first \\
 metis_tac [vertype_stmt_prun, vertype_env_fbits]
QED

(*Theorem si_sound_union:
 !Ec cenv b1 b2 n.
 si_wf [b1] /\ si_wf [b2] /\
 si_sound Ec cenv [b1] /\ si_sound Ec cenv [b2] ==>
 si_sound Ec cenv [union string_cmp b1 b2]
Proof
 simp [si_wf_def, si_sound_def, cget_net_var_singleton, lookup_union] \\ rpt strip_tac' \\
 every_case_tac \\ drule_first \\ rfs []
QED*)

Triviality IS_SOME_cget_net_var_HD:
 ∀si var. si_wf si ⇒ IS_SOME (cget_net_var [HD si] var) ⇒  IS_SOME (cget_net_var si var)
Proof
 Cases \\ rw [si_wf_def, cget_net_var_def] \\ TOP_CASE_TAC \\ fs []
QED

Theorem regs_ok_compile_regs:
 !decls pseudos fext EEv Ev s s' cenv cenv'.
 cstate_ok fext EEv Ev s cenv ∧
 cstate_ok fext EEv Ev s' cenv' ∧
 s.tmpnum ≤ s'.tmpnum ∧
 EVERY (λ(var, data). OPTION_ALL (λv. vertype_v v data.type) data.init) decls ⇒
 (*(∀var. pseudos ⇒ IS_SOME (cget_net_var [HD s.bsi] var)) ⇒*)
 regs_ok EEv s.tmpnum s'.tmpnum (compile_regs pseudos s.bsi s'.bsi s'.nbsi decls)
Proof
 Induct \\ TRY PairCases \\ fs [compile_regs_def, regs_ok_def, reg_ok_def, compile_reg_def] \\ rpt strip_tac
 >- (Cases_on ‘h1.init’ \\ fs [has_rtltype_v_correct, rtltype_v_compile_value_compile_type])
 (*>- (IF_CASES_TAC \\ fs [verilogWriteCheckerTheory.compute_writes_bw_correct, cstate_ok_def, IS_SOME_cget_net_var_HD])*)
 >- (fs [cstate_ok_def, si_lt_def, OPTION_ALL_alt] \\ every_case_tac \\ rw [] \\ metis_tac [cell_input_lt_le])
 >- (fs [cstate_ok_def, si_sound_def, OPTION_ALL_alt] \\ every_case_tac \\ rw [] \\ metis_tac [cell_input_lt_le])
 \\ metis_tac []
QED

Theorem mem_compile_reg:
 !decls var pseudos bsi bsi' nbsi.
 MEM var (MAP reg_name (MAP (compile_reg pseudos bsi bsi' nbsi) decls)) <=> MEM var (MAP FST decls)
Proof
 rw [MAP_MAP_o] \\ rw [MEM_MAP] \\ eq_tac \\ rpt strip_tac \\ rveq \\ PairCases_on ‘y’ \\ asm_exists_any_tac \\
 simp [compile_reg_def] \\ every_case_tac \\ simp [reg_name_def]
QED

Theorem regs_distinct_compile_regs:
 !decls pseudos bsi bsi' nbsi.
 ALL_DISTINCT (MAP FST decls) ==> regs_distinct (compile_regs pseudos bsi bsi' nbsi decls)
Proof
 Induct \\ TRY PairCases \\ fs [regs_distinct_def, compile_regs_def, compile_reg_def, reg_name_def, mem_compile_reg]
QED

Triviality compile_regs_alookup_lem:
 !decls var.
 ~MEM var (MAP (λ(t,var,v). var) decls) ==> ALOOKUP (MAP (λ(ty,var,v). (var,ty)) decls) var = NONE
Proof
 Induct \\ TRY PairCases \\ rw []
QED

(*Triviality compile_regs_alookup_lem_SOME:
 !decls t var v.
 MEM (t, var, v) decls /\ ALL_DISTINCT (MAP (λ(t,var,v). var) decls) ==> ALOOKUP (MAP (λ(ty,var,v). (var,ty)) decls) var = SOME t
Proof
 Induct \\ TRY PairCases \\ rw [ALOOKUP_def]
 >- (fs [MEM_MAP] \\ first_x_assum (qspec_then ‘(t, h1, v)’ strip_assume_tac) \\ fs [])
 >- drule_first
QED*)

Triviality compile_regs_correct_lem:
 !(bsi : si_t list) bsi' nbsi pseudos fext decls cenvnet cenvreg (EEv : extenvt) Ev.
 Ev_covers_decls Ev decls /\
 ALL_DISTINCT (MAP FST decls) /\
 si_sound fext EEv Ev cenvnet bsi /\
 si_sound fext EEv Ev cenvnet nbsi ==>
 ?cenv'. sum_foldM (reg_run fext cenvnet) cenvreg
                   (FILTER (λ(var,data). data.reg_type = Reg) (compile_regs pseudos bsi' bsi nbsi decls)) = INR cenv' /\
         (!var varnum.
           if varnum = 0 then
            (case ALOOKUP decls var of
             SOME _ =>
              if member string_cmp var pseudos then
               cget_var cenv' (RegVar var varnum) = cget_var cenvreg (RegVar var varnum)
              else
               (case cget_net_var nbsi var of
                  NONE => (case cget_net_var bsi var of
                             NONE => cget_var cenv' (RegVar var varnum) = cget_var cenvreg (RegVar var varnum)
                           | SOME inp => cget_var cenv' (RegVar var varnum) = cell_inp_run fext cenvnet inp)
                | SOME inp => cget_var cenv' (RegVar var varnum) = cell_inp_run fext cenvnet inp)
           | NONE => cget_var cenv' (RegVar var varnum) = cget_var cenvreg (RegVar var varnum))
           else
            cget_var cenv' (RegVar var varnum) = cget_var cenvreg (RegVar var varnum))
Proof
 ntac 5 gen_tac \\ Induct \\ TRY PairCases \\
 fs [Ev_covers_decls_cons, compile_regs_def, sum_foldM_def, sum_bind_INR] \\
 simp [compile_reg_def] \\ rpt gen_tac \\

 rpt strip_tac' \\ drule_first \\

 CASE_TAC >- (first_x_assum (qspec_then ‘cenvreg’ strip_assume_tac) \\
              asm_exists_tac \\ 
              rpt gen_tac \\ first_x_assum (qspecl_then [‘var’, ‘varnum’] mp_tac) \\
              rw [] \\ gs [GSYM ALOOKUP_NONE]) \\

 simp [sum_foldM_def, reg_run_def] \\
 reverse CASE_TAC >- (fs [si_sound_def] \\ drule_first \\ simp [sum_bind_def, has_rtltype_v_correct] \\
                      drule_strip same_type_compile_type \\ gvs [] \\ simp [sum_bind_def] \\

                      qmatch_goalsub_abbrev_tac `sum_foldM _ cenvreg' _ = _` \\
                      first_x_assum (qspec_then ‘cenvreg'’ strip_assume_tac) \\
                      qunabbrev_tac ‘cenvreg'’ \\ asm_exists_tac \\

                      rpt gen_tac \\ first_x_assum (qspecl_then [‘var’, ‘varnum’] mp_tac) \\
                      rw [] \\ gs [cget_var_cset_var, GSYM ALOOKUP_NONE]) \\

 CASE_TAC >- (first_x_assum (qspec_then ‘cenvreg’ strip_assume_tac) \\
              simp [sum_bind_def] \\
              rpt gen_tac \\ first_x_assum (qspecl_then [‘var’, ‘varnum’] mp_tac) \\
              rw [] \\ gs [GSYM ALOOKUP_NONE]) \\

 fs [si_sound_def] \\ drule_first \\ simp [sum_bind_def, has_rtltype_v_correct] \\
 drule_strip same_type_compile_type \\ gvs [] \\ simp [sum_bind_def] \\

 qmatch_goalsub_abbrev_tac `sum_foldM _ cenvreg' _ = _` \\
 first_x_assum (qspec_then ‘cenvreg'’ strip_assume_tac) \\
 qunabbrev_tac ‘cenvreg'’ \\ asm_exists_tac \\

 rpt gen_tac \\ first_x_assum (qspecl_then [‘var’, ‘varnum’] mp_tac) \\
 rw [] \\ gs [cget_var_cset_var, GSYM ALOOKUP_NONE]
QED

Theorem writes_ok_no_overlap:
 !ps s.
 writes_ok ps /\
 writes_ok_sis ps s ==>
 (!var inp. cget_net_var s.bsi var = SOME inp ==> cget_net_var s.nbsi var = NONE) /\
 (!var inp. cget_net_var s.nbsi var = SOME inp ==> cget_net_var s.bsi var = NONE)
Proof
 rw [writes_ok_def, writes_ok_sis_def] \\ metis_tac [optionTheory.option_CLAUSES]
QED

(* back comp. *)
Triviality Ev_from_decls_not_in_decls:
 ∀var decls. ALOOKUP decls var = NONE ⇔ (Ev_from_decls decls) var = NONE
Proof
 simp [Ev_from_decls_def, alist_to_map_alookup, ALOOKUP_MAP]
QED

Theorem compile_regs_correct:
 !cenvnet cenvreg decls ffs rtlfext s (EEv : extenvt) bsi pseudos.

 ALL_DISTINCT (MAP FST decls) /\
 EVERY (λ(var, data). OPTION_ALL (\v. vertype_v v data.type) data.init) decls /\
 (* actually cenvreg important, but can resolve this in the proof: *)
 (!fext. si_complete fext (Ev_from_decls decls) cenvnet [empty]) /\

 cstate_ok rtlfext EEv (Ev_from_decls decls) s cenvnet ∧ (* only depend on si_sound currently *)

 (* maybe also no non-blocking writes? *)
 (∀var. member string_cmp var pseudos ⇒ ~MEM var (FLAT (MAP vwrites ffs)) ∧
                                        ~MEM var (FLAT (MAP vnwrites ffs))) ∧

 writes_ok ffs /\
 writes_ok_sis ffs s ∧
 (∀reg i. cget_var cenvreg (RegVar reg i) = cget_var cenvnet (RegVar reg i)) ⇒
 (*regs_ok EEv s.tmpnum (compile_regs s.bsi s.nbsi decls combs) /\
 regs_distinct (compile_regs s.bsi s.nbsi decls combs) /\*)
 ?cenv. sum_foldM (reg_run rtlfext cenvnet) cenvreg
                  (FILTER (λ(var,data). data.reg_type = Reg) (compile_regs pseudos bsi s.bsi s.nbsi decls)) = INR cenv /\
        (!fext. si_complete fext (Ev_from_decls decls) cenv [empty]) /\
        (!venv venv' vfext.
        (*mstep vfext ffs venv = INR venv' /\ (* <-- again, overly specific *)*)
        sum_foldM (prun vfext) venv ffs = INR venv' ∧
        venv.nbq = [] /\
        same_state_bsi rtlfext venv'.vars cenvnet s.bsi /\
        same_state_nbsi rtlfext venv'.nbq cenvnet s.nbsi /\
        same_state (venv.nbq ++ venv.vars) cenvreg ==>
        same_state (venv'.nbq ++ venv'.vars) cenv)
Proof
 rewrite_tac [cstate_ok_def] \\

 rpt strip_tac \\
 drule_strip Ev_covers_decls_Ev_from_decls \\
 qspecl_then [‘s.bsi’, ‘bsi’, ‘s.nbsi’, ‘pseudos’] assume_tac compile_regs_correct_lem \\ drule_first \\
 first_x_assum (qspecl_then [‘cenvreg’] strip_assume_tac) \\ asm_exists_tac \\
 
 conj_tac >-
 (fs [si_complete_def, cget_net_empty] \\ rpt strip_tac \\
  drule_first \\ first_x_assum (qspec_then ‘fext’ strip_assume_tac) \\
  first_x_assum (qspecl_then [‘var’, ‘0’] mp_tac) \\ every_case_tac \\
  fs [cell_inp_run_def] \\ strip_tac \\ rpt asm_exists_tac \\ fs [si_sound_def] \\
  rpt drule_first \\ fs [sum_bind_def, cget_fext_var_def] \\ TRY (metis_tac [same_type_deterministic])) \\

 drule_strip regs_run_cget_var_NetVar \\
 (*drule_strip cells_run_cget_var_RegVar \\*)
 rpt strip_tac \\ fs [same_state_def, sum_alookup_append] (*, GSYM get_var_sum_alookup, GSYM get_nbq_var_sum_alookup]*) \\
 rpt gen_tac \\ TOP_CASE_TAC \\ strip_tac

 >- (fs [same_state_bsi_def] \\ drule_first \\ first_x_assum (qspecl_then [‘var’, ‘0’] mp_tac) \\ simp [] \\ rpt TOP_CASE_TAC
    >- (fs [Ev_from_decls_not_in_decls] \\ Cases_on ‘cget_net_var s.bsi var’
       >- (fs [cget_net_def, cell_inp_run_def, sum_bind_INR, cget_fext_var_def] \\ metis_tac [])
       \\ fs [cget_net_def, si_sound_def] \\ drule_first \\ fs [alist_to_map_alookup])
    >- (strip_tac \\ drule_first \\ gs [] \\ first_x_assum irule \\ drule_strip pruns_same_after \\
        fs [EVERY_MEM_MEM_FLAT_MAP, get_var_sum_alookup])
    >- (fs [cget_net_def, cell_inp_run_def, sum_bind_INR, cget_fext_var_def] \\ metis_tac [])
    \\ fs [same_state_nbsi_def] \\ drule_first \\ rfs [cget_net_def] \\
       fs [si_sound_def] \\ drule_first \\
       fs [cell_inp_run_def] \\ qpat_x_assum ‘INR _ = _’ (assume_tac o GSYM) \\ rfs [sum_bind_INR, sum_bind_def, cget_fext_var_def] \\
       strip_tac \\ drule_strip writes_ok_no_overlap \\ drule_first \\ fs [cell_inp_run_def, sum_bind_INR, cget_fext_var_def] \\ rfs [] \\ fs [])

 \\ rveq \\ fs [same_state_nbsi_def] \\ drule_first \\ first_x_assum (qspecl_then [‘var’, ‘0’] mp_tac) \\ simp [] \\ rpt TOP_CASE_TAC
    >- (fs [Ev_from_decls_not_in_decls] \\ Cases_on ‘cget_net_var s.nbsi var’
       >- (fs [cget_net_def, cell_inp_run_def, sum_bind_INR, cget_fext_var_def] \\ metis_tac [])
       \\ fs [cget_net_def, si_sound_def] \\ drule_first \\ fs [alist_to_map_alookup])
    >- (strip_tac \\ drule_first \\ drule_strip pruns_same_after \\
        gs [EVERY_MEM_MEM_FLAT_MAP, get_nbq_var_sum_alookup])
    >- (fs [cget_net_def, cell_inp_run_def, sum_bind_INR, cget_fext_var_def] \\ metis_tac [])
    >- (strip_tac \\ drule_strip pruns_get_nbq_var_INR \\ simp [get_nbq_var_sum_alookup, sum_alookup_nil] \\ disch_then drule_strip \\
        fs [writes_ok_sis_def] \\ drule_first \\ fs [writes_ok_def] \\ metis_tac [])
    \\ strip_tac \\ fs [cget_net_def]
QED

Triviality compile_regs_correct_PseudoRegs_lem:
 !(bsi : si_t list) bsi' nbsi pseudos fext decls cenvnet cenvreg (EEv : extenvt) Ev.
 Ev_covers_decls Ev decls /\
 ALL_DISTINCT (MAP FST decls) /\
 si_sound fext EEv Ev cenvnet bsi ⇒
 (*(∀var. MEM var (FLAT (MAP vwrites combs)) ⇒ cget_net_var bsi' var = NONE) ==>*)
 ?cenv'. sum_foldM (reg_run fext cenvnet)
                   cenvreg 
                   (FILTER (λ(var,data). data.reg_type = PseudoReg) (compile_regs pseudos bsi bsi' nbsi decls)) = INR cenv' /\
         (!var varnum.
           if varnum = 0 then
            (case ALOOKUP decls var of
             SOME _ =>
              if member string_cmp var pseudos then
               (case cget_net_var bsi var of
                  NONE => cget_var cenv' (RegVar var varnum) = cget_var cenvreg (RegVar var varnum)
                | SOME inp => cget_var cenv' (RegVar var varnum) = cell_inp_run fext cenvnet inp)
              else
               cget_var cenv' (RegVar var varnum) = cget_var cenvreg (RegVar var varnum)
           | NONE => cget_var cenv' (RegVar var varnum) = cget_var cenvreg (RegVar var varnum))
           else
            cget_var cenv' (RegVar var varnum) = cget_var cenvreg (RegVar var varnum))
Proof
 ntac 5 gen_tac \\ Induct \\ TRY PairCases \\ 
 simp [compile_regs_def, compile_reg_def, sum_foldM_def, Ev_covers_decls_cons] \\
 rpt strip_tac' \\ 
 reverse CASE_TAC >- (drule_first \\
                      first_x_assum (qspec_then ‘cenvreg’ strip_assume_tac) \\ fs [compile_regs_def] \\ 
                      rpt gen_tac \\ first_x_assum (qspecl_then [‘var’, ‘varnum’] mp_tac) \\
                      rw [] \\ gs [GSYM ALOOKUP_NONE]) \\
 simp [sum_foldM_INR, reg_run_def] \\
 TOP_CASE_TAC >- (* duplication *) (drule_last \\
                                    first_x_assum (qspec_then ‘cenvreg’ strip_assume_tac) \\ fs [compile_regs_def] \\ 
                                    rpt gen_tac \\ first_x_assum (qspecl_then [‘var’, ‘varnum’] mp_tac) \\
                                    rw [] \\ gs [GSYM ALOOKUP_NONE]) \\
 drule_last \\ fs [si_sound_def] \\ rpt drule_first \\ drule_strip same_type_compile_type \\
 gvs [sum_bind_def, has_rtltype_v_correct] \\
 qmatch_goalsub_abbrev_tac ‘sum_foldM _ cenvreg' _’ \\ first_x_assum (qspec_then ‘cenvreg'’ strip_assume_tac) \\
 unabbrev_all_tac \\ fs [compile_regs_def] \\
 rpt gen_tac \\ first_x_assum (qspecl_then [‘var’, ‘varnum’] mp_tac) \\
 rw [] \\ gs [GSYM ALOOKUP_NONE, cget_var_cset_var]
QED

Theorem compile_regs_correct_PsuedoRegs:
 !cenv decls combs rtlfext s s' (EEv : extenvt) pseudos.
 ALL_DISTINCT (MAP FST decls) /\
 EVERY (λ(var, data). OPTION_ALL (\v. vertype_v v data.type) data.init) decls /\
 EVERY (vertype_stmt EEv (Ev_from_decls decls)) combs /\
 
 si_sound rtlfext EEv (Ev_from_decls decls) cenv s.bsi ∧

 (!fext. si_complete fext (Ev_from_decls decls) cenv [empty]) ∧

 (∀var. MEM var (FLAT (MAP vwrites combs)) ⇒ member string_cmp var pseudos) ⇒

 (* writes stuff *)
 (*(∀var. MEM var (FLAT (MAP vwrites combs)) ⇒ cget_net_var s'.bsi var = NONE) ⇒ *)
 ?cenv'. sum_foldM (reg_run rtlfext cenv) cenv 
                   (FILTER (λ(var,data). data.reg_type = PseudoReg)
                           (compile_regs pseudos s.bsi s'.bsi s'.nbsi decls)) = INR cenv' /\
         (!fext. si_complete fext (Ev_from_decls decls) cenv' [empty]) /\
         (!venv venv' vfext.
         sum_foldM (prun vfext) venv combs = INR venv' ∧ (* <-- overly specific (probably?) *)
         same_state_bsi rtlfext venv'.vars cenv s.bsi /\
         same_state venv.vars cenv ==>
         same_state venv'.vars cenv')
Proof
 rpt strip_tac \\
 drule_strip Ev_covers_decls_Ev_from_decls \\
 qspecl_then [‘s.bsi’, ‘s'.bsi’, ‘s'.nbsi’, ‘pseudos’] assume_tac compile_regs_correct_PseudoRegs_lem \\
 drule_first \\ first_x_assum (qspecl_then [‘cenv’] strip_assume_tac) \\ asm_exists_tac \\
 conj_tac >- (fs [si_complete_def, si_sound_def, cget_net_empty, cell_inp_run_def] \\ rpt strip_tac \\
              drule_first \\ fs [Ev_from_decls_def, alist_to_map_alookup, ALOOKUP_MAP] \\
              first_x_assum (qspecl_then [‘var’, ‘0’] mp_tac) \\ simp [] \\
              every_case_tac \\ rw [] \\ rpt asm_exists_tac \\ rpt drule_first \\ gvs [] \\ metis_tac []) \\
 simp [same_state_def, same_state_bsi_def] \\ rpt strip_tac \\ drule_first \\
 first_x_assum (qspecl_then [‘var’, ‘0’] mp_tac) \\ simp [] \\ TOP_CASE_TAC
 >- (strip_tac \\ fs [GSYM get_var_sum_alookup] \\
     metis_tac [vertype_stmts_writes, pruns_same_after, Ev_from_decls_not_in_decls, EVERY_MEM_MEM_FLAT_MAP])
 \\ TOP_CASE_TAC
 >- (TOP_CASE_TAC \\ fs [cget_net_def, cell_inp_run_def])
 \\ strip_tac \\ drule_strip pruns_same_after \\ fs [get_var_sum_alookup, EVERY_MEM_MEM_FLAT_MAP] \\ metis_tac []
QED

Theorem same_state_same_state_bsi:
 !fext venv cenv. same_state venv cenv ==> same_state_bsi fext venv cenv [empty]
Proof
 rw [same_state_def, same_state_bsi_def, cget_net_empty] \\ drule_first \\ rw [cell_inp_run_def, sum_bind_def, cget_fext_var_def]
QED

Theorem same_state_nbsi_nil_empty:
 !fext s. same_state_nbsi fext [] s [empty]
Proof
 rw [same_state_nbsi_def, sum_alookup_def, cget_net_empty]
QED

Theorem cstate_vertypes_sound_Ev_from_decls:
 !decls. cstate_vertypes_sound (Ev_from_decls decls) decls
Proof
 rw [cstate_vertypes_sound_def, decls_type_INR, Ev_from_decls_def] \\ rw [alist_to_map_alookup, ALOOKUP_MAP]
QED

Triviality same_state_bsi_ffs_lem:
 sum_foldM (cell_run fext) cenv' nl_ffs = INR cenv'' ∧
 netlist_ok EEv s_combs.tmpnum s.tmpnum nl_ffs ∧
 cstate_ok fext EEv (Ev_from_decls decls) s_combs cenv' ∧
 same_state_sis fext venv s_combs cenv' ⇒
 same_state_bsi fext venv.vars cenv'' s_combs.bsi
Proof
 rw [cstate_ok_def, same_state_sis_def, same_state_bsi_def] \\ drule_first \\
 imp_res_tac cells_run_unchanged_netlist_ok_cget_net \\ simp []
QED

Theorem cells_run_same_state:
 sum_foldM (cell_run fext) s nl = INR s' ∧ same_state cenv s ⇒ same_state cenv s'
Proof
 rw [same_state_def] \\ drule_first \\ drule_strip cells_run_cget_var_RegVar \\ simp []
QED

Theorem cells_run_si_complete_empty:
 ∀nl fext cenv cenv' Ev.
 sum_foldM (cell_run fext) cenv nl = INR cenv' ∧
 (∀fext. si_complete fext Ev cenv [empty]) ⇒
 (∀fext. si_complete fext Ev cenv' [empty])
Proof
 rw [si_complete_def, cget_net_empty, cell_inp_run_def] \\ metis_tac [cells_run_cget_var_RegVar]
QED

Theorem compile_stmts_correct_step:
 !decls combs s_combs nl_combs ffs s nl_ffs rtlfext vfext cenv pseudos EEv.
 let regs = compile_regs pseudos s_combs.bsi s.bsi s.nbsi decls in
 compile_stmts <| bsi := [empty]; nbsi := [empty]; vertypes := decls; tmpnum := 0 |> combs = INR (s_combs, nl_combs) /\
 compile_stmts (s_combs with <| bsi := [empty]; nbsi := [empty] |>) ffs = INR (s, nl_ffs) /\

 ALL_DISTINCT (MAP FST decls) /\ (* <-- can say regs_distinct here... *)
 EVERY (λ(var, data). OPTION_ALL (λv. vertype_v v data.type) data.init) decls /\

 writes_ok combs /\
 writes_ok ffs ∧

 (∀var. member string_cmp var pseudos ⇒ ~MEM var (FLAT (MAP vwrites ffs)) ∧
                                        ~MEM var (FLAT (MAP vnwrites ffs))) ∧

 same_fext_n vfext rtlfext /\
 vertype_fext_n EEv vfext /\

 EVERY (preprocessed (Ev_from_decls decls) EEv) ffs ∧
 EVERY (vertype_stmt EEv (Ev_from_decls decls)) ffs /\

 EVERY (preprocessed (Ev_from_decls decls) EEv) combs ∧
 EVERY (vertype_stmt EEv (Ev_from_decls decls)) combs /\
 
 (!fext. si_complete fext (Ev_from_decls decls) cenv [empty]) ∧
 (∀var. MEM var (FLAT (MAP vwrites combs)) ⇒ member string_cmp var pseudos) ==>
 s_combs.tmpnum ≤ s.tmpnum ∧
 netlist_ok EEv 0 s_combs.tmpnum nl_combs ∧
 netlist_ok EEv s_combs.tmpnum s.tmpnum nl_ffs /\
 netlist_sorted (nl_combs ++ nl_ffs) /\
 regs_ok EEv s_combs.tmpnum s.tmpnum regs /\
 regs_distinct regs /\
 ?cenv' cenv''.
  netlist_step rtlfext cenv nl_combs nl_ffs regs = INR cenv' /\
  (!fext. si_complete fext (Ev_from_decls decls) cenv' [empty]) /\
  (* since we move the evaluation of reg's inps one step before Verilog: *)
  sum_foldM (reg_run rtlfext cenv')
            (cenv' with env := FILTER (is_RegVar o FST) cenv'.env)
            (FILTER (λ(var,data). data.reg_type = Reg) regs) = INR cenv'' ∧
  (!fext. si_complete fext (Ev_from_decls decls) cenv'' [empty]) /\ (* <-- might want to move this... *)
  !venv. ?fbits.
   case mstep_combs vfext fbits combs venv of
     INL e => T
   | INR (venv', fbits') =>
      same_state venv cenv /\ vertype_list (Ev_from_decls decls) venv ⇒
      same_state venv' cenv' ∧
      (case mstep_ffs vfext fbits' ffs venv' of
         INL e => T
       | INR (venv'', fbits'') => same_state venv'' cenv'')
Proof
 simp [mstep_combs_def, netlist_step_def] \\ rpt strip_tac' \\

 last_x_assum assume_tac \\
 drule_strip compile_stmts_correct_cells_run \\
 disch_then (qspec_then `combs` mp_tac) \\ simp [memsublist_sym] \\
 disch_then drule_strip \\ simp [] \\
 disch_then (qspec_then `cenv` mp_tac) \\
 impl_tac >- fs [vertype_fext_vertype_fext_n, writes_ok_sis_def, cget_net_var_empty,
                 cstate_ok_def, si_wf_empty, si_sound_empty, si_lt_empty, cstate_vertypes_sound_Ev_from_decls] \\
 strip_tac \\

 drule_strip compile_regs_correct_PsuedoRegs \\
 disch_then (qspecl_then [‘cenv'’, ‘rtlfext’, ‘s_combs’, ‘s’, ‘pseudos’] mp_tac) \\
 impl_tac >- (imp_res_tac cells_run_cget_var_RegVar \\
              fs [si_complete_def, cget_net_empty, cell_inp_run_def] \\
              fs [si_sound_def, cstate_ok_def] \\ metis_tac []) \\
 strip_tac \\

 last_x_assum assume_tac \\
 drule_strip compile_stmts_correct_cells_run \\
 disch_then (qspec_then `ffs` mp_tac) \\ simp [memsublist_sym] \\
 disch_then drule_strip \\ simp [] \\
 disch_then (qspec_then `cenv''` mp_tac) \\
 impl_tac >- (fs [vertype_fext_vertype_fext_n, writes_ok_sis_def, cget_net_var_empty,
                  cstate_ok_def, si_wf_empty, si_sound_empty, si_lt_empty, cstate_vertypes_sound_Ev_from_decls]) \\

 rw []
 >- fs [cstate_progress_def]
 (*>- (rw [netlist_ok_append] \\ irule netlist_ok_le \\ asm_exists_any_tac \\ fs [cstate_progress_def])*)
 >- metis_tac [netlist_sorted_append]
 >- (match_mp_tac regs_ok_compile_regs \\ rpt asm_exists_tac \\ fs [cstate_progress_def])
 >- (drule_strip regs_distinct_compile_regs \\ simp []) \\

 drule_strip cells_run_si_complete_empty \\
 simp [sum_bind_def] \\

 drule_strip compile_regs_correct \\
 qmatch_goalsub_abbrev_tac ‘sum_foldM _ cenvreg _’ \\
 disch_then (qspecl_then [‘cenvreg’, ‘s_combs.bsi’] strip_assume_tac) \\
 unabbrev_all_tac \\
 pop_assum mp_tac \\ impl_tac >- simp [cget_var_def, ALOOKUP_FILTER_FST, is_RegVar_def] \\ strip_tac \\
 rpt asm_exists_tac \\

 gen_tac \\
 last_x_assum (qspec_then ‘<| vars := venv; nbq := [] |>’ strip_assume_tac) \\
 pop_assum mp_tac \\ TOP_CASE_TAC >- (qexists_tac ‘fbits’ \\ fs [sum_bind_def]) \\ strip_tac \\
 drule_strip pruns_fbits \\
 qpat_x_assum ‘∀vs. ∃fbits. _’ (qspec_then ‘<|vars := y.vars; nbq := []; fbits := y.fbits|>’ strip_assume_tac) \\

 (* fbits for n steps + fbits' for the rest *)
 qexists_tac ‘replace_prefix fbits' fbits n’ \\
 first_x_assum (qspec_then ‘replace_prefix fbits' fbits n’ mp_tac) \\
 impl_tac >- simp [init_seq_eq_replace_prefix] \\ simp [sum_bind_def] \\ rpt strip_tac' \\
     
 qpat_x_assum ‘_ ⇒ _’ mp_tac \\
 impl_tac >- (simp [same_state_sis_def, same_state_bsi_def, same_state_nbsi_def, cget_net_empty, cell_inp_run_def,
                    vertype_env_vertype_list, vertype_list_nil] \\ fs [same_state_def]) \\ strip_tac \\
     
 drule_first \\ impl_tac >- (fs [same_state_sis_def] \\ metis_tac [cells_run_same_state]) \\
 simp [shift_seq_replace_prefix] \\ strip_tac \\

 conj_asm1_tac >- metis_tac [cells_run_same_state] \\

 TOP_CASE_TAC \\ TOP_CASE_TAC \\
 gvs [shift_seq_replace_prefix, mstep_ffs_def, sum_bind_INR] \\ drule_first \\ disch_then irule \\
 conj_tac >- simp [] \\
 conj_tac >- fs [same_state_def, cget_var_def, ALOOKUP_FILTER_FST, is_RegVar_def] \\
 fs [same_state_sis_def] \\ first_x_assum irule \\
 
 simp [same_state_sis_def, same_state_same_state_bsi, same_state_nbsi_nil_empty,
       vertype_env_vertype_list, vertype_list_nil] \\

 (* vertype_list survives... *)
 qpat_x_assum ‘sum_foldM _ _ combs = _’ assume_tac \\
 drule_strip vertype_env_pruns \\
 impl_tac >- fs [vertype_fext_vertype_fext_n, vertype_env_vertype_list, vertype_list_nil] \\
 simp [shift_seq_replace_prefix] \\ strip_tac \\
 
 qpat_x_assum ‘sum_foldM _ _ ffs = _’ assume_tac \\
 drule_strip vertype_env_pruns \\
 impl_tac >- fs [vertype_fext_vertype_fext_n, vertype_env_vertype_list, vertype_list_nil] \\
 fs [vertype_env_vertype_list, vertype_list_nil]
QED

Triviality shift_seq_shift_seq_replace_prefix_lem:
 ∀fbits fbits' n m. shift_seq n (shift_seq m (replace_prefix fbits' fbits (m + n))) = fbits'
Proof
 simp [shift_seq_def, replace_prefix_def, SF boolSimps.ETA_ss]
QED

Theorem compile_stmts_correct_run:
 !decls n combs s_combs nl_combs ffs s nl_ffs rtlfext vfext cenv pseudos EEv.
 compile_stmts <| bsi := [empty]; nbsi := [empty]; vertypes := decls; tmpnum := 0 |> combs = INR (s_combs, nl_combs) /\
 compile_stmts (s_combs with <| bsi := [empty]; nbsi := [empty] |>) ffs = INR (s, nl_ffs) /\
 (* compile_regs inlined below *)

 ALL_DISTINCT (MAP FST decls) /\ (* <-- can say regs_distinct here... *)
 EVERY (λ(var, data). OPTION_ALL (λv. vertype_v v data.type) data.init) decls /\

 writes_ok combs /\
 writes_ok ffs ∧

 (∀var. member string_cmp var pseudos ⇒ ~MEM var (FLAT (MAP vwrites ffs)) ∧
                                        ~MEM var (FLAT (MAP vnwrites ffs))) ∧
 (∀var. MEM var (FLAT (MAP vwrites combs)) ⇒ member string_cmp var pseudos) ∧

 same_fext vfext rtlfext /\
 vertype_fext EEv vfext /\

 (!fext. si_complete fext (Ev_from_decls decls) cenv [empty]) ∧

 EVERY (preprocessed (Ev_from_decls decls) EEv) ffs ∧
 EVERY (vertype_stmt EEv (Ev_from_decls decls)) ffs /\

 EVERY (preprocessed (Ev_from_decls decls) EEv) combs ∧
 EVERY (vertype_stmt EEv (Ev_from_decls decls)) combs ==>
 s_combs.tmpnum ≤ s.tmpnum ∧
 netlist_ok EEv 0 s_combs.tmpnum nl_combs ∧
 netlist_ok EEv s_combs.tmpnum s.tmpnum nl_ffs /\
 netlist_sorted (nl_combs ++ nl_ffs) /\
 regs_ok EEv s_combs.tmpnum s.tmpnum (compile_regs pseudos s_combs.bsi s.bsi s.nbsi decls) /\
 regs_distinct (compile_regs pseudos s_combs.bsi s.bsi s.nbsi decls) /\
 ?cenv' cenv''.
  netlist_run rtlfext cenv nl_combs nl_ffs (compile_regs pseudos s_combs.bsi s.bsi s.nbsi decls) n = INR cenv' /\
  (!fext. si_complete fext (Ev_from_decls decls) cenv' [empty]) /\
  (* since we move the evaluation of reg's inps one step before Verilog: *)
  sum_foldM (reg_run (rtlfext n) cenv')
            (cenv' with env := FILTER (is_RegVar o FST) cenv'.env)
            (FILTER (λ(var,data). data.reg_type = Reg) (compile_regs pseudos s_combs.bsi s.bsi s.nbsi decls)) = INR cenv'' ∧
  (!fext. si_complete fext (Ev_from_decls decls) cenv'' [empty]) /\ (* <-- might want to move this... *)
  !venv. ?fbits.
   case mrun vfext fbits ffs combs venv n of
     INL e => T
   | INR (venv', fbits') =>
      same_state venv cenv /\ vertype_list (Ev_from_decls decls) venv ⇒
      same_state venv' cenv' ∧ 
      (case mstep_ffs (vfext n) fbits' ffs venv' of
         INL e => T
       | INR (venv'', fbits'') => same_state venv'' cenv'')
Proof
 gen_tac \\ Induct
 (* base case *) >-
 (simp [mrun_def, netlist_run_def] \\ rpt strip_tac' \\

 drule_strip (same_fext_same_fext_n |> SPEC_ALL |> EQ_IMP_RULE |> fst) \\
 pop_assum (qspec_then `0` assume_tac) \\
 drule_strip (vertype_fext_vertype_fext_n |> SPEC_ALL |> EQ_IMP_RULE |> fst) \\
 pop_assum (qspec_then `0` assume_tac) \\

 drule_strip (SIMP_RULE (srw_ss()) [LET_THM] compile_stmts_correct_step) \\ simp [])

 (* step case *) \\
 simp [mrun_def, netlist_run_def] \\ rpt strip_tac' \\
 drule_first \\ simp [sum_bind_def] \\

 drule_strip (same_fext_same_fext_n |> SPEC_ALL |> EQ_IMP_RULE |> fst) \\
 pop_assum (qspec_then `SUC n` assume_tac) \\
 drule_strip (vertype_fext_vertype_fext_n |> SPEC_ALL |> EQ_IMP_RULE |> fst) \\
 pop_assum (qspec_then `SUC n` assume_tac) \\

 drule_strip (SIMP_RULE (srw_ss()) [LET_THM] compile_stmts_correct_step) \\
 
 simp [] \\ gen_tac \\
 last_x_assum (qspec_then ‘venv’ strip_assume_tac) \\ pop_assum mp_tac \\
 TOP_CASE_TAC >- (qexists_tac ‘fbits’ \\ fs [sum_bind_def]) \\
 TOP_CASE_TAC \\ TOP_CASE_TAC >- (strip_tac \\ qexists_tac ‘fbits’ \\ simp [sum_bind_def]) \\ 
 TOP_CASE_TAC \\ strip_tac \\

 drule_strip mrun_fbits \\
 drule_strip mstep_ffs_fbits \\
 first_x_assum (qspec_then ‘q'’ strip_assume_tac) \\
 
 qexists_tac ‘replace_prefix fbits' fbits (n' + m)’ \\
 last_x_assum (qspec_then ‘replace_prefix fbits' fbits (n' + m)’ mp_tac) \\
 impl_tac >- simp [init_seq_eq_def, replace_prefix_def] \\ simp [sum_bind_def] \\ rpt strip_tac' \\

 first_x_assum (qspec_then ‘shift_seq m (replace_prefix fbits' fbits (n' + m))’ mp_tac) \\
 impl_tac >- simp [init_seq_eq_def, shift_seq_def, replace_prefix_def] \\
 simp [sum_bind_def, shift_seq_shift_seq_replace_prefix_lem] \\ strip_tac \\

 TOP_CASE_TAC \\ TOP_CASE_TAC \\ rpt strip_tac' \\ fs [] \\
 
 first_x_assum irule \\ simp [] \\

 drule_strip vertype_env_mstep_ffs \\
 impl_tac >- (drule_strip vertype_list_mrun \\ fs [vertype_fext_vertype_fext_n]) \\ simp []
QED

Triviality compile_regs_correct_init_lem:
 !(bsi : si_t list) bsi' nbsi pseudos decls cenv.
 ALL_DISTINCT (MAP FST decls) ∧
 EVERY (λ(var,data). OPTION_ALL (λv. vertype_v v data.type) data.init) decls ⇒
 ?cenv'. init_run cenv (compile_regs pseudos bsi bsi' nbsi decls) = INR cenv' /\
         (!var.
           case ALOOKUP decls var of
             SOME rdata => (?v. cget_var cenv' (RegVar var 0) = INR v /\ rtltype_v v (compile_type rdata.type))
           | NONE => !varnum. cget_var cenv' (RegVar var varnum) = cget_var cenv (RegVar var varnum))
Proof
 ntac 4 gen_tac \\ Induct \\ TRY PairCases \\ fs [compile_regs_def, compile_reg_def, init_run_def] \\ rpt strip_tac \\
 drule_first \\ TOP_CASE_TAC
 >- (pairarg_tac \\ simp [] \\ qmatch_goalsub_abbrev_tac ‘init_run cenv' _’ \\
     first_x_assum (qspec_then ‘cenv'’ strip_assume_tac) \\ unabbrev_all_tac \\ rw [] \\ rw []
     >- (drule_strip rtl_nd_value_type_correct \\
         fs [GSYM ALOOKUP_NONE] \\ first_x_assum (qspec_then ‘h0’ mp_tac) \\ simp [cget_var_cset_var])
     \\ first_x_assum (qspec_then ‘var’ mp_tac) \\ TOP_CASE_TAC \\ simp [cget_var_cset_var]) \\

 gvs [has_rtltype_v_correct, rtltype_v_compile_value_compile_type] \\
 qmatch_goalsub_abbrev_tac ‘init_run cenv' _’ \\ first_x_assum (qspec_then ‘cenv'’ strip_assume_tac) \\
 unabbrev_all_tac \\ rw [] \\ rw []
 >- (fs [GSYM ALOOKUP_NONE] \\ first_x_assum (qspec_then ‘h0’ mp_tac) \\
     simp [cget_var_cset_var, rtltype_v_compile_value_compile_type])
 \\ first_x_assum (qspec_then ‘var’ mp_tac) \\ TOP_CASE_TAC \\ simp [cget_var_cset_var]
QED

Theorem compile_regs_correct_init:
 !(bsi : si_t list) bsi' nbsi pseudos m cenv.
 vertype_prog m ==>
 ?cenv'. init_run cenv (compile_regs pseudos bsi bsi' nbsi m.decls) = INR cenv' /\
         !fext. si_complete fext (Ev_from_decls m.decls) cenv' [empty]
Proof
 rewrite_tac [vertype_prog_def] \\ rpt strip_tac \\ drule_strip compile_regs_correct_init_lem \\
 first_x_assum (qspecl_then [‘bsi’, ‘bsi'’, ‘nbsi’, ‘pseudos’, ‘cenv’] strip_assume_tac) \\ simp [] \\

 simp [si_complete_def, Ev_from_decls_def, alist_to_map_alookup, ALOOKUP_MAP, cget_net_empty] \\ rpt strip_tac \\

 first_x_assum (qspec_then ‘var’ mp_tac) \\ simp [] \\ strip_tac \\
 simp [cell_inp_run_def, sum_bind_def, cget_fext_var_def] \\
 asm_exists_any_tac \\ simp [compile_type_correct]
QED

Theorem compile_type_correct_nd:
 !t fbits fbits' fbits'' vv rtlv.
 nd_value fbits t = (vv, fbits') /\
 rtl_nd_value fbits (compile_type t) = (rtlv, fbits'') ==>
 ?m.
  fbits' = shift_seq m fbits /\ 
  fbits'' = fbits' /\  
  same_value vv rtlv /\
  !fbits'. init_seq_eq fbits fbits' m ==>
           nd_value fbits' t = (vv, shift_seq m fbits') /\
           rtl_nd_value fbits' (compile_type t) = (rtlv, shift_seq m fbits')
Proof
 Cases_on `t`
 >- (rw [nd_value_def, rtl_nd_value_def, compile_type_def, oracle_bit_def] \\ simp [same_value_def] \\ qexists_tac `1` \\ simp [init_seq_eq_def])
 \\ rw [nd_value_def, rtl_nd_value_def, compile_type_def] \\ pairarg_tac \\ fs [] \\ rveq \\
    simp [same_value_def] \\ drule_strip oracle_bits_correct \\ qexists_tac ‘LENGTH bs’ \\ simp [] \\
    rpt strip_tac' \\ pairarg_tac \\ drule_strip oracle_bits_correct \\ imp_res_tac oracle_bits_cong \\
    rw []
QED

Theorem compile_regs_correct_init_run:
 !(bsi : si_t list) bsi' nbsi decls pseudos venv venv' s s' fbits fbits'.
 run_decls fbits decls venv = (fbits', venv') /\
 init_run (s with fbits := fbits) (compile_regs pseudos bsi bsi' nbsi decls) = INR s' ==>
 fbits' = s'.fbits /\
 (same_state venv s ==> same_state venv' s')
Proof
 ntac 3 gen_tac \\ Induct \\ TRY PairCases \\
 fs [compile_regs_def, compile_reg_def, run_decls_def, init_run_def, same_state_fbits] \\
 TOP_CASE_TAC
 (* Some ugly duplication here, should factor more: *)
 >-
 (rpt strip_tac' \\ rpt (pairarg_tac \\ fs []) \\ drule_strip compile_type_correct_nd \\
 drule_first \\ simp [] \\ strip_tac \\ first_x_assum match_mp_tac \\
 fs [same_state_def] \\ rw [sum_alookup_cons] \\ fs [cget_var_cset_var, cget_var_def])

 \\
 simp [] \\ CASE_TAC \\ fs [has_rtltype_v_correct, cset_var_fbits] \\ rpt strip_tac' \\ drule_first \\ simp [] \\
 strip_tac \\ first_x_assum match_mp_tac \\
 fs [same_state_def] \\ rw [sum_alookup_cons] \\
 fs [cget_var_cset_var, cget_var_def, compile_value_correct]
QED

(* Can maybe be proven direct instead? *)
Triviality compile_regs_correct_init_run':
 !(bsi : si_t list) bsi' nbsi decls pseudos venv venv' s s' fbits fbits'.
 run_decls fbits decls venv = (fbits', venv') /\
 init_run s (compile_regs pseudos bsi bsi' nbsi decls) = INR s' /\
 fbits = s.fbits ==>
 fbits' = s'.fbits /\
 (same_state venv s ==> same_state venv' s')
Proof
 rpt strip_tac' \\ match_mp_tac compile_regs_correct_init_run \\ asm_exists_tac \\
 simp [rtlstate_fbits_fbits] \\ asm_exists_tac
QED

Theorem nd_value_fbits:
 !t v fbits fbits'.
 nd_value fbits t = (v, fbits') ==>
 ?m. fbits' = shift_seq m fbits /\
     !fbits''. init_seq_eq fbits fbits'' m ==>
               nd_value fbits'' t = (v, shift_seq m fbits'')
Proof
 Cases \\ simp [nd_value_def] \\ rpt strip_tac
 >- (qexists_tac ‘1’ \\ fs [oracle_bit_def] \\ rveq \\ fs [init_seq_eq_def]) \\
 pairarg_tac \\ drule_strip oracle_bits_correct \\ fs [] \\ rveq \\ qexists_tac ‘LENGTH bs’ \\ rw [] \\
 pairarg_tac \\ drule_strip oracle_bits_correct \\ imp_res_tac oracle_bits_cong \\ rw []
QED

Theorem run_decls_fbits:
 !decls venv venv' fbits fbits'.
 run_decls fbits decls venv = (fbits', venv') ==>
 ?m. fbits' = shift_seq m fbits /\
     !fbits''. init_seq_eq fbits fbits'' m ==>
               run_decls fbits'' decls venv = (shift_seq m fbits'', venv')
Proof
 Induct \\ TRY PairCases \\ simp [run_decls_def] \\ rpt gen_tac
 >- (qexists_tac `0` \\ simp [shift_seq_0]) \\
 TOP_CASE_TAC
 >- (pairarg_tac \\ fs [] \\ drule_strip nd_value_fbits \\ strip_tac \\ drule_first \\
    qexists_tac ‘m + m'’ \\ fs [shift_seq_add] \\ rpt strip_tac \\ pairarg_tac \\
    last_x_assum (qspec_then ‘fbits''’ mp_tac) \\
    impl_tac >- (match_mp_tac init_seq_eq_shorten \\ asm_exists_tac \\ simp []) \\ strip_tac \\
    last_x_assum (qspec_then ‘shift_seq m fbits''’ mp_tac) \\
    impl_tac >- simp [init_seq_eq_shift_seq] \\ simp [])
 \\ strip_tac \\ drule_first \\ metis_tac []
QED

Theorem cell_input_covered_by_extenv_compile_fextenv:
 !inp decls. cell_input_covered_by_extenv (compile_fextenv decls) inp ⇔ cell_input_covered_by_extenv decls inp
Proof
 Cases \\ rw [cell_input_covered_by_extenv_def, compile_fextenv_def, ALOOKUP_MAP]
QED

Theorem cell_covered_by_extenv_compile_fextenv:
 ∀inp decls. cell_covered_by_extenv (compile_fextenv decls) inp ⇔ cell_covered_by_extenv decls inp
Proof
 Cases \\ rw [cell_covered_by_extenv_def, cell_input_covered_by_extenv_compile_fextenv]
QED

Theorem netlist_ok_compile_fextenv:
 !decls min max nl. netlist_ok (compile_fextenv decls) min max nl ⇔ netlist_ok decls min max nl
Proof
 metis_tac [netlist_ok_def, EVERY_CONG, cell_covered_by_extenv_compile_fextenv]
QED

Theorem regs_ok_compile_fextenv:
 !decls EEv combs_tmpnum ffs_tmpnum bsi bsi' nbsi combs.
 regs_ok (compile_fextenv EEv) combs_tmpnum ffs_tmpnum (compile_regs bsi bsi' nbsi decls combs) ⇔
 regs_ok EEv combs_tmpnum ffs_tmpnum (compile_regs bsi bsi' nbsi decls combs)
Proof
 rw [regs_ok_def] \\ irule EVERY_CONG \\ simp [] \\ PairCases \\ rw [reg_ok_def] \\ 
 metis_tac [optionTheory.OPTION_ALL_CONG, cell_input_covered_by_extenv_compile_fextenv]
QED

Theorem si_complete_empty_decls_cons:
 ∀decls var rdata cenv.
 ¬MEM var (MAP FST decls) ∧
 (∀fext. si_complete fext (Ev_from_decls ((var, rdata)::decls)) cenv [empty]) ⇒
 (∀fext. si_complete fext (Ev_from_decls decls) cenv [empty]) ∧ 
 (∃cv t'. cget_var cenv (RegVar var 0) = INR cv ∧ same_type rdata.type t' ∧ rtltype_v cv t')
Proof
 simp [si_complete_def, Ev_from_decls_def, alist_to_map_alookup, ALOOKUP_MAP] \\ rpt strip_tac' \\
 fs [GSYM ALOOKUP_NONE, cget_net_empty, cell_inp_run_def] \\ rw [] \\ first_x_assum irule \\ rw [] \\ fs []
QED

Theorem outs_run_compile_outs:
 ∀fext decls cenv.
 ALL_DISTINCT (MAP FST decls) ∧
 (∀fext. si_complete fext (Ev_from_decls decls) cenv [empty]) ⇒
 EVERY out_ok (compile_outs decls) ∧
 ∃cenv'. sum_mapM (out_run fext cenv) (compile_outs decls) = INR cenv' ∧
         ∀var. sum_alookup cenv' var =
               case ALOOKUP decls var of
                 NONE => INL UnknownVariable
               | SOME rdata => if rdata.output then cget_var cenv (RegVar var 0) else INL UnknownVariable
Proof
 gen_tac \\ Induct \\ TRY PairCases \\ fs [compile_outs_def, sum_mapM_def] \\ rpt gen_tac \\ strip_tac \\
 conj_tac >- (rw [EVERY_MAP, EVERY_FILTER, pairTheory.LAMBDA_PROD, out_ok_def, cell_input_lt_def, var_lt_def, cell_input_covered_by_extenv_def] \\ simp [GSYM pairTheory.LAMBDA_PROD]) \\
 drule_strip si_complete_empty_decls_cons \\ drule_first \\ IF_CASES_TAC
 >- (simp [sum_mapM_def, out_run_def, cell_inp_run_def, sum_bind_def, sum_map_def, sum_alookup_cons] \\
     rw [] \\ simp [EQ_SYM]) \\
 rw [] \\ IF_CASES_TAC \\ fs [] \\ CASE_TAC \\ rw [] \\ fs [GSYM ALOOKUP_NONE]
QED

(* Module EEv decls ps *)

Theorem rtltype_extenv_compile_fextenv:
 !vfext rtlfext fextenv.
 same_fext vfext rtlfext ⇒
 (rtltype_extenv (compile_fextenv fextenv) rtlfext ⇔ vertype_fext fextenv vfext)
Proof
 rw [vertype_fext_def, rtltype_extenv_def, compile_fextenv_def,
     ALOOKUP_MAP, sum_alookup_INR, same_fext_def, PULL_EXISTS] \\ eq_tac \\ rw [] \\
 drule_first \\ first_x_assum (qspec_then ‘n’ strip_assume_tac) \\
 fs [] \\ first_x_assum (qspecl_then [‘n’, ‘var’] assume_tac)
 >- (Cases_on ‘vfext n var’ \\ rfs [sum_same_value_def] \\ drule_strip same_value_rtltype_v_vertype_v \\ fs [])
 >- (Cases_on ‘rtlfext n var’ \\ rfs [sum_same_value_def] \\ drule_strip same_value_rtltype_v_vertype_v \\ fs [])
QED

Definition same_state_outs_def:
 same_state_outs m venv cenv ⇔
 ∀var rdata vv. ALOOKUP m.decls var = SOME rdata ∧ rdata.output ∧ sum_alookup venv var = INR vv ⇒
                ∃cv. sum_alookup cenv var = INR cv ∧ same_value vv cv
End

Triviality vertype_stmt_vwrites_lem:
 ∀EEv decls p.
 vertype_stmt EEv (Ev_from_decls decls) p ⇒
 ∀var. MEM var (vwrites p) ⇒ MEM var (MAP FST decls)
Proof
 ntac 2 gen_tac \\ ho_match_mp_tac vertype_stmt_ind \\
 rw [vwrites_def, evwrites_def] \\ simp [SF SFY_ss]
 >- (fs [EVERY_MEM, MEM_FLAT, MEM_MAP] \\ drule_first \\ pairarg_tac \\ gvs [])
 >- (every_case_tac \\ fs [])
 \\ fs [Ev_from_decls_decls_type, decls_type_INR] \\ drule_strip ALOOKUP_MEM \\ drule_strip MEM_pair
QED

(*Triviality EVERY_vertype_stmt_vwrites_lem:
 ∀decls EEv ps var.
 MEM var (FLAT (MAP vwrites ps)) ∧
 EVERY (vertype_stmt EEv (Ev_from_decls decls)) ps ⇒
 MEM var (MAP FST decls)
Proof
 rw [EVERY_MEM, MEM_FLAT, MEM_MAP] \\ drule_first \\ drule_strip vertype_stmt_vwrites_lem \\
 fs [MEM_MAP] \\ metis_tac []
QED*)

Triviality ALOOKUP_compile_regs_PseudoReg_lem:
 ∀decls rdata.
 member string_cmp var pseudos ∧
 ALOOKUP (compile_regs pseudos combs_bsi bsi nbsi decls) (var, 0) = SOME rdata ⇒
 rdata.reg_type = PseudoReg
Proof
 Induct \\ TRY PairCases \\ fs [compile_regs_def, compile_reg_def] \\ rw [] \\ rw []
QED

Theorem rtl_compile_correct:
 !m pseudos cir rtlfext vfext tmpnum.
 compile pseudos m = INR (cir, tmpnum) /\

 (* types *)
 vertype_prog m ∧
 vertype_fext m.fextty vfext /\ (* <-- only works over vfext functions that respect m.fextty (is well-typed) *)

 same_fext vfext rtlfext /\
 
 (* can only compile these kind of programs: *)
 writes_ok m.ffs ∧
 writes_ok m.combs ∧
 (∀var. MEM var (FLAT (MAP vwrites m.combs)) ⇒ member string_cmp var pseudos) ∧
 writes_overlap_ok_pseudos pseudos m.ffs ∧

 EVERY (preprocessed (Ev_from_decls m.decls) m.fextty) m.ffs ∧
 EVERY (preprocessed (Ev_from_decls m.decls) m.fextty) m.combs ⇒
 (rtltype_extenv (circuit_extenv cir) rtlfext ⇔ vertype_fext m.fextty vfext) ∧
 (∀var rdata. member string_cmp var pseudos ∧ ALOOKUP (circuit_regs cir) (var, 0) = SOME rdata ⇒
              rdata.reg_type = PseudoReg) ∧
 (∃combs_tmpnum. circuit_ok 0 combs_tmpnum tmpnum cir) /\
 circuit_sorted cir /\
 ∀n fbits. ?cenv' fbits'.
   circuit_run rtlfext fbits cir n = INR (cenv', fbits') /\
   ?fbits'.
     case run vfext fbits' m n of
       INL e => T
     | INR (venv', _) => same_state_outs m venv' cenv'
Proof
 rewrite_tac [writes_overlap_ok_pseudos_def] \\
 simp [compile_def, run_def, sum_bind_INR] \\ rpt strip_tac' \\
 rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ simp [sum_bind_def] \\ rveq \\

 Ho_Rewrite.REWRITE_TAC [PULL_FORALL] \\ rpt gen_tac \\

 drule_strip compile_regs_correct_init \\
 first_x_assum (qspecl_then [‘s_combs.bsi’, ‘s.bsi’, ‘s.nbsi’, ‘pseudos’, ‘<|env := []; fbits := fbits|>’] strip_assume_tac) \\

 fs [vertype_prog_def] \\
 drule_strip compile_stmts_correct_run \\
 first_x_assum (qspec_then ‘n’ strip_assume_tac) \\
 qspecl_then [‘rtlfext n’, ‘m.decls’, ‘cenv''’] assume_tac outs_run_compile_outs \\ drule_first \\

 rpt conj_tac
 >- (drule_strip rtltype_extenv_compile_fextenv \\ simp [circuit_extenv_def])
 >- (simp [circuit_regs_def] \\ metis_tac [(*EVERY_vertype_stmt_vwrites_lem,*) ALOOKUP_compile_regs_PseudoReg_lem])
 >- (simp [circuit_ok_def, regs_ok_compile_fextenv, netlist_ok_compile_fextenv] \\
     asm_exists_tac \\ simp [])
 >- simp [circuit_sorted_def] \\

 simp [circuit_run_def, sum_bind_INR] \\
 
 Cases_on `run_decls fbits m.decls []` \\
 drule_strip compile_regs_correct_init_run' \\ impl_tac >- simp [] \\ strip_tac \\ rveq \\
 first_x_assum (qspec_then ‘r’ strip_assume_tac) \\
  
 drule_strip run_decls_fbits \\
 qexists_tac `replace_prefix fbits' fbits m'` \\
 first_x_assum (qspec_then ‘replace_prefix fbits' fbits m'’ mp_tac) \\
 impl_tac >- simp [init_seq_eq_replace_prefix] \\ strip_tac \\ simp [] \\
 fs [shift_seq_replace_prefix] \\ rpt TOP_CASE_TAC \\ fs [] \\

 qpat_x_assum ‘_ ⇒ _’ mp_tac \\
 impl_tac >- (conj_tac >- (first_x_assum irule \\ simp [same_state_def]) \\ 
              drule_strip vertype_list_run_decls) \\ strip_tac \\

 fs [same_state_outs_def, same_state_def]
QED

val _ = export_theory ();
