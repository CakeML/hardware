open hardwarePreamble;

open sumExtraTheory RTLTheory;

val _ = new_theory "RTLType";

(* value type *)

Inductive rtltype_v:
 (rtltype_v (CBool v) CBool_t) /\
 (i = LENGTH vs ==> rtltype_v (CArray vs) (CArray_t i))
End

Theorem rtltype_v_CArray_CBool_t:
 !l. ~rtltype_v (CArray l) CBool_t
Proof
 rw [rtltype_v_cases]
QED

Theorem rtltype_v_CBool_CBool_t:
 !b. rtltype_v (CBool b) CBool_t
Proof
 rw [rtltype_v_cases]
QED

Theorem rtltype_v_CBool_t:
 !v. rtltype_v v CBool_t <=> ?b. v = CBool b
Proof
 rw [rtltype_v_cases]
QED

Theorem rtltype_v_CArray_t:
 !v l. rtltype_v v (CArray_t l) <=> ?b. v = CArray b /\ LENGTH b = l
Proof
 rw [rtltype_v_cases] \\ metis_tac []
QED

Theorem rtltype_v_ground_cases:
 (∀v. rtltype_v v CBool_t ⇔ ∃b. v = CBool b) ∧
 (∀v l. rtltype_v v (CArray_t l) ⇔ ∃bs. v = CArray bs ∧ LENGTH bs = l) ∧
 (∀t b. rtltype_v (CBool b) t ⇔ t = CBool_t) ∧
 (∀t bs. rtltype_v (CArray bs) t ⇔ t = CArray_t $ LENGTH bs)
Proof
 rw [rtltype_v_cases] \\ metis_tac []
QED

Definition rtltype_v_size_def:
 (rtltype_v_size CBool_t = 1) /\
 (rtltype_v_size (CArray_t l) = l)
End

(* executable version of value type *)

Theorem has_rtltype_v_correct:
 !v t. has_rtltype_v v t <=> rtltype_v v t
Proof
 Cases \\ Cases \\ rw [has_rtltype_v_def, rtltype_v_cases]
QED

Theorem has_rtltype_v_CBool_t:
 !v. has_rtltype_v v CBool_t <=> ?b. v = CBool b
Proof
 rw [has_rtltype_v_correct, rtltype_v_CBool_t]
QED

Theorem has_rtltype_v_CArray_t:
 !v l. has_rtltype_v v (CArray_t l) <=> ?b. v = CArray b /\ LENGTH b = l
Proof
 rw [has_rtltype_v_correct, rtltype_v_CArray_t]
QED

(* types for fext *)

Definition rtltype_extenv_def:
 rtltype_extenv extenv fext <=> (!var t. ALOOKUP extenv var = SOME t ==> !n. ?v. fext n var = INR v /\ rtltype_v v t)
End

Definition rtltype_extenv_n_def:
 rtltype_extenv_n extenv fext <=> (!var t. ALOOKUP extenv var = SOME t ==> ?v. fext var = INR v /\ rtltype_v v t)
End

Theorem rtltype_extenv_rtltype_extenv_n:
 !n extenv fext. rtltype_extenv extenv fext ==> rtltype_extenv_n extenv (fext n)
Proof
 rw [rtltype_extenv_def, rtltype_extenv_n_def]
QED

(*
val rtltype_v_bool = rtltype_v_rules |> CONJUNCT1;
val rtltype_v_array = rtltype_v_rules |> CONJUNCT2;

val rtltype_v_cases_imp = rtltype_v_cases |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL;
*)

(*
val (rtltype_cell_inp_rules, rtltype_cell_inp_ind, rtltype_cell_inp_cases) = Hol_reln `
 (!env v. rtltype_v v t ==> rtltype_cell_inp env (ConstInp v) t) /\
 (!env var. env var = SOME t ==> rtltype_cell_inp env (VarInp var) t)`;

(* The 3th field is the netvar num, and the 4th field is the output type *)
val (rtltype_cell_rules, rtltype_cell_ind, rtltype_cell_cases) = Hol_reln `
 (!env n in1.
   rtltype_cell_inp env in1 CBool_t /\
   env (NetVar n) = SOME CBool_t ==>
    rtltype_cell env (Cell1 CNot n in1) CBool_t) /\

 (!env cell n in1 in2.
   (cell = CAnd \/ cell = COr) /\
   rtltype_cell_inp env in1 CBool_t /\
   rtltype_cell_inp env in2 CBool_t /\ 
   env (NetVar n) = SOME CBool_t ==>
    rtltype_cell env (Cell2 cell n in1 in2) CBool_t)`;

(* Informal interpretation: no need to separately declare types of NetVars *)
val (rtltype_cells_rules, rtltype_cells_ind, rtltype_cells_cases) = Hol_reln `
 (rtltype_cells env []) /\

 (rtltype_cell env cell t /\ n = cell_output cell /\ rtltype_cells ((NetVar n =+ SOME t) env) cells ==>
  rtltype_cells env (cell::cells))`;

(*
val rtltype_env_def = Define `
 rtltype_env type_env env <=>
  !var. case cget_var env var of
          INL _ => type_env var = NONE
        | INR v => ?t. type_env var = SOME t /\ rtltype_v v t`;
*)

val rtltype_env_def = Define `
 rtltype_env type_env env <=>
  !var t. type_env var = SOME t ==>
   case cget_var env var of
          INL _ => F
        | INR v => rtltype_v v t`;
*)

val _ = export_theory ();
