open hardwarePreamble;

open alistTheory balanced_mapTheory bitstringTheory numposrepTheory rich_listTheory;

open sumExtraTheory oracleTheory RTLTheory RTLTypeTheory RTLPropsTheory RTLBlasterTheory;

open dep_rewrite;

open RTLSyntax RTLLib;

val _ = new_theory "RTLBlasterProof";

(* this proof/file is kind of a mess after some refactorings... but it works *)

infix THEN2;
infix THEN3;

val lookup_insert_var_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) lookup_insert) var_cmp_good
 |> REWRITE_RULE [var_cmp_antisym];

val lookup_delete_var_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) lookup_delete) var_cmp_good
 |> REWRITE_RULE [var_cmp_antisym];

val insert_thm_var_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) (SPEC_ALL insert_thm)) var_cmp_good;

val delete_thm_var_cmp =
 MATCH_MP (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) (SPEC_ALL delete_thm)) var_cmp_good;

val fromList_thm_var_cmp =
 MATCH_MP fromList_thm var_cmp_good;

Triviality lt1:
 ∀n. n < 1 ⇔ n = 0
Proof
 decide_tac
QED

Triviality lt2:
 ∀b. b < 2 ⇔ b = 0 ∨ b = 1
Proof
 decide_tac
QED

Triviality lt3:
 ∀b. b < 3 ⇔ b = 0 ∨ b = 1 ∨ b = 2
Proof
 decide_tac
QED

Triviality lt4:
 ∀n. n < 4 ⇔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3
Proof
 decide_tac
QED

Triviality le4:
 ∀n. n ≤ 4 ⇔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4
Proof
 decide_tac
QED

Triviality le12:
 ∀n. n ≤ 12 ⇔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
              n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12
Proof
 Cases >- simp [] \\ ntac 6 (Cases_on ‘n'’ >- simp [] \\ Cases_on ‘n’ >- simp []) \\ simp []
QED

Triviality fromList_cons:
 !cmp k v xs. fromList cmp ((k,v)::xs) = insert cmp k v (fromList cmp xs)
Proof
 simp [fromList_def]
QED

Definition blast_rel_bool_def:
 blast_rel_bool fext si bs n b ⇔
  (lookup var_cmp (NetVar n) si = NONE /\ cget_var bs (NetVar n) = INR (CBool b)) ∨
  (∃minp. lookup var_cmp (NetVar n) si = SOME (MBoolInp minp) /\
          case minp of
            GoodInp inp => cell_inp_run fext bs inp = INR (CBool b)
          | BadInp _ _ => T)
End

Definition blast_rel_array_def:
 blast_rel_array fext si bs var b ⇔
  ?minps. lookup var_cmp var si = SOME (MArrayInp minps) /\
          LENGTH minps = LENGTH b /\
          !i. i < LENGTH minps ==>
              case EL i minps of
                GoodInp inp => cell_inp_run fext bs inp = INR (CBool (EL i b))
              | BadInp _ _ => T
End

Theorem blast_rel_array_revEL:
 ∀fext si bs var b.
 blast_rel_array fext si bs var b ⇔
 ∃minps.
   lookup var_cmp var si = SOME (MArrayInp minps) ∧
   LENGTH minps = LENGTH b ∧
   ∀i.
     i < LENGTH minps ⇒
     case revEL i minps of
       GoodInp inp => cell_inp_run fext bs inp = INR (CBool (revEL i b))
     | BadInp _ _ => T
Proof
 rw [blast_rel_array_def, revEL_def] \\ eq_tac \\ rw [] \\ asm_exists_tac \\ rw [] \\
 first_x_assum (qspec_then ‘LENGTH minps - i - 1’ mp_tac) \\ simp []
QED

(* bs for "blast s" *)
Definition blast_rel_def:
 blast_rel fext si tmpnum s bs <=> (* <-- tmpnum here is tmpnum from compiler (not blaster!) *)
  bs.fbits = s.fbits /\
  (* lt check probably redundant when we assume netlist_lt/sorted? *)
  !n. n < tmpnum ==>
      case cget_var s (NetVar n) of
        INL e => T
      | INR (CBool b) => blast_rel_bool fext si bs n b
      | INR (CArray b) => blast_rel_array fext si bs (NetVar n) b
End

(* Note that this does not depend on fext! *)
(* need to know shape of si values to exclude cases that cannot happen + know that updating NetVars does not affect anything reg-related *)
(* the "i = 0" information was needed when proving run_reg thms, might exist better places to store this information *)
Definition blast_reg_rel_def:
 blast_reg_rel si s bs <=>
  bs.fbits = s.fbits /\
  !reg i. case cget_var s (RegVar reg i) of
          INL e => T
        | INR (CBool b) =>
          i = 0 ∧
          ((lookup var_cmp (RegVar reg i) si = NONE ∧ cget_var bs (RegVar reg i) = INR (CBool b))
           ∨
           lookup var_cmp (RegVar reg i) si = SOME (MBoolInp (BadInp reg NONE)))
        | INR (CArray b) =>
          i = 0 ∧
          ((lookup var_cmp (RegVar reg i) si =
            SOME (MArrayInp (GENLIST (λi. GoodInp (VarInp (RegVar reg i) NoIndexing)) (LENGTH b))) ∧
            ∀i. i < LENGTH b ⇒ cget_var bs (RegVar reg i) = INR (CBool (EL i b)))
           ∨
           (lookup var_cmp (RegVar reg i) si =
            SOME (MArrayInp (GENLIST (λi. BadInp reg (SOME i)) (LENGTH b)))))
End

Theorem blast_reg_rel_cong:
 ∀si si' b b' bs bs'.
 blast_reg_rel si b bs ∧
 (∀reg i. lookup var_cmp (RegVar reg i) si' = lookup var_cmp (RegVar reg i) si) ∧
 (∀reg i. cget_var b' (RegVar reg i) = cget_var b (RegVar reg i)) ∧
 (∀reg i. cget_var bs' (RegVar reg i) = cget_var bs (RegVar reg i)) ∧
 b'.fbits = b.fbits ∧
 bs'.fbits = bs.fbits ⇒
 blast_reg_rel si' b' bs'
Proof
 rw [blast_reg_rel_def]
QED

Theorem blast_reg_rel_cong_simple:
 ∀si si' s bs.
 blast_reg_rel si s bs ∧
 (∀reg i. lookup var_cmp (RegVar reg i) si' = lookup var_cmp (RegVar reg i) si) ⇒
 blast_reg_rel si' s bs
Proof
 rw [blast_reg_rel_def]
QED

(* Weaker than blast_reg_rel, references fext so can only be used for one step *)
Definition blast_reg_rel_fext_def:
 blast_reg_rel_fext fext si s bs <=>
  bs.fbits = s.fbits /\
  !reg i. case cget_var s (RegVar reg i) of
          INL e => T
        | INR (CBool b) =>
          i = 0 ∧
          (case lookup var_cmp (RegVar reg i) si of
             NONE => cget_var bs (RegVar reg i) = INR (CBool b)
           | SOME (MBoolInp (GoodInp inp)) => cell_inp_run fext bs inp = INR (CBool b)
           | SOME (MBoolInp (BadInp reg NONE)) => T
           | _ => F)
        | INR (CArray b) =>
          i = 0 ∧
          blast_rel_array fext si bs (RegVar reg i) b
End

Theorem blast_reg_rel_blast_reg_rel_fext:
 ∀fext si s bs. blast_reg_rel si s bs ⇒ blast_reg_rel_fext fext si s bs
Proof
 rw [blast_reg_rel_def, blast_reg_rel_fext_def] \\ first_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\
 rpt TOP_CASE_TAC \\ rpt strip_tac' \\ gvs [blast_rel_array_def, cell_inp_run_def]
QED

Definition blast_cell_input_ok_def:
 (blast_cell_input_ok (VarInp (NetVar n) idx) processed globalmax tmpnum ⇔
  (n < processed ∨ globalmax ≤ n) ∧ n < tmpnum) ∧
 (blast_cell_input_ok _ processed globalmax tmpnum ⇔ T)
End

Theorem blast_cell_input_ok_alt:
 ∀inp processed globalmax tmpnum.
 blast_cell_input_ok inp processed globalmax tmpnum =
 case inp of
   VarInp (NetVar n) idx => ((n < processed ∨ globalmax ≤ n) ∧ n < tmpnum)
 | _ => T
Proof
 rpt gen_tac \\ every_case_tac \\ rw [blast_cell_input_ok_def]
QED

Theorem blast_cell_input_ok_le:
 ∀cell processed processed' max tmpnum tmpnum'.
 blast_cell_input_ok cell processed max tmpnum ∧ processed ≤ processed' ∧ tmpnum ≤ tmpnum' ⇒
 blast_cell_input_ok cell processed' max tmpnum'
Proof
 rw [blast_cell_input_ok_alt] \\ rpt TOP_CASE_TAC \\ fs []
QED

Theorem EVERY_blast_cell_input_ok_le:
 ∀cs processed processed' max tmpnum tmpnum'.
 EVERY (λc. blast_cell_input_ok c processed max tmpnum) cs ∧ processed ≤ processed' ∧ tmpnum ≤ tmpnum' ⇒
 EVERY (λc. blast_cell_input_ok c processed' max tmpnum') cs
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [] \\
 match_mp_tac blast_cell_input_ok_le \\ asm_exists_tac \\ simp []
QED

Definition blast_cell_output_ok_def:
 blast_cell_output_ok cell processed globalmax tmpnum ⇔
 ∀out. MEM out (cell_output cell) ⇒ (processed ≤ out ∧ out < globalmax) ∨ tmpnum ≤ out
End

Theorem blast_cell_output_ok_le:
 ∀cell processed processed' max tmpnum tmpnum'.
 blast_cell_output_ok cell processed max tmpnum ∧ processed' ≤ processed ∧ tmpnum' ≤ tmpnum ⇒
 blast_cell_output_ok cell processed' max tmpnum'
Proof
 rw [blast_cell_output_ok_def] \\ drule_first \\ fs []
QED

Theorem EVERY_blast_cell_output_ok_le:
 ∀cs processed processed' max tmpnum tmpnum'.
 EVERY (λc. blast_cell_output_ok c processed max tmpnum) cs ∧ processed' ≤ processed ∧ tmpnum' ≤ tmpnum ⇒
 EVERY (λc. blast_cell_output_ok c processed' max tmpnum') cs
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [] \\
 match_mp_tac blast_cell_output_ok_le \\ asm_exists_tac \\ simp []
QED

Definition cell_input_ge_def:
 (cell_input_ge (VarInp (NetVar n) idx) m ⇔ m ≤ n) ∧
 (cell_input_ge _ m ⇔ T)
End

Theorem cell_input_ge_alt:
 ∀inp m.
 cell_input_ge inp m =
 case inp of
   VarInp (NetVar n) idx => m ≤ n
 | _ => T
Proof
 rpt gen_tac \\ every_case_tac \\ rw [cell_input_ge_def]
QED

Theorem cell_input_ge_le:
 ∀inp n m. cell_input_ge inp n ∧ m ≤ n ⇒ cell_input_ge inp m
Proof
 rw [cell_input_ge_alt] \\ every_case_tac \\ simp []
QED

Theorem EVERY_cell_input_ge_le:
 ∀inps n m. EVERY (λinp. cell_input_ge inp n) inps ∧ m ≤ n ⇒ EVERY (λinp. cell_input_ge inp m) inps
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [] \\
 match_mp_tac cell_input_ge_le \\ asm_exists_tac \\ simp []
QED

Theorem blast_cell_input_ok_cell_input_lt:
 ∀inp processed max tmpnum. blast_cell_input_ok inp processed max tmpnum ⇒ cell_input_lt inp tmpnum
Proof
 rw [blast_cell_input_ok_alt] \\ every_case_tac \\ simp [cell_input_lt_def, var_lt_def]
QED

Theorem EVERY_blast_cell_input_ok_cell_input_lt:
 ∀inps processed max tmpnum.
 EVERY (λinp. blast_cell_input_ok inp processed max tmpnum) inps ⇒ EVERY (λinp. cell_input_lt inp tmpnum) inps
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [] \\
 match_mp_tac blast_cell_input_ok_cell_input_lt \\ asm_exists_tac
QED

Definition blast_cell_input_marked_ok_def:
 (blast_cell_input_marked_ok (GoodInp inp) processed globalmax tmpnum ⇔
  blast_cell_input_ok inp processed globalmax tmpnum) ∧
 (blast_cell_input_marked_ok _ processed globalmax tmpnum ⇔ T)
End

Theorem blast_cell_input_marked_ok_alt:
 ∀minp processed globalmax tmpnum.
 blast_cell_input_marked_ok minp processed globalmax tmpnum =
 case minp of
   GoodInp (VarInp (NetVar n) idx) => (n < processed ∨ globalmax ≤ n) ∧ n < tmpnum
 | _ => T
Proof
 rpt gen_tac \\ every_case_tac \\ rw [blast_cell_input_marked_ok_def, blast_cell_input_ok_def]
QED

Theorem blast_cell_input_marked_ok_le:
 ∀inp processed processed' globalmax tmpnum tmpnum'.
 blast_cell_input_marked_ok inp processed globalmax tmpnum ∧ processed ≤ processed' ∧ tmpnum ≤ tmpnum' ⇒
 blast_cell_input_marked_ok inp processed' globalmax tmpnum'
Proof
 rw [blast_cell_input_marked_ok_alt] \\ rpt TOP_CASE_TAC \\ fs []
QED

Theorem EVERY_blast_cell_input_marked_ok_le:
 ∀inps processed processed' globalmax tmpnum tmpnum'.
 EVERY (λinp. blast_cell_input_marked_ok inp processed globalmax tmpnum) inps ∧
 processed ≤ processed' ∧ tmpnum ≤ tmpnum' ⇒
 EVERY (λinp. blast_cell_input_marked_ok inp processed' globalmax tmpnum') inps
Proof
 rpt strip_tac \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [] \\ 
 match_mp_tac blast_cell_input_marked_ok_le \\ asm_exists_tac \\ simp []
QED

(*Theorem cell_input_marked_lt_le:
 ∀inp n m. cell_input_marked_lt inp n ∧ n ≤ m ⇒ cell_input_marked_lt inp m
Proof
 Cases \\ simp [cell_input_marked_lt_def] \\ metis_tac [cell_input_lt_le]
QED*)

Definition cell_input_not_pseudo_def:
 (cell_input_not_pseudo regs (VarInp (RegVar reg i) idx) =
  ∀rdata. ALOOKUP regs (reg, i) = SOME rdata ⇒ rdata.reg_type = Reg) ∧
 (cell_input_not_pseudo regs _ = T)
End

Definition cell_input_marked_not_pseudo_def:
 (cell_input_marked_not_pseudo regs (GoodInp inp) = cell_input_not_pseudo regs inp) ∧
 (cell_input_marked_not_pseudo regs (BadInp _ _) = T)
End

(* 
  - processed = have processed cells up to this point
  - globalmax = tmpnum from compiler, all blasted cells allocated after this number
  - tmpnum = current blast tmpnum, nothing exist above this
*)
Definition blasterstate_ok_def:
 blasterstate_ok regs si processed globalmax tmpnum ⇔
  processed ≤ globalmax ∧
  globalmax ≤ tmpnum ∧

  invariant var_cmp si ∧

  (* Non-processed cells not covered yet *)
  (∀m. processed ≤ m ⇒ lookup var_cmp (NetVar m) si = NONE) ∧
  
  (* All pseudo-regs covered *)
  (∀reg i rdata. ALOOKUP regs (reg, i) = SOME rdata ∧ rdata.reg_type = PseudoReg ⇒
                 ∃v. lookup var_cmp (RegVar reg i) si = SOME v) ∧
 
  (* This is so we can allocate new blast cells *)
  (∀var minp. lookup var_cmp var si = SOME (MBoolInp minp) ⇒
              blast_cell_input_marked_ok minp processed globalmax tmpnum) ∧
  (∀var minps. lookup var_cmp var si = SOME (MArrayInp minps) ⇒
               EVERY (λminp. blast_cell_input_marked_ok minp processed globalmax tmpnum) minps) ∧

  (* No pseudo-regs in good inps *)
  (∀var minp. lookup var_cmp var si = SOME (MBoolInp minp) ⇒
              cell_input_marked_not_pseudo regs minp) ∧
  (∀var minps. lookup var_cmp var si = SOME (MArrayInp minps) ⇒
               EVERY (cell_input_marked_not_pseudo regs) minps)
End

(* Can be generalized? *)
Theorem blasterstate_ok_le:
 ∀regs si processed processed' globalmax tmpnum.
 blasterstate_ok regs si processed globalmax tmpnum ∧ processed ≤ processed' ∧ processed' ≤ globalmax ⇒
 blasterstate_ok regs si processed' globalmax tmpnum
Proof
 rw [blasterstate_ok_def] \\ rpt drule_first \\
 TRY (irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ simp [] \\ rpt strip_tac) \\
 match_mp_tac blast_cell_input_marked_ok_le \\ asm_exists_tac \\ simp []
QED

Theorem blast_rel_blast_reg_rel_fext_NONE:
 ∀var fext si s bs tmpnum n v.
 cget_var s var = INR v ∧
 var_lt var n ∧
 n ≤ tmpnum ∧

 lookup var_cmp var si = NONE ∧

 blast_rel fext si tmpnum s bs ∧
 blast_reg_rel_fext fext si s bs ⇒
 (∃b. v = CBool b) ∧ cget_var bs var = INR v
Proof
 Cases \\ rpt strip_tac'
 >- (fs [blast_reg_rel_fext_def, blast_rel_array_def] \\
     first_x_assum (qspecl_then [‘s’, ‘n’] mp_tac) \\ simp [] \\ TOP_CASE_TAC)
 \\ fs [blast_rel_def, var_lt_def] \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ simp [] \\ TOP_CASE_TAC \\ simp [blast_rel_bool_def, blast_rel_array_def]
QED

Theorem blast_rel_blast_reg_rel_fext_SOME_MBoolInp:
 ∀var fext si s bs tmpnum n v inp.
 cget_var s var = INR v ∧
 var_lt var n ∧
 n ≤ tmpnum ∧

 lookup var_cmp var si = SOME (MBoolInp (GoodInp inp)) ∧

 blast_rel fext si tmpnum s bs ∧
 blast_reg_rel_fext fext si s bs ⇒
 (∃b. v = CBool b) ∧ cell_inp_run fext bs inp = INR v
Proof
 Cases \\ rpt strip_tac'
 >- (fs [blast_reg_rel_fext_def, blast_rel_array_def] \\
     first_x_assum (qspecl_then [‘s’, ‘n’] mp_tac) \\ simp [] \\ TOP_CASE_TAC)
 \\ fs [blast_rel_def, var_lt_def] \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ simp [] \\ TOP_CASE_TAC \\ simp [blast_rel_bool_def, blast_rel_array_def]
QED

Theorem blast_rel_blast_reg_rel_fext_SOME_MArrayInp:
 ∀var fext si s bs tmpnum n v minps.
 cget_var s var = INR v ∧
 var_lt var n ∧
 n ≤ tmpnum ∧

 lookup var_cmp var si = SOME (MArrayInp minps) ∧

 blast_rel fext si tmpnum s bs ∧
 blast_reg_rel_fext fext si s bs ⇒
 ∃b. v = CArray b ∧ LENGTH b = LENGTH minps ∧
     ∀i. i < LENGTH minps ⇒
         case EL i minps of
           GoodInp inp => cell_inp_run fext bs inp = INR (CBool (EL i b))
         | BadInp _ _ => T
Proof
 Cases \\ rpt strip_tac'
 >- (fs [blast_reg_rel_fext_def, blast_rel_array_def] \\
     first_x_assum (qspecl_then [‘s’, ‘n’] assume_tac) \\ every_case_tac \\ gvs [cell_inp_run_def])
 \\ fs [blast_rel_def, var_lt_def] \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ simp [] \\ TOP_CASE_TAC \\ simp [blast_rel_bool_def, blast_rel_array_def]
QED

Theorem blast_rel_blast_reg_rel_fext_SOME_MArrayInp_Indexing:
 ∀var fext si s bs tmpnum n v v' minps i inp.
 cget_var s var = INR v' ∧
 cget_fext_var (Indexing i) v' = INR v ∧
 var_lt var n ∧
 n ≤ tmpnum ∧

 lookup var_cmp var si = SOME (MArrayInp minps) ∧
 i < LENGTH minps ∧ revEL i minps = GoodInp inp ∧

 blast_rel fext si tmpnum s bs ∧
 blast_reg_rel_fext fext si s bs ⇒
 cell_inp_run fext bs inp = INR v ∧ ∃b. v = CBool b
Proof
 rpt strip_tac' \\ drule_strip blast_rel_blast_reg_rel_fext_SOME_MArrayInp \\
 gvs [cget_fext_var_def, sum_map_INR, sum_revEL_INR, revEL_def] \\
 first_x_assum (qspec_then ‘LENGTH minps - (i + 1)’ mp_tac) \\ simp []
QED

Theorem blast_rel_blast_reg_rel_fext_SOME_MArrayInp_fail_case:
 ∀var.
 cget_var s var = INR (CArray b) ∧
 var_lt var n ∧
 n ≤ tmpnum ∧

 lookup var_cmp var si = SOME (MArrayInp minps) ∧

 blast_rel fext si tmpnum s bs ∧
 blast_reg_rel_fext fext si s bs ⇒
 LENGTH minps = LENGTH b
Proof
 Cases \\ rpt strip_tac'
 >- (fs [blast_reg_rel_fext_def, blast_rel_array_def] \\
     first_x_assum (qspecl_then [‘s'’, ‘n'’] assume_tac) \\ rfs [])
 \\ fs [blast_rel_def, var_lt_def] \\ first_x_assum (qspec_then ‘n'’ assume_tac) \\ rfs [blast_rel_array_def]
QED

Theorem blast_cell_inp_run_correct_bool:
 !inp tmpnum inp' fext s bs v blast_s n.
 blast_cell_input blast_s inp = INR (BoolInp inp') /\
 cell_inp_run fext s inp = INR v /\
 rtltype_extenv_n blast_s.extenv fext /\
 blast_rel fext blast_s.si tmpnum s bs /\
 blast_reg_rel_fext fext blast_s.si s bs ∧
 cell_input_lt inp n /\
 cell_input_covered_by_extenv blast_s.extenv inp /\
 n <= tmpnum ==>
 cell_inp_run fext bs inp' = INR v /\ ?b. v = CBool b
Proof
 Cases
 >- (Cases_on `v` \\ simp [cell_inp_run_def, blast_cell_input_def])

 >- (simp [cell_inp_run_def, sum_bind_INR, blast_cell_input_def, rtltype_extenv_n_def,
           cell_input_covered_by_extenv_def] \\ rpt strip_tac' \\ drule_first \\
     every_case_tac \\ gvs [rtltype_v_cases, cell_inp_run_def, sum_bind_def, sum_map_INR, cget_fext_var_def]) \\

 simp [cell_inp_run_def, sum_bind_INR, blast_cell_input_def, cell_input_lt_def] \\ rpt gen_tac \\
 TOP_CASE_TAC >- (rpt strip_tac' \\ rveq \\
                  drule_strip blast_rel_blast_reg_rel_fext_NONE \\
                  fs [cell_inp_run_def, cget_fext_var_def, sum_bind_def] \\
                  every_case_tac \\ gvs []) \\
 TOP_CASE_TAC >- (TOP_CASE_TAC \\ rpt strip_tac' \\
                  drule_strip blast_rel_blast_reg_rel_fext_SOME_MBoolInp \\
                  fs [cget_fext_var_def] \\
                  every_case_tac \\ gvs []) \\
 every_case_tac \\ simp [sum_map_INR] \\ rpt strip_tac'
 >- (fs [inp_marked_get_INR] \\ drule_strip blast_rel_blast_reg_rel_fext_SOME_MArrayInp_Indexing \\ simp []) \\
 rveq \\ fs [cget_fext_var_def] \\ every_case_tac \\ gvs [sum_map_INR, sum_revEL_INR] \\
 drule_strip blast_rel_blast_reg_rel_fext_SOME_MArrayInp_fail_case \\ fs []
QED

Theorem blast_cell_inp_run_correct_array:
 !inp n tmpnum fext s bs v blast_s inps.
 blast_cell_input blast_s inp = INR (ArrayInp inps) /\
 cell_inp_run fext s inp = INR v /\
 rtltype_extenv_n blast_s.extenv fext /\
 blast_rel fext blast_s.si tmpnum s bs /\
 blast_reg_rel_fext fext blast_s.si s bs ∧
 cell_input_lt inp n /\
 cell_input_covered_by_extenv blast_s.extenv inp ∧
 n <= tmpnum ==>
 ?b. v = CArray b /\ LENGTH b = LENGTH inps /\
     (!i. i < LENGTH inps ==> cell_inp_run fext bs (EL i inps) = INR (CBool (EL i b)))
Proof
 Cases
 >- (Cases_on `v` \\ simp [cell_inp_run_def, blast_cell_input_def, EL_MAP])

 >- (simp [cell_inp_run_def, sum_bind_INR, blast_cell_input_def, rtltype_extenv_n_def, cell_input_covered_by_extenv_def] \\
     rpt strip_tac \\ every_case_tac \\ fs [cget_fext_var_def] \\ rveq \\
     drule_first \\ fs [rtltype_v_cases] \\ rveq \\
     fs [cell_inp_run_def, sum_bind_def, cget_fext_var_def, sum_revEL_revEL, revEL_def, sum_map_def,
         EL_TAKE, EL_DROP]) \\

 simp [cell_inp_run_def, cell_input_lt_def, blast_cell_input_def] \\
 rpt gen_tac \\ rpt TOP_CASE_TAC \\ simp [sum_map_INR, sum_bind_INR] \\
 rpt strip_tac' \\ drule_strip blast_rel_blast_reg_rel_fext_SOME_MArrayInp \\
 fs [sum_mapM_EL, inp_marked_get_INR, cget_fext_var_def, length_rev_slice] \\ rpt strip_tac'
 >- (rpt drule_first \\ fs []) \\
 last_x_assum drule \\ simp [rev_slice_def, EL_TAKE, EL_DROP] \\ 
 qmatch_goalsub_abbrev_tac ‘EL idx l = _’ \\
 first_x_assum (qspec_then ‘idx’ mp_tac) \\
 unabbrev_all_tac \\ rpt strip_tac \\ fs []
QED

Theorem cell_input_lt_blast_cell_input_ok:
 cell_input_lt inp processed ∧ processed ≤ tmpnum ⇒ blast_cell_input_ok inp processed max tmpnum
Proof
 Cases_on ‘inp’ \\ simp [blast_cell_input_ok_def] \\
 Cases_on ‘v’ \\ simp [cell_input_lt_def, blast_cell_input_ok_def, var_lt_def]
QED

Theorem blast_cell_input_cell_input_marked_ok_bool:
 !inp blast_s inp' tmpnum regs processed max.
 blast_cell_input blast_s inp = INR (BoolInp inp') /\
 (∀var minp. lookup var_cmp var blast_s.si = SOME (MBoolInp minp) ⇒
             blast_cell_input_marked_ok minp processed max tmpnum) ∧
 (∀var minps. lookup var_cmp var blast_s.si = SOME (MArrayInp minps) ⇒
              EVERY (λminp. blast_cell_input_marked_ok minp processed max tmpnum) minps) ∧
 cell_input_lt inp processed ∧ processed ≤ tmpnum ==> (* was less-than tmpnum before *)
 blast_cell_input_ok inp' processed max tmpnum
Proof
 Cases
 >- (Cases_on `v` \\ rw [blast_cell_input_def] \\ rw [blast_cell_input_ok_def])

 >- (rw [blast_cell_input_def] \\ every_case_tac \\ rw [blast_cell_input_ok_def])

 >- (rw [blast_cell_input_def] \\ every_case_tac \\ fs [cell_input_lt_blast_cell_input_ok] \\ drule_first \\
     gvs [sum_map_INR, EVERY_revEL, inp_marked_get_INR, blast_cell_input_ok_def] \\
     metis_tac [blast_cell_input_marked_ok_def])
QED

(* previous name: blast_cell_input_SOME_bool *)
Theorem blast_cell_input_cell_input_lt_bool:
 !inp blast_s inp' tmpnum regs processed max.
 blast_cell_input blast_s inp = INR (BoolInp inp') /\
 blasterstate_ok regs blast_s.si processed max tmpnum ∧
 cell_input_lt inp processed ∧ processed ≤ tmpnum ⇒ (* was less-than tmpnum before *)
 cell_input_lt inp' tmpnum
Proof
 rw [blasterstate_ok_def] \\
 drule_strip blast_cell_input_cell_input_marked_ok_bool \\
 first_x_assum (qspec_then ‘regs'’ assume_tac) \\
 irule blast_cell_input_ok_cell_input_lt \\ asm_exists_tac
QED

Theorem blast_cell_input_cell_input_marked_ok_array:
 !inp blast_s inps tmpnum regs processed max.
 blast_cell_input blast_s inp = INR (ArrayInp inps) /\
 (∀var minp. lookup var_cmp var blast_s.si = SOME (MBoolInp minp) ⇒
             blast_cell_input_marked_ok minp processed max tmpnum) ∧
 (∀var minps. lookup var_cmp var blast_s.si = SOME (MArrayInp minps) ⇒
              EVERY (λminp. blast_cell_input_marked_ok minp processed max tmpnum) minps) ⇒
 EVERY (\inp. blast_cell_input_ok inp processed max tmpnum) inps
Proof
 Cases
 >- (Cases_on `v` \\ rw [blast_cell_input_def] \\
    rw [EVERY_MEM, MEM_MAP] \\ simp [blast_cell_input_ok_def])

 >- (rpt gen_tac \\ simp [blast_cell_input_def] \\ every_case_tac \\ strip_tac \\ rveq \\
    rw [EVERY_MEM, MEM_GENLIST] \\ simp [blast_cell_input_ok_def])

 >- (rw [blast_cell_input_def] \\ every_case_tac \\ fs [] \\ rpt drule_first \\
     fs [sum_map_INR, EVERY_MEM] \\ rpt strip_tac \\ drule_strip sum_mapM_MEM \\
     TRY (drule_strip MEM_rev_slice) \\ drule_first \\
     gvs [inp_marked_get_INR, blast_cell_input_marked_ok_def])
QED

(* previous name: blast_cell_input_SOME *)
Theorem blast_cell_input_cell_input_lt_array:
 !inp blast_s inps tmpnum regs processed max.
 blast_cell_input blast_s inp = INR (ArrayInp inps) ∧
 blasterstate_ok regs blast_s.si processed max tmpnum ⇒
 EVERY (λinp. cell_input_lt inp tmpnum) inps
Proof
 rw [blasterstate_ok_def] \\
 drule_strip blast_cell_input_cell_input_marked_ok_array \\
 first_x_assum (qspec_then ‘regs'’ assume_tac) \\
 irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [] \\
 irule blast_cell_input_ok_cell_input_lt \\ asm_exists_tac
QED

(*Theorem blast_cell_input_cell_input_lt_gen:
 !inp minp tmpnum blast_s.
 blast_cell_input blast_s inp = INR minp /\
 (∀var minp. lookup var_cmp var blast_s.si = SOME (MBoolInp minp) ⇒
             cell_input_marked_lt minp tmpnum) ∧
 (∀var minps. lookup var_cmp var blast_s.si = SOME (MArrayInp minps) ⇒
              EVERY (λminp. cell_input_marked_lt minp tmpnum) minps) ⇒
 case minp of
   BoolInp inp' => cell_input_lt inp tmpnum ⇒ cell_input_lt inp' tmpnum
 | ArrayInp inps => EVERY (\inp. cell_input_lt inp tmpnum) inps
Proof
 rpt strip_tac \\ Cases_on ‘minp’
 >- (drule_strip blast_cell_input_cell_input_lt_bool \\ simp [])
 >- (drule_strip blast_cell_input_cell_input_lt_array \\ simp [])
QED*)

Theorem blast_cell_input_cell_input_marked_ok:
 !inp minp tmpnum blast_s regs processed max.
 blast_cell_input blast_s inp = INR minp /\
 blasterstate_ok regs blast_s.si processed max tmpnum ∧
 cell_input_lt inp processed ∧ processed ≤ tmpnum (* <-- strictly speaking only needed for bool case *) ⇒
 case minp of
   BoolInp inp' => blast_cell_input_ok inp' processed max tmpnum
 | ArrayInp inps => EVERY (\inp. blast_cell_input_ok inp processed max tmpnum) inps
Proof
 rw [blasterstate_ok_def] \\ TOP_CASE_TAC
 >- (drule_strip blast_cell_input_cell_input_marked_ok_bool \\ simp [])
 >- (drule_strip blast_cell_input_cell_input_marked_ok_array \\ simp [])
QED

Theorem blast_cell_input_not_pseudo:
 ∀inp blast_s regs tinp processed globalmax tmpnum.
 blast_cell_input blast_s inp = INR tinp ∧
 blasterstate_ok regs blast_s.si processed globalmax tmpnum ⇒
 case tinp of
   BoolInp inp => cell_input_not_pseudo regs inp
 | ArrayInp inps => EVERY (cell_input_not_pseudo regs) inps
Proof
 Cases
 >- (Cases_on `v` \\ rw [blast_cell_input_def] \\ simp [cell_input_not_pseudo_def, EVERY_MAP])

 >- (rpt gen_tac \\ simp [blast_cell_input_def] \\ every_case_tac \\ strip_tac \\ rveq \\
     rw [EVERY_MEM, MEM_GENLIST] \\ simp [cell_input_not_pseudo_def]) \\

 rename1 ‘VarInp var idx’ \\
 fs [blast_cell_input_def] \\ rpt gen_tac \\
 TOP_CASE_TAC >- (rw [blasterstate_ok_def] \\ simp [] \\
                  Cases_on ‘var’ \\ rw [cell_input_not_pseudo_def] \\ drule_first \\
                  Cases_on ‘rdata.reg_type’ \\ simp []) \\
 TOP_CASE_TAC >- (TOP_CASE_TAC \\ rw [blasterstate_ok_def] \\ drule_first \\
                  fs [cell_input_marked_not_pseudo_def]) \\
 TOP_CASE_TAC \\ rw [cell_input_not_pseudo_def, sum_map_INR, blasterstate_ok_def] \\ drule_first
 >- (fs [EVERY_MEM] \\ rpt strip_tac \\ drule_strip sum_mapM_MEM \\ drule_first \\
     gvs [inp_marked_get_INR, cell_input_marked_not_pseudo_def])
 >- (fs [EVERY_revEL, inp_marked_get_INR] \\ drule_first \\ gvs [cell_input_marked_not_pseudo_def])
 >- (fs [EVERY_MEM] \\ rpt strip_tac \\ drule_strip sum_mapM_MEM \\ drule_strip MEM_rev_slice \\
     drule_first \\ gvs [inp_marked_get_INR, cell_input_marked_not_pseudo_def])
QED

Theorem blasterstate_ok_insert:
 !regs si min max globalmax tmpnum tmpnum' out minp.
 blasterstate_ok regs si min globalmax tmpnum ∧
 cell_output_ok min max out ∧
 (case minp of
    MBoolInp inp => blast_cell_input_marked_ok inp max globalmax tmpnum' ∧
                    cell_input_marked_not_pseudo regs inp
  | MArrayInp inps => EVERY (λminp. blast_cell_input_marked_ok minp max globalmax tmpnum') inps ∧
                      EVERY (cell_input_marked_not_pseudo regs) inps) ∧
 max ≤ globalmax ∧
 tmpnum ≤ tmpnum' ⇒
 blasterstate_ok regs (insert var_cmp (NetVar out) minp si) max globalmax tmpnum'
Proof
 simp [blasterstate_ok_def, lookup_insert_var_cmp, insert_thm_var_cmp, cell_output_ok_def] \\
 rpt strip_tac' \\ rpt conj_tac \\ rpt gen_tac \\
 IF_CASES_TAC \\ strip_tac \\ fs  [] \\

 rpt drule_first \\
 TRY (irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw []) \\
 match_mp_tac blast_cell_input_marked_ok_le \\ asm_exists_tac \\ simp []
QED

(* Somewhat overkill do not simply do this inline *)
Theorem blasterstate_ok_insert_cell1:
 !regs si min max globalmax tmpnum out l.
 blasterstate_ok regs si min globalmax tmpnum ∧ cell_output_ok min max out ∧ max ≤ globalmax ⇒
 blasterstate_ok regs
                 (insert var_cmp (NetVar out)
                                 (MArrayInp (GENLIST (λi. GoodInp (VarInp (NetVar (i + tmpnum)) NoIndexing)) l)) si)
                 max globalmax (l + tmpnum)
Proof
 rpt strip_tac \\ match_mp_tac blasterstate_ok_insert \\ asm_exists_tac \\
 fs [blasterstate_ok_def, EVERY_GENLIST,
     blast_cell_input_marked_ok_def, blast_cell_input_ok_def,
     cell_input_marked_not_pseudo_def, cell_input_not_pseudo_def]
QED

Theorem cell1_bitwise_correct:
 !fext inps tmpnum b s.
 EVERY (\inp. cell_input_lt inp tmpnum) inps /\
 (!i. i < LENGTH inps ==> cell_inp_run fext s (EL i inps) = INR (CBool (EL i b))) /\
 LENGTH b = LENGTH inps ==>
 ?s'. sum_foldM (cell_run fext) s (MAPi (λi inp. Cell1 CNot (i + tmpnum) inp) inps) =
      INR s' /\
      s'.fbits = s.fbits /\ (* <-- follows from general determinism thm... *)
      (!inp. cell_input_lt inp tmpnum ==> cell_inp_run fext s' inp = cell_inp_run fext s inp) /\
      (!i. i < LENGTH inps ==> cell_inp_run fext s' (VarInp (NetVar (i + tmpnum)) NoIndexing) =
                               INR (CBool ~(EL i b)))
Proof
 gen_tac \\ Induct \\ rw [sum_foldM_def, sum_bind_INR, cell_run_def] \\
 Cases_on `b` \\ fs [] \\
 first_assum (qspec_then `0` mp_tac) \\ impl_tac >- simp [] \\ PURE_REWRITE_TAC [EL, HD] \\
 strip_tac \\ simp [PULL_EXISTS, cell1_run_def] \\

 qmatch_goalsub_abbrev_tac `sum_foldM _ s' _` \\
 first_x_assum (qspecl_then [`SUC tmpnum`, `t`, `s'`] mp_tac) \\
 unabbrev_all_tac \\
 impl_tac >- (
 conj_tac >- (irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rw [cell_input_lt_SUC]) \\
 reverse conj_tac >- simp [] \\
 rpt strip_tac \\
 first_x_assum (qspec_then `SUC i` mp_tac) \\ simp [] \\
 Cases_on `EL i inps` \\ simp [cell_inp_run_def, cget_var_cset_var] \\
 fs [EVERY_EL] \\ drule_first \\ rfs [cell_input_lt_def] \\
 Cases_on `v` \\ fs [var_lt_def]) \\ strip_tac \\

 `((λi inp. Cell1 CNot (i + tmpnum) inp) ∘ SUC) = (λi inp. Cell1 CNot (i + SUC tmpnum) inp)` by
 simp [FUN_EQ_THM] \\ pop_assum (fn th => rewrite_tac [th]) \\ simp [cset_var_fbits] \\

 conj_tac >- (rpt strip_tac \\ first_x_assum (qspec_then `inp` mp_tac) \\
              simp [cell_input_lt_SUC, cell_input_lt_cell_inp_run_cset_var]) \\

 Cases >- (simp [] \\ first_x_assum (qspec_then `VarInp (NetVar tmpnum) NoIndexing` mp_tac) \\
          simp [cell_input_lt_def, var_lt_def, cell_inp_run_cset_var]) \\

 simp [] \\ strip_tac \\ drule_first \\ fs [arithmeticTheory.ADD1]
QED

Theorem gol_mux_array_correct:
 ∀c not_c inpt inpf c' inpt' inpf' tmpnum fext s.
 cell_inp_run fext s c = INR (CBool c') ∧
 cell_inp_run fext s not_c = INR (CBool (¬c')) ∧
 cell_inp_run fext s inpt = INR (CBool inpt') ∧
 cell_inp_run fext s inpf = INR (CBool inpf') ∧
 cell_input_lt c tmpnum ∧
 cell_input_lt not_c tmpnum ∧
 cell_input_lt inpt tmpnum ∧
 cell_input_lt inpf tmpnum ⇒
 ∃s'. sum_foldM (cell_run fext) s (gol_mux_array tmpnum c not_c inpt inpf) = INR s' ∧
      s'.fbits = s.fbits ∧
      (!inp. cell_input_lt inp tmpnum ==> cell_inp_run fext s' inp = cell_inp_run fext s inp) ∧
      (cell_inp_run fext s' (VarInp (NetVar (tmpnum + 2)) NoIndexing) = INR (CBool (if c' then inpt' else inpf')))
Proof
 simp [gol_mux_array_def, sum_foldM_def, cell_run_def, cell2_run_def, sum_bind_def, sum_bind_INR] \\ rpt strip_tac' \\
 simp [cell_input_lt_cell_inp_run_cset_var_plus, cell2_run_def] \\
 simp [cell_inp_run_cset_var, cell2_run_def] \\ rw [cell_input_lt_cell_inp_run_cset_var_plus]
QED

Theorem blast_cellMux_correct:
 !lhs rhs c not_c s lhs' rhs' c' tmpnum fext.
 LENGTH lhs = LENGTH rhs ∧
 LENGTH lhs' = LENGTH lhs ∧
 LENGTH rhs' = LENGTH rhs ∧
 cell_input_lt c tmpnum ∧
 EVERY (\inp. cell_input_lt inp tmpnum) lhs ∧
 EVERY (\inp. cell_input_lt inp tmpnum) rhs ∧
 (!i. i < LENGTH lhs ==> cell_inp_run fext s (EL i lhs) = INR (CBool (EL i lhs'))) ∧
 (!i. i < LENGTH rhs ==> cell_inp_run fext s (EL i rhs) = INR (CBool (EL i rhs'))) ∧
 cell_inp_run fext s c = INR (CBool c') ∧
 cell_input_lt not_c tmpnum ∧
 cell_inp_run fext s not_c = INR (CBool ~c') ⇒
 ∃s'. sum_foldM (cell_run fext) s (FLAT (MAP2i (λi inp2 inp3. gol_mux_array (3*i + tmpnum) c not_c inp2 inp3) lhs rhs)) = INR s' /\
      s'.fbits = s.fbits /\ (* <-- follows from general determinism thm... *)
      (!inp. cell_input_lt inp tmpnum ==> cell_inp_run fext s' inp = cell_inp_run fext s inp) /\
      (!i. i < LENGTH lhs ==> cell_inp_run fext s' (VarInp (NetVar (3*i + tmpnum + 2)) NoIndexing) =
                              INR (CBool (EL i (if c' then lhs' else rhs'))))
Proof
 Induct >- rw [sum_foldM_def] \\ Cases_on ‘lhs'’ >- rw [] \\ Cases_on ‘rhs’ >- rw [] \\ Cases_on ‘rhs'’ >- rw [] \\
 simp [sum_foldM_append, sum_bind_INR] \\ rpt strip_tac' \\

 first_assum (qspec_then `0` mp_tac) \\ impl_tac >- simp [] \\
 last_assum (qspec_then `0` mp_tac) \\ impl_tac >- simp [] \\ 
 PURE_REWRITE_TAC [EL, HD] \\ rpt strip_tac \\ 
 
 rename1 ‘gol_mux_array _ _ _ inpt inpf’ \\
 qspecl_then [‘c’, ‘not_c’, ‘inpt’, ‘inpf’] assume_tac gol_mux_array_correct \\ drule_first \\ simp [] \\
 
 first_x_assum (qspecl_then [‘t'’, ‘c’, ‘not_c’, ‘s'’, ‘t’, ‘t''’, ‘c'’, ‘tmpnum + 3’, ‘fext’] mp_tac) \\
 impl_tac >- (rw [cell_input_lt_cell_inp_run_cset_var]
 >- (match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])
 THEN2 (match_mp_tac EVERY_cell_input_lt_le \\ asm_exists_tac \\ simp [])
 THEN2 (rpt (first_x_assum (qspec_then ‘SUC i’ mp_tac)) \\ fs [EVERY_EL, cell_input_lt_cell_inp_run_cset_var])
 >- (match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])) \\ strip_tac \\

 ‘((λi inp2 inp3. gol_mux_array (3 * i + tmpnum) c not_c inp2 inp3) ∘ SUC) =
  (λi inp2 inp3. gol_mux_array (3 * i + (tmpnum + 3)) c not_c inp2 inp3)’
 by (rw [FUN_EQ_THM] \\ f_equals_tac \\ decide_tac) \\ simp [] \\

 rpt strip_tac
 >- (drule_strip cell_input_lt_le \\ simp [])
 \\ Cases_on ‘i’ \\ fs []
 >- (first_x_assum (qspec_then ‘VarInp (NetVar (tmpnum + 2)) NoIndexing’ mp_tac) \\
     impl_tac >- simp [cell_input_lt_def, var_lt_def] \\ strip_tac \\ rw [cell_inp_run_cset_var])
 \\ drule_first \\ rw [] \\ gs [arithmeticTheory.ADD1] \\ first_x_assum (qspec_then ‘n’ mp_tac) \\
    disch_then (assume_tac o GSYM) \\ simp [] \\ f_equals_tac \\ decide_tac
QED

Triviality Abbrev_cset_var_tmpvar_lem:
 ∀s s' n v. Abbrev (s' = cset_var s (NetVar n) v) ⇒ (∀var. var_lt var n ⇒ cget_var s' var = cget_var s var)
Proof
 rw [markerTheory.Abbrev_def, cget_var_cset_var] \\ rw [] \\ fs [var_lt_def]
QED

Theorem cell_inp_run_lt_cget_var_cong:
 ∀inp fext s s' n m.
 (∀var. var_lt var n ⇒ cget_var s' var = cget_var s var) ∧ cell_input_lt inp m ∧ m ≤ n ⇒
 cell_inp_run fext s' inp = cell_inp_run fext s inp
Proof
 Cases \\ rw [cell_inp_run_def, cell_input_lt_def] \\ drule_strip var_lt_le \\ simp []
QED

(*Theorem cell_inp_run_cell_input_lt_cong:
 ∀inp fext s s' n m.
 (∀inp. cell_input_lt inp n ⇒ cell_inp_run fext s' inp = cell_inp_run fext s inp) ∧ cell_input_lt inp m ∧ m ≤ n ⇒
 cell_inp_run fext s' inp = cell_inp_run fext s inp
Proof
 rpt strip_tac \\ first_x_assum match_mp_tac \\ match_mp_tac cell_input_lt_le \\ rpt asm_exists_tac
QED*)

Theorem EVERY_cell_inp_run_lt_cget_var_cong:
 ∀inps fext s s' n m.
 (∀var. var_lt var n ⇒ cget_var s' var = cget_var s var) ∧ EVERY (λinp. cell_input_lt inp m) inps ∧ m ≤ n ⇒
 ∀i. i < LENGTH inps ⇒ cell_inp_run fext s' (EL i inps) = cell_inp_run fext s (EL i inps)
Proof
 rw [EVERY_EL] \\ drule_first \\ match_mp_tac cell_inp_run_lt_cget_var_cong \\ rpt asm_exists_tac
QED
                                                                                               
Definition inps2n_def:
 inps2n fext s inps = sum_map v2n $ sum_mapM (λinp. sum_bind (cell_inp_run fext s inp) get_bool) inps
End

Theorem inps2n_lt:
 ∀inps fext s n. inps2n fext s inps = INR n ⇒ n < 2 ** LENGTH inps
Proof
 rw [inps2n_def, sum_map_INR, sum_mapM_EL] \\ metis_tac [v2n_lt]
QED

Theorem inps2n_nil:
 ∀fext s. inps2n fext s [] = INR 0
Proof
 rpt gen_tac \\ EVAL_TAC
QED

Theorem inps2n_sing:
 ∀fext s inp b.
 cell_inp_run fext s inp = INR (CBool b) ⇒ inps2n fext s [inp] = INR (if b then 1 else 0)
Proof
 simp [inps2n_def, sum_mapM_def, sum_bind_def, get_bool_def, sum_map_INR, v2n_sing]
QED

Theorem inps2n_F:
 ∀fext s. inps2n fext s [ConstInp (CBool F)] = INR 0
Proof
 rpt gen_tac \\ EVAL_TAC
QED

Triviality zero_extend_suc:
 ∀l n. LENGTH l ≤ n ⇒ zero_extend (SUC n) l = F :: zero_extend n l
Proof
 rw [zero_extend_def, PAD_LEFT] \\ ‘SUC n − LENGTH l = SUC (n - LENGTH l)’ by decide_tac \\
 pop_assum (rewrite_tac o sing) \\ simp [GENLIST_CONS]
QED

Triviality length_dropwhile_sub_length:
 ∀l P. LENGTH (dropWhile P l) − LENGTH l = 0
Proof
 simp [LENGTH_dropWhile_LESS_EQ]
QED

Triviality fixwidth_dropWhile_F:
 ∀l. fixwidth (LENGTH l) (dropWhile ($<=> F) l) = l
Proof
 Induct \\ rw [fixwidth_def] \\ fs [] \\ qspecl_then [‘$<=> F’, ‘l’] assume_tac LENGTH_dropWhile_LESS_EQ
 >- (fs [zero_extend_suc, fixwidth_def] \\ every_case_tac \\ fs [length_dropwhile_sub_length, zero_extend_id])
 \\ fs [arithmeticTheory.ADD1]
QED

Triviality el_inps2n_lem:
 ∀inps fext s n i.
 inps2n fext s inps = INR n ∧ i < LENGTH inps ⇒
 cell_inp_run fext s (EL i inps) = INR $ CBool $ EL i (fixwidth (LENGTH inps) (n2v n))
Proof
 simp [inps2n_def, sum_map_INR] \\ rpt strip_tac \\ rveq \\ simp [n2v_v2n] \\ 
 fs [sum_mapM_EL] \\ drule_first \\ fs [sum_bind_INR, get_bool_INR] \\ rveq \\
 IF_CASES_TAC >- fs [EVERY_EL, fixwidth_F] \\ 
 qpat_x_assum ‘LENGTH _ = LENGTH _’ (assume_tac o GSYM) \\ simp [fixwidth_dropWhile_F]
QED

Theorem inps2n_append:
 ∀l1 l2 n fext s.
 inps2n fext s (l1 ++ l2) = INR n ⇔
 ∃n1 n2. inps2n fext s l1 = INR n1 ∧ inps2n fext s l2 = INR n2 ∧ n = n1*2**(LENGTH l2) + n2
Proof
 rw [inps2n_def] \\ fs [sum_map_INR, sum_mapM_append] \\ eq_tac \\ rw [v2n_append, PULL_EXISTS] \\
 imp_res_tac length_sum_mapM \\ simp []
QED

(* Too weak to be an eq currently *)
Theorem inps2n_INR:
 ∀inps s fext n.
 inps2n fext s inps = INR n ⇒
 EVERY (λinp. ∃b. cell_inp_run fext s inp = INR $ CBool b) inps
Proof
 rw [EVERY_EL] \\ drule_strip el_inps2n_lem \\ simp []
QED

(* hack: *)
Theorem inps2n_sing_INR:
 ∀inp s fext n. inps2n fext s [inp] = INR n ⇔ ∃b. cell_inp_run fext s inp = INR $ CBool b ∧ n = v2n [b]
Proof
 rw [inps2n_def, sum_mapM_def] \\ CASE_TAC \\ rw [sum_map_def, sum_bind_def] \\
 gvs [sum_bind_def, get_bool_def, sum_bind_INR, v2n_sing, get_bool_INR] \\ rw []
QED

Triviality inps2n_v2n_lem:
 ∀l s fext bs.
 (∀i. i < LENGTH l ⇒ cell_inp_run fext s (EL i l) = INR (CBool (EL i bs))) ∧ LENGTH bs = LENGTH l ⇒
 inps2n fext s l = INR (v2n bs)
Proof
 rw [inps2n_def, sum_map_INR, sum_mapM_EL] \\ qexists_tac ‘bs’ \\ rw [] \\ drule_first \\
 simp [sum_bind_def, get_bool_def]
QED

Triviality n2l_2_2pow_lem:
 ∀n a. a < 2**n ⇒ n2l 2 (a + 2 ** n) = if a = 0 then PAD_LEFT 0 (n + 1) [1] else PAD_RIGHT 0 n (n2l 2 a) ++ [1]
Proof
 (* Can be cleaned up probably, but I don't want to touch this proof right now... *)
 Induct >- simp [lt1, PAD_LEFT] \\ rpt strip_tac \\ simp [Once n2l_def] \\
 IF_CASES_TAC >- (fs [arithmeticTheory.EXP] \\ Cases_on ‘a’ \\ fs [] \\ Cases_on ‘n'’ \\ fs []) \\
 simp [arithmeticTheory.ZERO_EXP] \\ ‘(a + 2 ** SUC n) = (2 ** n * 2 + a)’ by fs [arithmeticTheory.EXP] \\
 pop_assum (rewrite_tac o sing) \\ DEP_REWRITE_TAC [arithmeticTheory.ADD_DIV_ADD_DIV] \\ simp [] \\
 first_x_assum (qspec_then ‘a DIV 2’ mp_tac) \\ impl_tac >- simp [arithmeticTheory.EXP2_LT] \\ strip_tac \\
 simp [] \\ CONV_TAC (RHS_CONV (REWRITE_CONV [Once n2l_def])) \\ simp [] \\
 Cases_on ‘a’ >- (simp [PAD_LEFT, GENLIST_CONS]) \\ simp [] \\ Cases_on ‘n'’ >- (simp [PAD_LEFT, PAD_RIGHT]) \\ simp [] \\
 simp [PAD_LEFT, PAD_RIGHT] \\ rw [] \\ Cases_on ‘n’ \\ fs [GENLIST_CONS]
QED

Triviality length_n2l_bound_lem:
 ∀a n. a ≠ 0 ∧ a < 2 ** n ⇒ LENGTH (n2l 2 a) ≤ n
Proof
 rpt gen_tac \\ Cases_on ‘n = 0’ >- simp [] \\
 simp [LENGTH_n2l] \\ rpt strip_tac \\ ‘a <= 2 ** n - 1’ by decide_tac \\ ‘0 < a’ by decide_tac \\
 drule_strip bitTheory.LOG2_LE_MONO \\ rfs [log2_twoexp_sub1, bitTheory.LOG2_def]
QED

Triviality fixwidth_sum_2pow_lem:
 ∀n a. a < 2**n ⇒ n2v (a + 2 ** n) = T :: fixwidth n (n2v a)
Proof
 rw [n2v_def, boolify_reverse_map, num_to_bin_list_def] \\
 drule_strip n2l_2_2pow_lem \\ rw []
 >- simp [PAD_LEFT, fixwidth_F, MAP_GENLIST, REVERSE_GENLIST, GENLIST_FUN_EQ]
 \\ simp [PAD_RIGHT, MAP_GENLIST, REVERSE_GENLIST] \\ rw [fixwidth_def, zero_extend_def, PAD_LEFT, GENLIST_FUN_EQ] \\
    drule_strip length_n2l_bound_lem \\ ‘LENGTH (n2l 2 a) = n’ by decide_tac \\ simp []
QED

Triviality fixwidth_sum_2pow: (* todo: rename to carry something *)
 ∀b a n. a < 2**n ∧ b < 2 ⇒ fixwidth n (n2v $ a + b * 2 ** n) = fixwidth n (n2v a)
Proof
 simp [lt2] \\ rpt strip_tac \\ simp [] \\ drule_strip fixwidth_sum_2pow_lem \\ simp [] \\ simp [fixwidth_def]
QED
                                                                                     
Triviality length_le4_lem:
 (∀l. LENGTH l = 1 ⇔ ∃e0. l = [e0]) ∧
 (∀l. LENGTH l = 2 ⇔ ∃e1 e0. l = [e1; e0]) ∧
 (∀l. LENGTH l = 3 ⇔ ∃e2 e1 e0. l = [e2; e1; e0]) ∧
 (∀l. LENGTH l = 4 ⇔ ∃e3 e2 e1 e0. l = [e3; e2; e1; e0])
Proof
 simp [LENGTH_EQ_NUM_compute, PULL_EXISTS]
QED

Triviality EVERY_cell_inp_run_bool_lt_cset_var:
 ∀inps v fext s tmpnum.
 EVERY (λinp. ∃b. cell_inp_run fext s inp = INR (CBool b)) inps ∧
 EVERY (λinp. cell_input_lt inp tmpnum) inps ⇒
 EVERY (λinp. ∃b. cell_inp_run fext (cset_var s (NetVar tmpnum) v) inp = INR (CBool b)) inps
Proof
 rw [EVERY_MEM] \\ rpt drule_first \\
 Cases_on ‘inp’ \\ fs [cell_inp_run_def, cell_input_lt_def, cget_var_cset_var] \\
 Cases_on ‘v'’ \\ fs [var_lt_def]
QED

Triviality EVERY_cell_input_lt_unchanged:
 ∀inps n fext s s'.
 EVERY (λinp. cell_input_lt inp n) inps ∧
 (∀inp. cell_input_lt inp n ⇒ cell_inp_run fext s' inp = cell_inp_run fext s inp) ⇒
 EVERY (λinp. cell_inp_run fext s' inp = cell_inp_run fext s inp) inps
Proof
 simp [EVERY_MEM]
QED

(* Separate out proof of "static properties" in adder case, "dynamic properties" depends on the input lists being
   of equal length... *)
Theorem blast_cell_add1_correct_static_part:
 ∀tmpnum tmpnum' cin l r out cout cells regs.
 blast_cell_add1 tmpnum cin l r = (tmpnum', out, cout, cells) ∧
 cell_input_lt cin tmpnum ∧
 cell_input_lt l tmpnum ∧
 cell_input_lt r tmpnum ⇒
 tmpnum ≤ tmpnum' ∧
 cell_input_ge out tmpnum ∧
 cell_input_lt out tmpnum' ∧
 cell_input_not_pseudo regs out ∧
 cell_input_lt cout tmpnum' ∧
 deterministic_netlist cells ∧
 (* added afterwards: *)
 (∀processed globalmax.
  blast_cell_input_ok l processed globalmax tmpnum ∧
  blast_cell_input_ok r processed globalmax tmpnum ⇒
  EVERY (λc. blast_cell_output_ok c processed globalmax tmpnum) cells)
Proof
 simp [Once blast_cell_add1_def, le4] \\ rpt strip_tac' \\ fs [length_le4_lem] \\ rveq \\ fs [] \\
 simp [EVERY_DEF, cell_input_ge_def, cell_input_lt_def, var_lt_def] \\
 simp [EVERY_EL, deterministic_netlist_def, deterministic_cell_def, indexedListsTheory.EL_MAP2i,
       cell_input_not_pseudo_def, blast_cell_output_ok_def, cell_output_def]
QED

Theorem blast_cell_addarray_correct_static_part:
 ∀regs inps1 inps2 tmpnum tmpnum' cin outs cout cells.
 blast_cell_addarray tmpnum cin inps1 inps2 = (tmpnum', outs, cout, cells) ∧
 cell_input_lt cin tmpnum ∧
 EVERY (\inp. cell_input_lt inp tmpnum) inps1 ∧
 EVERY (\inp. cell_input_lt inp tmpnum) inps2 ⇒
 tmpnum ≤ tmpnum' ∧
 EVERY (λinp. cell_input_ge inp tmpnum) outs ∧
 EVERY (λinp. cell_input_lt inp tmpnum') outs ∧
 EVERY (λc. cell_input_not_pseudo regs c) outs ∧
 deterministic_netlist cells ∧
 (* added afterwards: *)
 (∀processed globalmax.
  EVERY (λinp. blast_cell_input_ok inp processed globalmax tmpnum) inps1 ∧
  EVERY (λinp. blast_cell_input_ok inp processed globalmax tmpnum) inps2 ⇒
  EVERY (λc. blast_cell_output_ok c processed globalmax tmpnum) cells)
Proof
 gen_tac \\ Induct >- simp [blast_cell_addarray_def, deterministic_netlist_def] \\
 gen_tac \\ Cases >- simp [blast_cell_addarray_def, deterministic_netlist_def] \\
 rpt gen_tac \\ rename1 ‘blast_cell_addarray _ _ (l::ls) (r::rs)’ \\
 simp [blast_cell_addarray_def] \\ rpt strip_tac' \\ rpt (pairarg_tac \\ fs []) \\ rveq \\

 drule_strip blast_cell_add1_correct_static_part \\ first_x_assum (qspec_then ‘regs’ strip_assume_tac) \\
 imp_res_tac EVERY_cell_input_lt_le \\
 drule_last \\

 rw [deterministic_netlist_append]
 >- (match_mp_tac EVERY_cell_input_ge_le \\ asm_exists_tac \\ simp [])
 >- (match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp [])
 >- metis_tac [EVERY_blast_cell_output_ok_le, EVERY_blast_cell_input_ok_le, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem blast_cell_add1_correct:
 ∀l r l' r' tmpnum tmpnum' cin cin' cout out cells fext bs.
 blast_cell_add1 tmpnum cin l r = (tmpnum', out, cout, cells) ∧
 inps2n fext bs [l] = INR l' ∧
 inps2n fext bs [r] = INR r' ∧
 inps2n fext bs [cin] = INR cin' ∧
 cell_input_lt l tmpnum ∧
 cell_input_lt r tmpnum ∧
 cell_input_lt cin tmpnum ⇒
 tmpnum ≤ tmpnum' ∧
 cell_input_lt out tmpnum' ∧
 cell_input_lt cout tmpnum' ∧
 ∃bs' out' cout'. sum_foldM (cell_run fext) bs cells = INR bs' ∧
                  bs'.fbits = bs.fbits ∧
                  (∀var. var_lt var tmpnum ⇒ cget_var bs' var = cget_var bs var) ∧
                  inps2n fext bs' [out] = INR out' ∧
                  inps2n fext bs' [cout] = INR cout' ∧
                  out' + 2*cout' = l' + r' + cin'
Proof
 simp [blast_cell_add1_def, cell_input_lt_def, var_lt_def, sum_foldM_def] \\ rpt strip_tac' \\

 gvs [inps2n_sing_INR] \\

 simp [cell_run_def, sum_bind_def, cell2_run_def, cell1_run_def,
       cell_inp_run_cset_var, cell_input_lt_cell_inp_run_cset_var_plus] \\

 conj_tac >- rw [cget_var_cset_var, var_lt_def] \\ simp [v2n_sing] \\ rw []
QED

Triviality inps2n_cong:
 ∀inps fext s s' n tmpnum.
 EVERY (λinp. cell_input_lt inp tmpnum) inps ∧
 (∀inp fext. cell_input_lt inp tmpnum ⇒ cell_inp_run fext s' inp = cell_inp_run fext s inp) ∧
 inps2n fext s inps = INR n ⇒ inps2n fext s' inps = INR n
Proof
 rw [EVERY_EL, inps2n_def, sum_map_INR, sum_mapM_EL] \\ metis_tac []
QED
                  
Triviality inps2n_cong_REVERSE:
 ∀inps fext s s' n tmpnum.
 EVERY (λinp. cell_input_lt inp tmpnum) inps ∧
 (∀inp fext. cell_input_lt inp tmpnum ⇒ cell_inp_run fext s' inp = cell_inp_run fext s inp) ∧
 inps2n fext s (REVERSE inps) = INR n ⇒
 inps2n fext s' (REVERSE inps) = INR n
Proof
 metis_tac [EVERY_REVERSE, inps2n_cong]
QED

Theorem blast_cell_addarray_correct:
 ∀inps1 inps2 inps1' inps2' cin cin' tmpnum tmpnum' outs cout cells fext bs.
 blast_cell_addarray tmpnum cin inps1 inps2 = (tmpnum', outs, cout, cells) ∧
 inps2n fext bs (REVERSE inps1) = INR inps1' ∧
 inps2n fext bs (REVERSE inps2) = INR inps2' ∧
 inps2n fext bs [cin] = INR cin' ∧
 cell_input_lt cin tmpnum ∧
 EVERY (\inp. cell_input_lt inp tmpnum) inps1 ∧
 EVERY (\inp. cell_input_lt inp tmpnum) inps2 ∧
 LENGTH inps1 = LENGTH inps2 ⇒
 tmpnum ≤ tmpnum' ∧
 LENGTH outs = LENGTH inps1 ∧
 ∃bs' outs' cout'. sum_foldM (cell_run fext) bs cells = INR bs' ∧
                   bs'.fbits = bs.fbits ∧
                   (∀var. var_lt var tmpnum ⇒ cget_var bs' var = cget_var bs var) ∧
                   inps2n fext bs' (REVERSE outs) = INR outs' ∧
                   inps2n fext bs' [cout] = INR cout' ∧
                   outs' + 2**(LENGTH inps1)*cout' = inps1' + inps2' + cin'
Proof
 Induct
 >- (Cases \\ simp [blast_cell_addarray_def] \\ rpt strip_tac' \\ fs [inps2n_nil, sum_foldM_def]) \\
 gen_tac \\ Cases >- simp [] \\
 rpt gen_tac \\ rename1 ‘blast_cell_addarray _ _ (in1::inps1) (in2::inps2)’ \\ rpt strip_tac' \\
 fs [blast_cell_addarray_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\
 fs [inps2n_append] \\ rveq \\ 
 drule_strip blast_cell_add1_correct \\
 drule cell_inp_run_cong_lt \\ strip_tac \\
 qspec_then ‘inps1’ assume_tac inps2n_cong_REVERSE \\ drule_first \\
 qspec_then ‘inps2’ assume_tac inps2n_cong_REVERSE \\ drule_first \\
 imp_res_tac EVERY_cell_input_lt_le \\
 drule_last \\ simp [] \\ strip_tac \\

 simp [sum_foldM_append, sum_bind_def] \\
 simp [GSYM PULL_EXISTS] \\ conj_tac >- metis_tac [var_lt_le] \\

 drule cell_inp_run_cong_lt \\ strip_tac \\
 qspec_then ‘[out]’ assume_tac inps2n_cong \\ fs [] \\ drule_first \\ simp [] \\

 simp [arithmeticTheory.ADD1, arithmeticTheory.EXP_ADD]
QED

Theorem blast_cell_equal12_correct_static:
 blast_cell_equal12 tmpnum preveq lhs rhs = (tmpnum',cells,out) ∧
 LENGTH lhs ≤ 12 ∧ lhs ≠ [] ⇒
 tmpnum ≤ tmpnum' ∧
 cell_input_lt out tmpnum' ∧
 cell_input_ge out tmpnum ∧
 cell_input_not_pseudo regs out ∧
 deterministic_netlist cells ∧
 (* added afterwards: *)
 (∀processed globalmax.
  EVERY (λinp. blast_cell_input_ok inp processed globalmax tmpnum) lhs ∧
  EVERY (λinp. blast_cell_input_ok inp processed globalmax tmpnum) rhs ⇒
  EVERY (λc. blast_cell_output_ok c processed globalmax tmpnum) cells)
Proof
 rewrite_tac [le12] \\ rpt strip_tac' \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\
 fs [blast_cell_equal12_def] \\
 fs [Ntimes blast_cell_equal_luts_def 4, blast_cell_equal_lut_def, take_drop_TAKE_DROP] \\ rveq \\
 every_case_tac \\ fs [] \\ rveq \\
 simp [deterministic_netlist_def, deterministic_cell_def, cell_input_lt_def, var_lt_def, cell_input_ge_def,
       cell_input_not_pseudo_def, blast_cell_output_ok_def, cell_output_def]
QED

Theorem blast_cell_equalarray_correct_static:
 ∀lhs rhs tmpnum tmpnum' tmpnumbase cells out preveq regs.
 blast_cell_equalarray tmpnum preveq lhs rhs = (tmpnum', cells, out) ∧
 cell_input_lt preveq tmpnum ∧
 cell_input_ge preveq tmpnumbase ∧
 cell_input_not_pseudo regs preveq ∧
 tmpnumbase ≤ tmpnum ⇒
 tmpnum ≤ tmpnum' ∧
 cell_input_lt out tmpnum' ∧
 cell_input_ge out tmpnumbase ∧
 cell_input_not_pseudo regs out ∧
 deterministic_netlist cells ∧
 (* added afterwards: *)
 (∀processed globalmax.
  EVERY (λinp. blast_cell_input_ok inp processed globalmax tmpnum) lhs ∧
  EVERY (λinp. blast_cell_input_ok inp processed globalmax tmpnum) rhs ⇒
  EVERY (λc. blast_cell_output_ok c processed globalmax tmpnum) cells)
Proof
 gen_tac \\ completeInduct_on ‘LENGTH lhs’ \\ gen_tac \\ strip_tac \\ rpt gen_tac \\
 once_rewrite_tac [blast_cell_equalarray_def] \\
 IF_CASES_TAC >- (rw [deterministic_netlist_def, cell_input_lt_def, cell_input_ge_def] \\ simp []) \\
 simp [take_drop_TAKE_DROP] \\ rpt strip_tac' \\
 pairarg_tac \\ drule_strip blast_cell_equal12_correct_static \\ disch_then (qspec_then ‘regs’ mp_tac) \\
 impl_tac >- simp [LENGTH_TAKE_EQ] \\ strip_tac \\ fs [] \\
 every_case_tac >- (fs [] \\ rw []
                    >- (match_mp_tac cell_input_ge_le \\ asm_exists_tac \\ simp [])
                    >- (metis_tac [EVERY_TAKE])) \\

 pairarg_tac \\
 last_x_assum (qspec_then ‘LENGTH (DROP 12 lhs)’ mp_tac) \\
 impl_tac >- (Cases_on ‘lhs’ \\ fs [LENGTH_DROP]) \\
 disch_then (qspec_then ‘DROP 12 lhs’ mp_tac) \\ impl_tac >- simp [] \\ disch_then drule_strip \\
 fs [] \\ rw [deterministic_netlist_append]
 >- (match_mp_tac cell_input_ge_le \\ asm_exists_tac \\ simp [])
 >- metis_tac [EVERY_TAKE]
 >- (‘tmpnum ≤ tmpnum''’ by fs [] \\
     metis_tac [EVERY_DROP, EVERY_blast_cell_output_ok_le, EVERY_blast_cell_input_ok_le,
                arithmeticTheory.LESS_EQ_REFL])
QED

Triviality cell_inp_run_cleanup_lem:
 ∀inp n v0 v1 v2 v3 s fext.
 cell_input_lt inp n ⇒
 (cell_inp_run fext (cset_var s (NetVar n) v0) inp =
  cell_inp_run fext s inp) ∧
 (cell_inp_run fext (cset_var (cset_var s (NetVar n) v0) (NetVar (SUC n)) v1) inp =
  cell_inp_run fext s inp) ∧
 (cell_inp_run fext (cset_var (cset_var (cset_var s (NetVar n) v0) (NetVar (SUC n)) v1) (NetVar (SUC (SUC n))) v2) inp =
  cell_inp_run fext s inp) ∧
 (cell_inp_run fext (cset_var (cset_var (cset_var (cset_var s (NetVar n) v0) (NetVar (SUC n)) v1) (NetVar (SUC (SUC n))) v2) (NetVar (SUC (SUC (SUC n)))) v3) inp =
  cell_inp_run fext s inp)
Proof
 rpt strip_tac' \\
 DEP_REWRITE_TAC [cell_input_lt_cell_inp_run_cset_var] \\ rw [cell_input_lt_def] \\
 match_mp_tac cell_input_lt_le \\ asm_exists_tac \\ simp []
QED

Theorem cell_run_CellLut_eq2:
 ∀in1 in2 s in1' in2' fext out.
 cell_inp_run fext s in1 = INR (CBool in1') ∧
 cell_inp_run fext s in2 = INR (CBool in2') ⇒
 cell_run fext s (CellLUT out [in1; in2] [[F; F]; [T; T]]) = INR (cset_var s (NetVar out) (CBool (in1' = in2')))
Proof
 EVAL_TAC \\ simp [] \\ EVAL_TAC \\ simp [rtlstate_component_equality] \\ metis_tac []
QED

Theorem cell_run_CellLut_eq4:
 ∀in1 in2 in3 in4 s in1' in2' in3' in4' fext out.
 cell_inp_run fext s in1 = INR (CBool in1') ∧
 cell_inp_run fext s in2 = INR (CBool in2') ∧
 cell_inp_run fext s in3 = INR (CBool in3') ∧
 cell_inp_run fext s in4 = INR (CBool in4') ⇒
 cell_run fext s (CellLUT out [in1; in2; in3; in4] [[F; F; F; F]; [F; F; T; T]; [T; T; F; F]; [T; T; T; T]]) = INR (cset_var s (NetVar out) (CBool (in1' = in2' ∧ in3' = in4')))
Proof
 EVAL_TAC \\ simp [] \\ EVAL_TAC \\ simp [rtlstate_component_equality] \\ metis_tac []
QED

Theorem cell_run_CellLut_eq6:
 ∀in1 in2 in3 in4 in5 in6 s in1' in2' in3' in4' in5' in6' fext out.
 cell_inp_run fext s in1 = INR (CBool in1') ∧
 cell_inp_run fext s in2 = INR (CBool in2') ∧
 cell_inp_run fext s in3 = INR (CBool in3') ∧
 cell_inp_run fext s in4 = INR (CBool in4') ∧
 cell_inp_run fext s in5 = INR (CBool in5') ∧
 cell_inp_run fext s in6 = INR (CBool in6') ⇒
 cell_run fext s (CellLUT out [in1; in2; in3; in4; in5; in6] [[F;F;F;F;F;F]; [F;F;F;F;T;T]; [F;F;T;T;F;F]; [F;F;T;T;T;T]; [T;T;F;F;F;F]; [T;T;F;F;T;T]; [T;T;T;T;F;F]; [T;T;T;T;T;T]]) = INR (cset_var s (NetVar out) (CBool (in1' = in2' ∧ in3' = in4' ∧ in5' = in6')))
Proof
 EVAL_TAC \\ simp [] \\ EVAL_TAC \\ simp [rtlstate_component_equality] \\ metis_tac []
QED

Theorem cell_run_Carry4_eq:
 ∀cin in0 in1 in2 in3 cin' in0' in1' in2' in3' fext s out cout.
 cell_inp_run fext s cin = INR (CBool cin') ∧
 cell_inp_run fext s in0 = INR (CBool in0') ∧
 cell_inp_run fext s in1 = INR (CBool in1') ∧
 cell_inp_run fext s in2 = INR (CBool in2') ∧
 cell_inp_run fext s in3 = INR (CBool in3') ⇒
 ∃out'. cell_run fext s (Carry4 out cout cin (REPLICATE 4 (ConstInp (CBool F))) [in3; in2; in1; in0]) =
        INR (cset_var (cset_var s (NetVar cout) (CArray [in3' ∧ in2' ∧ in1' ∧ in0' ∧ cin';
                                                         in2' ∧ in1' ∧ in0' ∧ cin';
                                                         in1' ∧ in0' ∧ cin';
                                                         in0' ∧ cin'])) (NetVar out) out')
Proof
 rpt strip_tac \\ EVAL_TAC \\ simp [] \\ EVAL_TAC \\ simp [rtlstate_component_equality]
QED

fun cell_run_Carry4_tac (g as (asl,w)) = let
 val cell_run_tm = find_term is_cell_run w
in
 mp_tac (PART_MATCH' (lhs o snd o strip_exists o rand) cell_run_Carry4_eq cell_run_tm) g
end

fun cell_run_CellLut_tac (g as (asl,w)) = let
 val cell_run_tm = find_term is_cell_run w
 val vars = cell_run_tm |> rand |> rator |> rand |> listSyntax.dest_list |> fst
 val th = case (length vars) of 2 => cell_run_CellLut_eq2 | 4 => cell_run_CellLut_eq4 | _ => cell_run_CellLut_eq6
 val s = cell_run_tm |> rator |> rand
in
 assume_tac (SPECL (vars @ [s]) th) g
end

val blast_luts_tac = (cell_run_CellLut_tac \\ rfs [cell_inp_run_cleanup_lem] \\
                      drule_first \\ simp [sum_bind_def] \\ pop_assum kall_tac);

val blast_carry_tac = (simp [PAD_LEFT] \\ cell_run_Carry4_tac \\
                       simp [cell_inp_run_cset_var, cell_inp_run_ConstInp, cell_inp_run_cleanup_lem] \\
                       strip_tac \\ simp [] \\ pop_assum kall_tac);

Theorem blast_cell_equal12_correct:
 blast_cell_equal12 tmpnum preveq lhs rhs = (tmpnum', cells, out) ∧
 cell_input_lt preveq tmpnum ∧
 cell_inp_run fext bs preveq = INR (CBool preveq') ∧
 LENGTH lhs ≤ 12 ∧ lhs ≠ [] ∧
 LENGTH rhs = LENGTH lhs ∧
 LENGTH b = LENGTH lhs ∧
 LIST_REL (λinp1 inp2. cell_inp_run fext bs inp1 = INR (CBool inp2)) lhs b ∧
 EVERY (λinp. cell_input_lt inp tmpnum) lhs ∧
 LENGTH b' = LENGTH rhs ∧
 LIST_REL (λinp1 inp2. cell_inp_run fext bs inp1 = INR (CBool inp2)) rhs b' ∧
 EVERY (λinp. cell_input_lt inp tmpnum) rhs ⇒
 tmpnum ≤ tmpnum' ∧
 ∃bs'. sum_foldM (cell_run fext) bs cells = INR bs' ∧
       cell_inp_run fext bs' out =
       INR (CBool ((LIST_REL (λinp1 inp2. cell_inp_run fext bs inp1 = cell_inp_run fext bs inp2) lhs rhs) ∧ preveq')) ∧
       (∀inp. cell_input_lt inp tmpnum ⇒ cell_inp_run fext bs' inp = cell_inp_run fext bs inp)
Proof
 rewrite_tac [le12] \\ rpt strip_tac' \\ rfs [] \\ fs [LENGTH_EQ_NUM_compute] \\ rveq \\
 fs [blast_cell_equal12_def] \\
 fs [Ntimes blast_cell_equal_luts_def 4, blast_cell_equal_lut_def, take_drop_TAKE_DROP] \\ rveq \\

 TRY (CHANGED_TAC every_case_tac \\ fs [cell_inp_run_ConstInp] \\ rveq) \\
 simp [sum_foldM_def, flat_zip_def, sum_bind_INR] \\
 rpt blast_luts_tac \\
 TRY blast_carry_tac \\
 
 TRY (conj_tac >- (simp [cell_inp_run_cset_var] \\ EVAL_TAC \\ rewrite_tac [CONJ_ASSOC]) \\
      Cases \\ rw [cell_inp_run_def, cget_var_cset_var, cell_input_lt_def, var_lt_def])
QED

Triviality LENGTH_TAKE_less:
 ∀l n. LENGTH l ≤ n ⇒ LENGTH (TAKE n l) = LENGTH l
Proof
 simp [LENGTH_TAKE_EQ]
QED

Theorem blast_cell_equalarray_correct:
 ∀lhs rhs b b' tmpnum tmpnum' cells out preveq preveq' fext bs.
 blast_cell_equalarray tmpnum preveq lhs rhs = (tmpnum', cells, out) ∧
 cell_input_lt preveq tmpnum ∧
 cell_inp_run fext bs preveq = INR (CBool preveq') ∧
 LENGTH rhs = LENGTH lhs ∧
 LENGTH b = LENGTH lhs ∧
 LIST_REL (λinp1 inp2. cell_inp_run fext bs inp1 = INR (CBool inp2)) lhs b ∧
 EVERY (λinp. cell_input_lt inp tmpnum) lhs ∧
 LENGTH b' = LENGTH rhs ∧
 LIST_REL (λinp1 inp2. cell_inp_run fext bs inp1 = INR (CBool inp2)) rhs b' ∧
 EVERY (λinp. cell_input_lt inp tmpnum) rhs  ⇒
 tmpnum ≤ tmpnum' ∧
 ∃bs'. sum_foldM (cell_run fext) bs cells = INR bs' ∧
       cell_inp_run fext bs' out =
       INR (CBool ((∀i. i < LENGTH lhs ⇒ cell_inp_run fext bs (EL i lhs) = cell_inp_run fext bs (EL i rhs)) ∧ preveq')) ∧
       (∀inp. cell_input_lt inp tmpnum ⇒ cell_inp_run fext bs' inp = cell_inp_run fext bs inp)
Proof
 gen_tac \\ completeInduct_on ‘LENGTH lhs’ \\ simp [Once blast_cell_equalarray_def] \\
 rpt gen_tac \\ strip_tac \\ rpt gen_tac \\ IF_CASES_TAC >- (rw [sum_foldM_def, cell_inp_run_def] \\ simp []) \\
 simp [take_drop_TAKE_DROP] \\ rpt strip_tac' \\ pairarg_tac \\ drule_strip blast_cell_equal12_correct \\
 disch_then (qspecl_then [‘TAKE 12 b'’, ‘TAKE 12 b’] mp_tac) \\
 impl_tac >- simp [LENGTH_TAKE_EQ, rich_listTheory.EVERY2_TAKE, EVERY_TAKE] \\ strip_tac \\
 every_case_tac \\ fs [] >- (rveq \\ fs [DROP_EQ_NIL] \\ simp [LIST_REL_EL_EQN, LENGTH_TAKE_less, EL_TAKE]) \\
 pairarg_tac \\ first_x_assum (qspec_then ‘LENGTH (DROP 12 lhs)’ mp_tac) \\
 impl_tac >- (Cases_on ‘lhs’ \\ fs [LENGTH_DROP]) \\ disch_then (qspec_then ‘DROP 12 lhs’ mp_tac) \\
 impl_tac >- simp [] \\
 drule_strip blast_cell_equal12_correct_static \\ disch_then (qspec_then ‘regs’ mp_tac) \\
 impl_tac >- simp [LENGTH_TAKE_EQ] \\ strip_tac \\
 drule_strip blast_cell_equalarray_correct_static \\
 disch_then drule_strip \\ disch_then (qspecl_then [‘DROP 12 b’, ‘DROP 12 b'’] mp_tac) \\
 impl_tac >- (rw [] \\
              TRY (match_mp_tac rich_listTheory.EVERY2_DROP \\ irule EVERY2_MEM_MONO \\ asm_exists_any_tac \\
                   Cases \\ rw [MEM_ZIP] \\ fs [EVERY_EL]) \\
              TRY (match_mp_tac EVERY_DROP \\ match_mp_tac EVERY_cell_input_lt_le \\ asm_exists_tac \\ simp [])) \\
 strip_tac \\ fs [] \\ rveq \\ simp [sum_foldM_append, sum_bind_def] \\
 reverse conj_tac >- metis_tac [cell_input_lt_le] \\
 fs [DROP_EQ_NIL] \\ simp [LIST_REL_EL_EQN, LENGTH_TAKE_EQ, EL_DROP, EL_TAKE] \\ eq_tac
 >- (strip_tac \\ simp [] \\ rpt strip_tac \\ Cases_on ‘i < 12’ >- simp [] \\
     rpt (first_x_assum (qspec_then ‘i - 12’ mp_tac)) \\ simp [] \\ rpt strip_tac \\
     fs [EVERY_EL] \\ metis_tac [cell_input_lt_le])
 >- (strip_tac \\ simp [] \\ rpt strip_tac \\ first_x_assum (qspec_then ‘i + 12’ mp_tac) \\ simp [] \\
     fs [EVERY_EL] \\ metis_tac [cell_input_lt_le])
QED

Theorem cell2_run_bad_types:
 (∀v bs. cell2_run CAnd (CArray bs) v = INL TypeError) ∧
 (∀v bs. cell2_run CAnd v (CArray bs) = INL TypeError) ∧
 (∀v bs. cell2_run COr (CArray bs) v = INL TypeError) ∧
 (∀v bs. cell2_run COr v (CArray bs) = INL TypeError) ∧
 (∀v b. cell2_run CAdd (CBool b) v = INL TypeError) ∧
 (∀v b. cell2_run CAdd v (CBool b) = INL TypeError)
Proof
 rpt conj_tac \\ Cases \\ simp [cell2_run_def]
QED

(*Theorem inp_marked_NetVar_inv_cell_inp_run:
 ∀inp s out max v fext.
 inp_marked_NetVar_inv out max (GoodInp inp) ∧ out < max ⇒
 cell_inp_run fext (cset_var s (NetVar out) v) inp = cell_inp_run fext s inp
Proof
 Cases \\ simp [cell_inp_run_def] \\ rename1 ‘VarInp var idx’ \\ Cases_on ‘var’ \\
 simp [cget_var_cset_var, inp_marked_NetVar_inv_def]
QED*)

Theorem blast_cell_input_ok_cell_inp_run_cset_var:
 ∀inp s out v fext processed max tmpnum.
 blast_cell_input_ok inp processed max tmpnum ∧ processed ≤ out ∧ out < max ⇒
 cell_inp_run fext (cset_var s (NetVar out) v) inp = cell_inp_run fext s inp
Proof
 Cases \\ fs [cell_inp_run_def] \\ rename1 ‘VarInp var idx’ \\ Cases_on ‘var’ \\
 fs [cget_var_cset_var, blast_cell_input_ok_def]
QED

Theorem blast_rel_cset_var_cset_var_bool:
 ∀fext si max s bs out b regs processed tmpnum.
 blast_rel fext si max s bs ∧
 blasterstate_ok regs si processed max tmpnum ∧
 processed ≤ out ∧ out < max ⇒
 blast_rel fext si max (cset_var s (NetVar out) (CBool b)) (cset_var bs (NetVar out) (CBool b))
Proof
 simp [blast_rel_def, blasterstate_ok_def, cget_var_cset_var] \\ rpt strip_tac \\ rw [] \\ rpt TOP_CASE_TAC
 >- simp [blast_rel_bool_def, cget_var_cset_var]
 >- (rpt drule_first \\ gs [blast_rel_bool_def, cget_var_cset_var] \\ TOP_CASE_TAC \\
     rpt drule_first \\ fs [blast_cell_input_marked_ok_def] \\
     drule_strip blast_cell_input_ok_cell_inp_run_cset_var \\ simp [])
 >- (rpt drule_first \\ gs [blast_rel_array_def, cget_var_cset_var] \\ rpt strip_tac \\ TOP_CASE_TAC \\
     rpt drule_first \\ gs [EVERY_EL] \\ rpt drule_first \\ gs [blast_cell_input_marked_ok_def] \\
     drule_strip blast_cell_input_ok_cell_inp_run_cset_var \\ simp [])
QED

Theorem blast_rel_blast_reg_rel_fext_array:
 ∀var fext si tmpnum s bs b out.
 blast_rel fext si tmpnum s bs ∧
 blast_reg_rel_fext fext si s bs ∧
 cget_var s var = INR (CArray b) ∧
 var_lt var out ∧
 out ≤ tmpnum ⇒
 ∃minps. lookup var_cmp var si = SOME (MArrayInp minps) ∧ LENGTH minps = LENGTH b ∧
         ∀i. i < LENGTH minps ⇒
             case EL i minps of
               GoodInp inp => cell_inp_run fext bs inp = INR (CBool (EL i b))
             | BadInp _ _ => T
Proof
 Cases \\ rpt strip_tac'
 >- (fs [blast_reg_rel_fext_def, blast_rel_array_def] \\ first_x_assum (qspecl_then [‘s’, ‘n’] mp_tac) \\ simp [])
 \\ fs [blast_rel_def, var_lt_def] \\ first_x_assum (qspec_then ‘n’ mp_tac) \\ simp [blast_rel_array_def]
QED

Theorem cells_run_gol_mux:
 ∀out inpc inpt inpf tmpnum fext s vc vt vf.
 cell_inp_run fext s inpc = INR (CBool vc) ∧
 cell_inp_run fext s inpt = INR (CBool vt) ∧
 cell_inp_run fext s inpf = INR (CBool vf) ∧
 cell_input_lt inpc tmpnum ∧
 cell_input_lt inpt tmpnum ∧
 cell_input_lt inpf tmpnum ⇒
 sum_foldM (cell_run fext) s (gol_mux tmpnum inpc inpt inpf) = 
 INR $ cset_var (cset_var (cset_var (cset_var s
        (NetVar tmpnum) (CBool (vc ∧ vt)))
        (NetVar (tmpnum + 1)) (CBool (¬vc)))
        (NetVar (tmpnum + 2)) (CBool (¬vc ∧ vf)))
        (NetVar (tmpnum + 3)) (CBool (if vc then vt else vf))
Proof
 rw [gol_mux_def, sum_foldM_def,
     cell_input_lt_cell_inp_run_cset_var_plus, cell_inp_run_cset_var,
     cell_run_def, cell1_run_def, cell2_run_def, sum_bind_def]
QED

Theorem blast_rel_insert_bool:
 ∀fext si globalmax tmpnum s bs bs' var inp regs out b.
 blast_rel fext si globalmax s bs ∧
 blasterstate_ok regs si out globalmax tmpnum ∧
 cell_inp_run fext bs' inp = INR (CBool b) ∧
 (∀var. var_lt var tmpnum ⇒ cget_var bs' var = cget_var bs var) ∧
 bs'.fbits = bs.fbits ⇒
 blast_rel fext (insert var_cmp var (MBoolInp (GoodInp inp)) si) globalmax (cset_var s var (CBool b)) bs'
Proof
 rw [blast_rel_def, cget_var_cset_var] \\ rw []
 >- fs [blasterstate_ok_def, blast_rel_bool_def, lookup_insert_var_cmp] \\
 drule_first \\ every_case_tac
 >- (fs [blasterstate_ok_def, blast_rel_bool_def, lookup_insert_var_cmp] \\ every_case_tac
     >- (first_x_assum (qspec_then ‘NetVar n’ mp_tac) \\ simp [var_lt_def]) \\
     rpt drule_first \\ fs [blast_cell_input_marked_ok_def] \\
     drule_strip blast_cell_input_ok_cell_input_lt \\
     drule_strip cell_inp_run_lt_cget_var_cong \\ simp [])
 >- (gs [blasterstate_ok_def, blast_rel_array_def, lookup_insert_var_cmp] \\ rpt strip_tac \\
     rpt drule_first \\ every_case_tac \\ gs [EVERY_EL] \\ rpt drule_first \\
     gs [blast_cell_input_marked_ok_def] \\
     drule_strip blast_cell_input_ok_cell_input_lt \\
     drule_strip cell_inp_run_lt_cget_var_cong \\ simp [])
QED

(* TODO
Theorem blast_rel_insert_array:
 ∀fext si globalmax tmpnum s bs bs' var inps vs regs out finp.
 blast_rel fext si globalmax s bs ∧
 blasterstate_ok regs si out globalmax tmpnum ∧
 (∀i. i < LENGTH inps ⇒ cell_inp_run fext bs' (finp i tmpnum) = INR (CBool (EL i vs))) ∧
 (∀var. var_lt var tmpnum ⇒ cget_var bs' var = cget_var bs var) ∧
 LENGTH vs = LENGTH inps ∧
 bs'.fbits = bs.fbits ⇒
 blast_rel fext (insert var_cmp (NetVar out) (MArrayInp (GENLIST (λi. GoodInp (finp i tmpnum)) (LENGTH vs))) si) globalmax (cset_var s var (CArray vs)) bs'
Proof
 rw [blast_rel_def, blasterstate_ok_def, cget_var_cset_var] \\
 IF_CASES_TAC
 >- (simp [blast_rel_array_def, lookup_insert_var_cmp] \\ rw [] \\ simp [cell_inp_run

 drule_last \\ rpt TOP_CASE_TAC
  >- (fs [blast_rel_bool_def, lookup_insert_var_cmp]
      >- (first_assum (qspec_then `VarInp (NetVar n) NoIndexing` mp_tac) \\ 
          impl_tac >- simp [cell_input_lt_def, var_lt_def] \\ strip_tac \\
          fs [cell_inp_run_def])
      >- (TOP_CASE_TAC \\ drule_last \\ fs [blast_cell_input_marked_ok_def] \\
          drule_strip blast_cell_input_ok_cell_input_lt \\
          drule_first \\ fs [])) \\

  fs [blast_rel_array_def, lookup_insert_var_cmp, EVERY_EL] \\
  rpt strip_tac \\ TOP_CASE_TAC \\ gs [] \\ drule_first \\ gs [] \\
  drule_last \\ disch_then (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\
  simp [blast_cell_input_marked_ok_def] \\ strip_tac \\
  drule_strip blast_cell_input_ok_cell_input_lt \\
  drule_first \\ fs []
QED*)

Theorem blast_cell_correct:
 !cell blast_s blast_s' nl globalmax.
 blast_cell blast_s cell = INR (blast_s', nl) /\

 deterministic_cell cell /\
 cell_ok (HD (cell_output cell)) (LAST (cell_output cell) + 1) cell /\
 cell_covered_by_extenv blast_s.extenv cell /\

 (* from si_NetVar_inv: *)
 (*(∀out. MEM out (cell_output cell) ⇒ si_cell_out_inv out globalmax blast_s.si) ∧*)
 
 blasterstate_ok regs blast_s.si (HD (cell_output cell)) globalmax blast_s.tmpnum ∧
 LAST (cell_output cell) < globalmax ==>
 blast_s'.extenv = blast_s.extenv /\
 blast_s.tmpnum ≤ blast_s'.tmpnum /\
 blasterstate_ok regs blast_s'.si (LAST (cell_output cell) + 1) globalmax blast_s'.tmpnum /\
 deterministic_netlist nl ∧
 EVERY (λc. blast_cell_output_ok c (HD (cell_output cell)) globalmax blast_s.tmpnum) nl ∧

 (* LAST makes sense here since the outputs are ordered *)
 (*(si_cell_out_inv (LAST (cell_output cell) + 1) globalmax blast_s'.si) ∧*)

 (!reg i. lookup var_cmp (RegVar reg i) blast_s'.si = lookup var_cmp (RegVar reg i) blast_s.si) /\
 (*(!n. ~MEM n (cell_output cell) ==> lookup var_cmp (NetVar n) blast_s'.si = lookup var_cmp (NetVar n) blast_s.si) /\*)

 (!fext s s' bs.
  cell_run fext s cell = INR s' /\ rtltype_extenv_n blast_s.extenv fext /\ 
  blast_rel fext blast_s.si globalmax s bs /\ blast_reg_rel_fext fext blast_s.si s bs ==>
  ?bs'. sum_foldM (cell_run fext) bs nl = INR bs' /\
        blast_rel fext blast_s'.si globalmax s' bs'
        (* probably need this as well now: blast_reg_rel_fext fext blast_s'.si s' bs'*))
Proof
 Cases \\ rewrite_tac [deterministic_cell_def, cell_ok_def, cell_covered_by_extenv_def]

 >- (* Cell1 *)
 (rename1 `Cell1 t out in1` \\ Cases_on `t` \\
 simp [blast_cell_def, blast_cell_bitwise_def, sum_bind_INR, cell_output_def, cell_output_ok_def] \\ rpt strip_tac' \\
 FULL_CASE_TAC

 >- (gvs [deterministic_netlist_def, deterministic_cell_def,
          cell_run_def, sum_foldM_def, sum_bind_INR] \\
     rpt strip_tac
     >- (match_mp_tac blasterstate_ok_le \\ asm_exists_tac \\ simp [])
     >- simp [blast_cell_output_ok_def, cell_output_def] \\
     drule_strip blast_cell_inp_run_correct_bool \\ impl_tac >- simp [] \\ strip_tac \\
     gvs [cell1_run_def] \\ match_mp_tac blast_rel_cset_var_cset_var_bool \\ rpt asm_exists_tac \\ simp []) \\

 gvs [blaster_new_names_def] \\ rpt conj_tac \\ rpt strip_tac
 >- (match_mp_tac blasterstate_ok_insert_cell1 \\ rpt asm_exists_tac \\ fs [cell_output_ok_def])
 >- simp [deterministic_netlist_def, EVERY_EL, deterministic_cell_def]
 >- simp [EVERY_MAPi, EVERYi_EL, blast_cell_output_ok_def, cell_output_def]
 >- fs [blasterstate_ok_def, lookup_insert_var_cmp, cell_output_def] \\

 fs [cell_run_def, sum_bind_INR, cell_output_ok_def, cell_output_def] \\
 drule_strip blast_cell_inp_run_correct_array \\ impl_tac >- simp [] \\ strip_tac \\
 fs [cell1_run_def] \\ rveq \\
 drule_strip blast_cell_input_cell_input_lt_array \\
 drule_strip cell1_bitwise_correct \\
 fs [blast_rel_def, cget_var_cset_var] \\ rpt strip_tac \\
 IF_CASES_TAC >- fs [blast_rel_array_def, blasterstate_ok_def, lookup_insert_var_cmp, cell_inp_run_def, EL_MAP] \\

 fs [blasterstate_ok_def] \\ drule_first \\ rpt TOP_CASE_TAC

 >- (fs [blast_rel_bool_def]
     >- (simp [lookup_insert_var_cmp] \\ first_x_assum (qspec_then ‘VarInp (NetVar n) NoIndexing’ mp_tac) \\
         simp [cell_inp_run_def, cell_input_lt_def, var_lt_def])
     >- (simp [lookup_insert_var_cmp] \\ TOP_CASE_TAC \\ fs [] \\ rpt drule_first \\
         fs [blast_cell_input_marked_ok_def] \\
         drule_strip blast_cell_input_ok_cell_input_lt \\ simp[]))
 \\ fs [blast_rel_array_def, lookup_insert_var_cmp] \\ rpt strip_tac \\ TOP_CASE_TAC \\
    first_x_assum (qspec_then ‘i’ mp_tac) \\ simp [] \\ rpt drule_first \\ fs [EVERY_EL] \\
    first_x_assum (qspec_then ‘i’ mp_tac) \\ simp [blast_cell_input_marked_ok_def] \\
    strip_tac \\ drule_strip blast_cell_input_ok_cell_input_lt \\ simp [])

 >- (* Cell2 *)
 (rename1 `Cell2 t out in1 in2` \\ Cases_on `t`

 THEN2 (* CAnd and COr *) (
 simp [blast_cell_def, sum_bind_INR, blast_cell_bitwise_def] \\ rpt strip_tac' \\
 every_case_tac
 >- (* bool, bool *)
 (gvs [deterministic_netlist_def, deterministic_cell_def,
       cell_output_ok_def, blast_cell_output_ok_def, cell_output_def] \\
  conj_tac >- (match_mp_tac blasterstate_ok_le \\ asm_exists_tac \\ simp []) \\
  simp [sum_foldM_def, cell_run_def, sum_bind_INR] \\ rpt strip_tac' \\
  qspec_then ‘in1’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\ impl_tac >- simp [] \\ strip_tac \\
  qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\ impl_tac >- simp [] \\ strip_tac \\
  fs [cell2_run_def] \\ 
  drule_strip blast_rel_cset_var_cset_var_bool \\ simp [])

 \\ (* non bool *)
 gvs [deterministic_netlist_def, deterministic_cell_def, cell_output_ok_def] \\
 (conj_tac >- (match_mp_tac blasterstate_ok_le \\ asm_exists_tac \\ simp [])) \\
 simp [sum_foldM_def, cell_run_def, sum_bind_INR] \\ rpt strip_tac' \\
 drule_strip blast_cell_inp_run_correct_array \\ (impl_tac >- simp []) \\ strip_tac \\
 fs [cell2_run_bad_types])

 >- (* Equal *)
 (simp [blast_cell_def, blast_cell_equal_def, sum_bind_INR, cell_output_def, cell_output_ok_def] \\ rpt strip_tac' \\
  every_case_tac \\ gvs []
 >- (* bool, bool *)
 (simp [deterministic_netlist_def, deterministic_cell_def,
        blast_cell_output_ok_def, cell_output_def,
        sum_foldM_def, cell_run_def, sum_bind_INR] \\
  conj_tac >- (match_mp_tac blasterstate_ok_le \\ asm_exists_tac \\ simp []) \\
  rpt strip_tac' \\
  qspec_then ‘in1’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
  qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
  simp [] \\ rpt strip_tac \\
  fs [cell2_run_def] \\
  drule_strip blast_rel_cset_var_cset_var_bool \\ simp [])

 THEN2 (* bool, array and array, bool*)
 (rw [sum_foldM_def, cell_run_def, sum_bind_INR, deterministic_netlist_def]
  >- (match_mp_tac blasterstate_ok_le \\ asm_exists_tac \\ simp []) \\
  drule_strip blast_cell_inp_run_correct_bool \\ drule_strip blast_cell_inp_run_correct_array \\
  simp [] \\ rpt strip_tac \\ fs [cell2_run_def])

 >- (* array, array *)
 (pairarg_tac \\ gvs [] \\

  qspec_then ‘in1’ assume_tac blast_cell_input_cell_input_marked_ok \\ drule_first \\
  impl_tac >- fs [blasterstate_ok_def] \\ strip_tac \\
  qspec_then ‘in2’ assume_tac blast_cell_input_cell_input_marked_ok \\ drule_first \\
  impl_tac >- fs [blasterstate_ok_def] \\ strip_tac \\
  
  fs [] \\
  drule_strip blast_cell_equalarray_correct_static \\
  disch_then (qspecl_then [‘blast_s.tmpnum’, ‘regs’] mp_tac) \\
  impl_tac >- simp [cell_input_lt_def, cell_input_ge_def, cell_input_not_pseudo_def] \\ strip_tac \\
  drule_first \\

  simp [] \\ rpt conj_tac
  >- (match_mp_tac blasterstate_ok_insert \\ asm_exists_tac \\
      fs [cell_output_ok_def, blast_cell_input_marked_ok_def, blast_cell_input_ok_alt,
          cell_input_marked_not_pseudo_def] \\
      rpt TOP_CASE_TAC \\ fs [cell_input_lt_def, var_lt_def, cell_input_ge_def, blasterstate_ok_def])
  >- fs [blasterstate_ok_def, lookup_insert_var_cmp] \\

 simp [cell_run_def, sum_bind_INR] \\ rpt strip_tac \\
 qspec_then ‘in1’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
 qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
 fs [cell_output_ok_def] \\ rpt strip_tac \\ rveq \\

 fs [cell2_run_def, sum_bind_INR, sum_check_INR] \\ rveq \\

 (* a little hack so we don't have to touch the proof: *)
 imp_res_tac EVERY_blast_cell_input_ok_cell_input_lt \\

 drule_strip blast_cell_equalarray_correct \\ simp [cell_input_lt_def, cell_inp_run_def] \\
 disch_then (qspecl_then [‘b'’, ‘b’, ‘fext’, ‘bs’] mp_tac) \\ impl_tac >- simp [LIST_REL_EL_EQN] \\ strip_tac \\
 fs [blast_rel_def, cset_var_fbits, cget_var_cset_var] \\
 conj_tac >- (drule_strip run_cells_deterministic_netlist \\ simp []) \\
 rpt strip_tac \\ drule_first \\ rw []
 >- (fs [blast_rel_bool_def, blasterstate_ok_def, lookup_insert_var_cmp] \\
     reverse eq_tac >- metis_tac [] \\
     strip_tac \\ rewrite_tac [GSYM LIST_REL_eq, LIST_REL_EL_EQN] \\ rw [])
 \\ rpt TOP_CASE_TAC
 >- (fs [blast_rel_bool_def, blasterstate_ok_def, lookup_insert_var_cmp]
     >- (first_x_assum (qspec_then ‘VarInp (NetVar n) NoIndexing’ mp_tac) \\
         simp [cell_input_lt_def, var_lt_def, cell_inp_run_def])
     >- (TOP_CASE_TAC \\ drule_last \\ first_x_assum (qspec_then ‘c’ mp_tac) \\
         impl_tac >- (fs [blast_cell_input_marked_ok_def] \\
                      match_mp_tac blast_cell_input_ok_cell_input_lt \\ asm_exists_tac) \\ fs []))
 >- (fs [blast_rel_array_def, blasterstate_ok_def, lookup_insert_var_cmp] \\
     drule_last \\ rpt strip_tac \\ TOP_CASE_TAC \\ gs [EVERY_EL] \\ ntac 2 drule_first \\
     gs [blast_cell_input_marked_ok_def] \\ drule_strip blast_cell_input_ok_cell_input_lt \\
     drule_first \\ simp [])))

 >- (* CAdd case *)
 (simp [blast_cell_def, blast_cell_add_def, CaseEq"inp_trans", sum_bind_INR, cell_output_def] \\
  rpt strip_tac' \\ rveq \\

 TRY (rw [sum_foldM_def, cell_run_def, sum_bind_INR, deterministic_netlist_def]
      >- (match_mp_tac blasterstate_ok_le \\ asm_exists_tac \\ simp []) \\
      drule_strip blast_cell_inp_run_correct_bool \\ impl_tac >- simp [] \\ strip_tac \\
      fs [cell2_run_bad_types] \\ NO_TAC) \\

 pairarg_tac \\ gvs [] \\

 qspec_then ‘in1’ assume_tac blast_cell_input_cell_input_marked_ok \\ drule_first \\
 impl_tac >- fs [blasterstate_ok_def] \\ disch_then (assume_tac o SIMP_RULE (srw_ss()) []) \\
 drule_strip EVERY_blast_cell_input_ok_cell_input_lt \\
  
 qspec_then ‘in2’ assume_tac blast_cell_input_cell_input_marked_ok \\ drule_first \\
 impl_tac >- fs [blasterstate_ok_def] \\ disch_then (assume_tac o SIMP_RULE (srw_ss()) []) \\
 drule_strip EVERY_blast_cell_input_ok_cell_input_lt \\

 drule_strip blast_cell_addarray_correct_static_part \\
 rewrite_tac [cell_input_lt_def, EVERY_REVERSE] \\
 disch_then drule_strip \\ pop_assum (qspec_then ‘regs’ strip_assume_tac) \\

 rw []
 >- (match_mp_tac blasterstate_ok_insert \\ asm_exists_tac \\
     rw [EVERY_MAP, blast_cell_input_marked_ok_def, cell_input_marked_not_pseudo_def] \\
     fs [EVERY_MEM] \\ rpt strip_tac \\ rpt drule_first \\
     rw [blast_cell_input_ok_alt] \\ rpt TOP_CASE_TAC \\
     fs [cell_input_lt_def, var_lt_def, cell_input_ge_def, blasterstate_ok_def])
 >- fs [blasterstate_ok_def, lookup_insert_var_cmp] \\

 rpt strip_tac' \\ fs [cell_run_def, sum_bind_INR] \\
 qspec_then ‘in1’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
 qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
 rpt (impl_tac >- simp [] \\ strip_tac) \\ rveq \\

 fs [cell2_run_def, sum_bind_INR, sum_check_INR] \\
 drule_strip inps2n_v2n_lem \\ qspec_then ‘inps2’ assume_tac inps2n_v2n_lem \\ drule_first \\
 qspecl_then [‘fext’, ‘bs’] assume_tac inps2n_F \\ gs [] \\

 drule_strip blast_cell_addarray_correct \\
 rewrite_tac [REVERSE_REVERSE, EVERY_REVERSE, cell_input_lt_def] \\
 disch_then drule_strip \\ simp [] \\

 fs [blast_rel_def, blasterstate_ok_def, cset_var_fbits, cget_var_cset_var] \\
 rpt strip_tac \\ simp [] \\ rpt strip_tac \\ IF_CASES_TAC

 >- (rw [lookup_insert_var_cmp, blast_rel_array_def, EL_MAP] \\
    qspec_then ‘REVERSE outs’ assume_tac el_inps2n_lem \\ drule_first \\ disch_then (qspec_then ‘i’ mp_tac) \\
    simp [] \\ strip_tac \\
    drule_strip inps2n_lt \\ qspec_then ‘REVERSE outs’ assume_tac inps2n_lt \\ drule_first \\ fs [] \\
    drule_strip fixwidth_sum_2pow \\ rfs [])

 \\ fs [] \\ drule_first \\ rpt TOP_CASE_TAC
 >- (fs [blast_rel_bool_def, lookup_insert_var_cmp]
     >- (first_x_assum (qspec_then ‘NetVar n’ mp_tac) \\ simp [var_lt_def])
     \\ TOP_CASE_TAC \\ drule_last \\ fs [blast_cell_input_marked_ok_def] \\
        drule_strip blast_cell_input_ok_cell_input_lt \\
        metis_tac [cell_inp_run_cong_lt])

 >- (fs [blast_rel_array_def, lookup_insert_var_cmp] \\
     rpt strip_tac \\ first_x_assum (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
     drule_last \\ fs [EVERY_EL] \\
     first_x_assum (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
     TOP_CASE_TAC \\
     gs [blast_cell_input_marked_ok_def] \\
     drule_strip blast_cell_input_ok_cell_input_lt \\
     drule_strip cell_inp_run_lt_cget_var_cong \\ simp [])))

 >- (* CellMux *)
 (rename1 ‘CellMux out in1 in2 in3’ \\
  rpt gen_tac \\ simp [blast_cell_def, sum_bind_INR, cell_output_def] \\
  strip_tac \\ reverse (fs [CaseEq"inp_trans"])
  >- (rveq \\ conj_tac >- (match_mp_tac blasterstate_ok_le \\ asm_exists_tac \\ simp []) \\
      simp [deterministic_netlist_def, cell_run_def, sum_bind_INR] \\ rpt strip_tac' \\
      drule_strip blast_cell_inp_run_correct_array \\ fs [cell_output_ok_def] \\ strip_tac \\ fs [cellMux_run_def]) \\
  
  gvs [blaster_new_names_def]

  >- (* array, array *)
  (rpt conj_tac
   >- (match_mp_tac blasterstate_ok_insert \\ asm_exists_tac \\
       fs [blasterstate_ok_def, EVERY_GENLIST,
           blast_cell_input_marked_ok_def, blast_cell_input_ok_def,
           cell_input_marked_not_pseudo_def, cell_input_not_pseudo_def])
   THEN3 (simp [deterministic_netlist_def, blast_cell_output_ok_def, cell_output_def,
                gol_mux_array_def, lt3,
                EVERY_FLAT, EVERY_EL, indexedListsTheory.EL_MAP2i] \\
          rw [] \\ fs [deterministic_cell_def, cell_output_def])
   >- fs [blasterstate_ok_def, lookup_insert_var_cmp, cell_output_def] \\

  simp [sum_foldM_def, cell_run_def, sum_bind_INR] \\ rpt strip_tac' \\

  qspec_then ‘in1’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
  qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
  qspec_then ‘in3’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
  simp [] \\ rpt strip_tac \\ fs [cellMux_run_def, sum_bind_INR, sum_check_INR] \\ rveq \\

  drule_strip blast_cell_input_cell_input_lt_bool \\ impl_tac >- fs [blasterstate_ok_def] \\ strip_tac \\
  qspec_then ‘in2’ assume_tac blast_cell_input_cell_input_lt_array \\ drule_first \\
  qspec_then ‘in3’ assume_tac blast_cell_input_cell_input_lt_array \\ drule_first \\

  simp [cell1_run_def] \\
  qmatch_goalsub_abbrev_tac ‘gol_mux_array _ _ not_inp1 _ _’ \\
  qmatch_goalsub_abbrev_tac ‘sum_foldM _ bs' _’ \\
  drule_strip Abbrev_cset_var_tmpvar_lem \\ strip_tac \\
  drule_strip cell_inp_run_lt_cget_var_cong \\
  qspec_then ‘inps1’ assume_tac EVERY_cell_inp_run_lt_cget_var_cong \\ drule_first \\ 
  qspec_then ‘inps2’ assume_tac EVERY_cell_inp_run_lt_cget_var_cong \\ drule_first \\
  simp [] \\ rpt strip_tac \\

  imp_res_tac cell_input_lt_SUC \\
  imp_res_tac EVERY_cell_input_lt_SUC \\
  qspecl_then [‘inps1’, ‘inps2’, ‘inp1’, ‘not_inp1’, ‘bs'’] assume_tac blast_cellMux_correct \\ drule_first \\
  gs [] \\ disch_then drule_strip \\
  unabbrev_all_tac \\ impl_tac >- simp [cell_inp_run_cset_var, cell_input_lt_def, var_lt_def] \\ strip_tac \\
  fs [arithmeticTheory.ADD1] \\

  fs [blast_rel_def, blasterstate_ok_def, cset_var_fbits, cget_var_cset_var] \\ rpt strip_tac \\
  IF_CASES_TAC >- (fs [blast_rel_bool_def, blast_rel_array_def, lookup_insert_var_cmp] \\ rw []) \\

  drule_last \\ rpt TOP_CASE_TAC
  >- (fs [blast_rel_bool_def, lookup_insert_var_cmp]
      >- (first_assum (qspec_then `VarInp (NetVar n) NoIndexing` mp_tac) \\ 
          impl_tac >- simp [cell_input_lt_def, var_lt_def] \\ strip_tac \\
          fs [cell_inp_run_def, cget_var_cset_var])
      >- (TOP_CASE_TAC \\ drule_last \\ fs [blast_cell_input_marked_ok_def] \\
          drule_strip blast_cell_input_ok_cell_input_lt \\
          drule_strip cell_input_lt_SUC \\ fs [arithmeticTheory.ADD1] \\
          rpt drule_first \\ fs [cell_input_lt_cell_inp_run_cset_var])) \\

  fs [blast_rel_array_def, lookup_insert_var_cmp, EVERY_EL] \\
  rpt strip_tac \\ TOP_CASE_TAC \\ gs [] \\ drule_first \\ gs [] \\
  drule_last \\ disch_then (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\
  simp [blast_cell_input_marked_ok_def] \\ strip_tac \\
  drule_strip blast_cell_input_ok_cell_input_lt \\
  drule_strip cell_input_lt_SUC \\ fs [arithmeticTheory.ADD1] \\
  drule_first \\ fs [cell_input_lt_cell_inp_run_cset_var]) \\

  (* bool, bool *)
  TRY (
  rename1 ‘blast_cell_input blast_s in2 = INR (BoolInp _)’ \\
  rename1 ‘blast_cell_input blast_s in3 = INR (BoolInp _)’ \\

  rpt conj_tac
  >- (match_mp_tac blasterstate_ok_insert \\ asm_exists_tac \\ simp [] \\ conj_tac
       >- (simp [blast_cell_input_marked_ok_def, blast_cell_input_ok_def] \\
           fs [blasterstate_ok_def, gol_mux_out_def, gol_mux_length_def])
       >- (simp [cell_input_marked_not_pseudo_def, cell_input_not_pseudo_def]))
   >- simp [gol_mux_def, deterministic_netlist_def, deterministic_cell_def]
   >- simp [gol_mux_def, blast_cell_output_ok_def, cell_output_def]
   >- fs [blasterstate_ok_def, lookup_insert_var_cmp] \\

   simp [cell_run_def, sum_bind_INR, sum_foldM_def] \\ rpt strip_tac' \\
  
   qspec_then ‘in1’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
   qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
   qspec_then ‘in3’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
   qspec_then ‘in1’ assume_tac blast_cell_input_cell_input_lt_bool \\ drule_first \\
   qspec_then ‘in2’ assume_tac blast_cell_input_cell_input_lt_bool \\ drule_first \\
   qspec_then ‘in3’ assume_tac blast_cell_input_cell_input_lt_bool \\ drule_first \\
   ‘out ≤ blast_s.tmpnum’ by fs [blasterstate_ok_def] \\
   simp [] \\ rpt strip_tac \\ rveq \\ fs [cellMux_run_def] \\ rveq \\
   qspecl_then [‘out’, ‘inp1’, ‘inp2’, ‘inp3’, ‘blast_s.tmpnum’] assume_tac cells_run_gol_mux \\ drule_first \\
   asm_exists_tac \\

   match_mp_tac blast_rel_insert_bool \\ rpt asm_exists_tac \\
   simp [cell_inp_run_def, cget_var_cset_var, gol_mux_out_def] \\
   Cases \\ simp [var_lt_def]) \\

  (rpt conj_tac
  >- (match_mp_tac blasterstate_ok_le \\ asm_exists_tac \\ simp [])
  >- simp [deterministic_netlist_def, deterministic_cell_def]) \\

  simp [cell_run_def, sum_bind_INR, sum_foldM_def] \\ rpt strip_tac' \\
  rev_drule_strip blast_cell_inp_run_correct_bool \\ (impl_tac >- simp []) \\ strip_tac

  >- (* array, bool *)
  (qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
   qspec_then ‘in3’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
   simp [] \\ rpt strip_tac \\ fs [cellMux_run_def])

  >- (* bool, array *)
  (qspec_then ‘in2’ assume_tac blast_cell_inp_run_correct_bool \\ drule_first \\
   qspec_then ‘in3’ assume_tac blast_cell_inp_run_correct_array \\ drule_first \\
   simp [] \\ rpt strip_tac \\ fs [cellMux_run_def]))

 \\ (* CellArrayWrite *)
 rename1 ‘CellArrayWrite out arr idx e’ \\
 simp [blast_cell_def, cell_output_ok_def, cell_output_def] \\
 rpt gen_tac \\ ntac 2 TOP_CASE_TAC \\ simp [sum_bind_INR] \\ ntac 2 TOP_CASE_TAC \\
 rpt strip_tac' \\ gvs [CaseEq"inp_trans"] \\

 rpt strip_tac
 >- (match_mp_tac blasterstate_ok_insert \\ asm_exists_tac \\ 
     drule_strip blast_cell_input_not_pseudo \\ 
     drule_strip blast_cell_input_cell_input_marked_ok \\ impl_tac >- fs [blasterstate_ok_def] \\
     fs [blasterstate_ok_def, cell_output_ok_def] \\ rpt drule_first \\ rw []
     >- (match_mp_tac EVERY_revLUPDATE_IMP \\ rw [blast_cell_input_marked_ok_def, cell_input_marked_not_pseudo_def]
         >- (match_mp_tac blast_cell_input_ok_le \\ asm_exists_tac \\ simp [])
         >- (match_mp_tac EVERY_blast_cell_input_marked_ok_le \\ asm_exists_tac \\ simp []))
     >- (match_mp_tac EVERY_revLUPDATE_IMP \\ simp [cell_input_marked_not_pseudo_def])
     >- (match_mp_tac EVERY_blast_cell_input_marked_ok_le \\ asm_exists_tac \\ simp []))
 >- simp [deterministic_netlist_def]
 >- fs [blasterstate_ok_def, lookup_insert_var_cmp] \\

 fs [sum_foldM_def, cell_run_def, sum_bind_INR] \\
 drule_strip blast_cell_inp_run_correct_bool \\ impl_tac >- simp [] \\ strip_tac \\
 Cases_on ‘in1’ \\ gvs [cellArrayWrite_run_def, cell_inp_run_def, cell_input_lt_def] \\
 drule_strip blast_rel_blast_reg_rel_fext_array \\ impl_tac >- simp [] \\ strip_tac \\

 fs [blast_rel_def, blasterstate_ok_def, cget_var_cset_var] \\
 rpt strip_tac \\ reverse IF_CASES_TAC >- fs [blast_rel_bool_def, blast_rel_array_def, lookup_insert_var_cmp] \\
 rw [revLUPDATE_def, EL_LUPDATE, blast_rel_array_def, lookup_insert_var_cmp] \\ rw []
QED

Triviality sorted_append_snd_imp:
 ∀l1 l2 R. SORTED R (l1 ⧺ l2) ⇒ SORTED R l2
Proof
 simp [sortingTheory.SORTED_APPEND_GEN]
QED

Triviality sorted_append_lt:
 ∀(xs : num list) ys.
 SORTED $< (xs ++ ys) ==> ∀x y. MEM x xs ∧ MEM y ys ⇒ x < y
Proof
 Induct \\ fs [sortingTheory.SORTED_EQ] \\ metis_tac []
QED

Triviality sorted_all_distinct_lt:
 !(l:num list). SORTED ($<) l ==> ALL_DISTINCT l
Proof
 rpt strip_tac' \\ irule sortingTheory.SORTED_ALL_DISTINCT \\ asm_exists_any_tac \\ 
 rw [relationTheory.irreflexive_def]
QED

Theorem MEM_cell_output:
 ∀c. ∃n. MEM n (cell_output c)
Proof
 Cases \\ simp [cell_output_def] \\ metis_tac []
QED

Theorem MEM_cell_neq_nil:
 ∀c. cell_output c ≠ []
Proof
 Cases \\ simp [cell_output_def]
QED

Theorem SORTED_MEM_HD:
 ∀l (n:num). SORTED $< l ∧ MEM n l ⇒ HD l ≤ n
Proof
 Cases \\ rw [sortingTheory.less_sorted_eq] \\ simp [] \\ drule_first \\ simp []
QED

(* ugly but does the job *)
(*Theorem si_cells_inv_glue:
 si_cell_out_inv (LAST (cell_output c) + 1) max si ∧
 SORTED $< (cell_output c ⧺ FLAT (MAP cell_output cs)) ⇒
 si_cells_inv si max cs
Proof
 simp [sortingTheory.SORTED_APPEND_GEN, si_cells_inv_def] \\ rpt strip_tac' \\
 gs [FLAT_EQ_NIL, EVERY_MAP, MEM_cell_neq_nil] \\
 irule si_cell_out_inv_le \\ asm_exists_any_tac \\
 drule_strip SORTED_MEM_HD \\ simp []
QED*)

(*Triviality cell_ok_LAST_max:
 ∀cell min max. cell_ok min max cell ⇒ LAST (cell_output cell) < max
Proof
 Cases \\ simp [cell_ok_def, cell_output_ok_def, cell_output_def]
QED*)

Triviality MEM_LAST_cell_output:
 ∀cell. MEM (LAST (cell_output cell)) (cell_output cell)
Proof
 Cases \\ simp [cell_output_def]
QED

Triviality lte1_lt:
 ∀(a:num) b. a + 1 ≤ b ⇔ a < b
Proof
 decide_tac
QED

(*Triviality cell_output_sorted_HD_LAST:
 ∀cell. SORTED $< (cell_output cell) ⇒ 
Proof
 Cases \\ simp [cell_output_def]
QED*)

Triviality netlist_ok_split:
 netlist_ok extenv min max (c::cs) ∧
 netlist_sorted (c::cs) ⇒
 LAST (cell_output c) + 1 ≤ max ∧
 min ≤ HD (cell_output c) ∧
 HD (cell_output c) ≤ LAST (cell_output c) ∧
 cell_covered_by_extenv extenv c ∧
 cell_ok (HD (cell_output c)) (LAST (cell_output c) + 1) c ∧
 netlist_ok extenv (LAST (cell_output c) + 1) max cs
Proof
 simp [netlist_ok_def, netlist_sorted_def, MATCH_MP sortingTheory.SORTED_APPEND arithmeticTheory.transitive_LESS] \\
 rpt strip_tac
 THEN3 (Cases_on ‘c’ \\ fs [cell_ok_def, cell_output_ok_def, cell_output_def])
 >- (fs [cell_ok_alt, cell_output_ok_def] \\ Cases_on ‘c’ \\ fs [cell_output_def]) \\

 fs [EVERY_MEM] \\ rpt strip_tac \\ drule_first \\ fs [cell_ok_alt] \\ rpt strip_tac \\ drule_first \\
 fs [cell_output_ok_def, lte1_lt] \\

 first_x_assum irule \\ simp [MEM_LAST_cell_output, MEM_FLAT, MEM_MAP] \\ metis_tac []
QED

(*Theorem si_cells_inv_max_le:
 ∀max max' globalmax si. si_cells_inv_max si globalmax max ∧ max ≤ max' ⇒ si_cells_inv_max si globalmax max'
Proof
 rw [si_cells_inv_max_def] \\ drule_strip si_cell_out_inv_le
QED

Theorem si_cells_inv_max_cell_ok:
 si_cells_inv_max si globalmax min ∧
 cell_ok min max cell ∧
 max ≤ globalmax ⇒
 ∀out. MEM out (cell_output cell) ⇒ si_cell_out_inv out globalmax si
Proof
 rw [si_cells_inv_max_def, si_cell_out_inv_def, cell_ok_alt, cell_output_ok_def]
 >- (drule_first \\ fs []) \\
 rpt drule_first \\
 TRY (irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ rpt strip_tac) \\
 match_mp_tac inp_marked_NetVar_inv_le \\ asm_exists_tac \\ simp []
QED*)

(*Theorem cell_input_marked_ok_GoodInp_cell_input_lt:
 cell_input_marked_ok (GoodInp inp) min globalmax tmpnum ⇒ cell_input_lt inp tmpnum
Proof
 simp [cell_input_marked_ok_alt] \\ every_case_tac \\ simp [cell_input_lt_def, var_lt_def]
QED*)

Theorem cells_run_cell_blast_cell_output_ok:
 sum_foldM (cell_run fext) s c = INR s' ∧
 EVERY (λc. blast_cell_output_ok c min globalmax tmpnum) c ∧
 blast_cell_input_marked_ok (GoodInp inp) min globalmax tmpnum ⇒
 cell_inp_run fext s' inp = cell_inp_run fext s inp
Proof
 rpt strip_tac \\ Cases_on ‘inp’ \\ simp [cell_inp_run_def] \\ Cases_on ‘v’
 >- (drule_strip cells_run_cget_var_RegVar \\ simp []) \\
 AP_THM_TAC \\ AP_TERM_TAC \\
 drule_strip cells_run_unchanged \\ disch_then irule \\ strip_tac \\
 gvs [EVERY_MEM, blast_cell_output_ok_def, MEM_FLAT, MEM_MAP] \\ drule_first \\
 gs [blast_cell_input_marked_ok_def, blast_cell_input_ok_def]
QED

Theorem blast_netlist_correct:
 !nl nl' blast_s blast_s' min regs globalmax max.
 blast_netlist blast_s nl = INR (blast_s', nl') /\

 netlist_ok blast_s.extenv min max nl /\
 min ≤ max ∧
 blasterstate_ok regs blast_s.si min globalmax blast_s.tmpnum ∧
 max ≤ globalmax ∧
 
 deterministic_netlist nl /\
 netlist_sorted nl

 (*si_cells_inv blast_s.si globalmax nl*)
 (*si_cells_inv_max blast_s.si globalmax min*) ⇒
 blast_s'.extenv = blast_s.extenv /\
 blast_s.tmpnum ≤ blast_s'.tmpnum ∧
 (!reg i. lookup var_cmp (RegVar reg i) blast_s'.si = lookup var_cmp (RegVar reg i) blast_s.si) /\

 deterministic_netlist nl' /\

 blasterstate_ok regs blast_s'.si max globalmax blast_s'.tmpnum /\
 (*si_cells_inv_max blast_s'.si globalmax max ∧*)
 (!s s' bs fext.
   sum_foldM (cell_run fext) s nl = INR s' /\ rtltype_extenv_n blast_s.extenv fext /\
   blast_rel fext blast_s.si globalmax s bs /\ blast_reg_rel_fext fext blast_s.si s bs ==>
   ?bs'. sum_foldM (cell_run fext) bs nl' = INR bs' /\ blast_rel fext blast_s'.si globalmax s' bs' ∧
         (* might as well provide this one: *) blast_reg_rel_fext fext blast_s'.si s' bs')
Proof
 Induct >- simp [blast_netlist_def, sum_foldM_def, blasterstate_ok_le, SF SFY_ss] \\
 simp [blast_netlist_def, sum_bind_INR] \\ rpt strip_tac' \\ rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\

 drule_strip netlist_ok_split \\
 fs [deterministic_netlist_def, netlist_sorted_def] \\
 drule_strip blast_cell_correct \\
 disch_then (qspecl_then [‘regs’, ‘globalmax’] mp_tac) \\
 impl_tac >- (simp [] \\ match_mp_tac blasterstate_ok_le \\ asm_exists_tac \\ simp []) \\ strip_tac \\

 drule_strip sorted_append_snd_imp \\
 drule_first \\ simp [] \\ disch_then drule_strip \\
 qpat_x_assum ‘SORTED _ _’ kall_tac \\
 fs [deterministic_netlist_def] \\
 
 simp [sum_foldM_INR] \\ rpt strip_tac' \\ drule_last \\ drule_first \\ impl_tac
 >- (fs [blast_reg_rel_fext_def] \\
     simp [PULL_FORALL] \\ rpt gen_tac \\ first_x_assum (qspecl_then [‘reg’, ‘i’] assume_tac) \\

     imp_res_tac cells_run_cget_var_RegVar \\ imp_res_tac cell_run_cget_var_RegVar \\
     imp_res_tac run_cells_deterministic_netlist \\ gs [deterministic_netlist_def] \\
     imp_res_tac run_cell_deterministic_cell \\

     rpt TOP_CASE_TAC \\ fs []

     >- (gs [blasterstate_ok_def] \\ rpt drule_first \\ drule_strip cells_run_cell_blast_cell_output_ok \\
         disch_then (qspec_then ‘c’ mp_tac) \\
         impl_tac >- (match_mp_tac blast_cell_input_marked_ok_le \\ asm_exists_tac \\ simp []) \\
         simp [])

     >- (gvs [blast_rel_array_def] \\ rpt strip_tac \\ drule_first \\ TOP_CASE_TAC \\
         fs [blasterstate_ok_def] \\ rpt drule_first \\
         drule_strip cells_run_cell_blast_cell_output_ok \\ strip_tac \\
         fs [EVERY_EL] \\
         first_x_assum (qspec_then ‘i’ mp_tac) \\ impl_tac >- simp [] \\ strip_tac \\
         first_x_assum (qspec_then ‘c’ mp_tac) \\
         impl_tac >- (match_mp_tac blast_cell_input_marked_ok_le \\ gs [] \\ asm_exists_tac \\ simp []) \\
         gs [])) \\

 simp [sum_foldM_append, sum_bind_def]
QED

(** blast regs **)

(* Needed to be able to run regs (both init and update) after having built the initial si... *)
(* TODO: add combs to name *)
Definition si_consistent_with_regs_def:
 si_consistent_with_regs si regs =
 ∀reg i. lookup var_cmp (RegVar reg i) si =
         OPTION_BIND (ALOOKUP regs (reg, i))
                     (λrdata. OPTION_MAP SND (build_combs_si_reg_entry ((reg, i), rdata)))
End

Theorem si_consistent_with_regs_cong:
 (∀reg i. lookup var_cmp (RegVar reg i) si' = lookup var_cmp (RegVar reg i) si) ⇒
 si_consistent_with_regs si' regs = si_consistent_with_regs si regs
Proof
 rpt strip_tac \\ simp [si_consistent_with_regs_def]
QED

(* Needed to be able to run regs (both init and update) after having built the initial si... *)
Definition ffs_si_consistent_with_regs_def:
 ffs_si_consistent_with_regs s si regs =
 ∀reg i. case ALOOKUP regs (reg, i) of
           NONE => lookup var_cmp (RegVar reg i) si = NONE
         | SOME rdata =>
            ∃res. build_ffs_si_reg_entry s ((reg, i), rdata) = INR res ∧
                  lookup var_cmp (RegVar reg i) si = OPTION_MAP SND res
End

(** blast regs + netlist **)

Theorem only_regs_blast_rel:
 ∀fext si tmpnum s bs.
 only_regs s ∧
 blast_reg_rel si s bs ⇒ (* just to get fbits equal *)
 blast_rel fext si tmpnum s bs
Proof
 simp [only_regs_def, blast_reg_rel_def, blast_rel_def]
QED

Theorem blast_regs_no_PseudoRegs:
 ∀regs regs' blast_s.
 blast_regs blast_s regs = INR regs' ⇒ FILTER (λ(var,data). data.reg_type = PseudoReg) regs' = []
Proof
 Induct \\ TRY PairCases \\ simp [blast_regs_def] \\ rpt gen_tac \\
 reverse TOP_CASE_TAC >- first_x_assum MATCH_ACCEPT_TAC \\
 every_case_tac \\ simp [sum_bind_INR] \\ strip_tac \\ every_case_tac \\ fs [sum_bind_INR] \\ drule_first \\
 gvs [FILTER_APPEND, FILTER_EQ_NIL, EVERY_GENLIST, EVERY_MAPi, EVERYi_T]
QED

Theorem ALL_DISTINCT_ALOOKUP_SOME_Reg_FILTER_PseudoReg:
 ∀regs reg i rdata.
 ALL_DISTINCT (MAP FST regs) ∧
 ALOOKUP regs (reg,i) = SOME rdata ∧
 rdata.reg_type = Reg ⇒
 ALOOKUP (FILTER (λ(var,data). data.reg_type = PseudoReg) regs) (reg,i) = NONE
Proof
 Induct \\ TRY PairCases \\ rw [] \\ fs [GSYM ALOOKUP_NONE] \\
 drule_strip ALL_DISTINCT_ALOOKUP_NONE_FILTER \\ simp []
QED

Theorem ALL_DISTINCT_ALOOKUP_SOME_PseudoReg_FILTER_PseudoReg:
 ∀regs reg i rdata.
 ALL_DISTINCT (MAP FST regs) ∧
 ALOOKUP regs (reg,i) = SOME rdata ∧
 rdata.reg_type = PseudoReg ⇒
 ALOOKUP (FILTER (λ(var,data). data.reg_type = PseudoReg) regs) (reg,i) = SOME rdata
Proof
 Induct \\ TRY PairCases \\ rw [] \\ fs [reg_type_not_PseudoReg]
QED

Theorem regs_run_PseudoReg:
 sum_foldM (reg_run fext s) s (FILTER (λ(var,data). data.reg_type = PseudoReg) regs) = INR s' ∧
 blast_regs_distinct regs ⇒
 s'.fbits = s.fbits ∧
 (∀n. cget_var s' (NetVar n) = cget_var s (NetVar n)) ∧
 (∀reg i. ALOOKUP regs (reg,i) = NONE ⇒ cget_var s' (RegVar reg i) = cget_var s (RegVar reg i)) ∧
 (∀reg i rdata. ALOOKUP regs (reg,i) = SOME rdata ∧ rdata.reg_type = Reg ⇒
                cget_var s' (RegVar reg i) = cget_var s (RegVar reg i)) ∧
 (∀reg i rdata. ALOOKUP regs (reg,i) = SOME rdata ∧ rdata.reg_type = PseudoReg ⇒
                case rdata.inp of
                  NONE => cget_var s' (RegVar reg i) = cget_var s (RegVar reg i)
                | SOME inp => ∃v. cell_inp_run fext s inp = INR v ∧
                                  rtltype_v v rdata.type ∧
                                  cget_var s' (RegVar reg i) = INR v)
Proof
 rewrite_tac [blast_regs_distinct_def, blast_reg_name_def] \\ rpt strip_tac' \\
 drule_strip regs_run_fbits_const \\ drule_strip regs_run_cget_var \\
 impl_tac >- simp [ALL_DISTINCT_MAP_FILTER] \\ rw [] \\ first_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac)
 >- (drule_strip ALL_DISTINCT_ALOOKUP_NONE_FILTER \\ simp [])
 >- (drule_strip ALL_DISTINCT_ALOOKUP_SOME_Reg_FILTER_PseudoReg \\ simp [])
 >- (drule_strip ALL_DISTINCT_ALOOKUP_SOME_PseudoReg_FILTER_PseudoReg \\ simp [] \\ TOP_CASE_TAC \\
     strip_tac \\ simp [])
QED

Theorem regs_run_PseudoReg_blast_rel:
 sum_foldM (reg_run fext s) s regs = INR s' ∧
 blast_rel fext si max s bs ⇒
 blast_rel fext si max s' bs
Proof
 simp [blast_rel_def] \\ rpt strip_tac' \\
 drule_strip regs_run_fbits_const \\ drule_strip regs_run_cget_var_NetVar \\ simp []
QED

Theorem regs_run_PseudoReg_blast_reg_rel:
 sum_foldM (reg_run fext s) s (FILTER (λ(var,data). data.reg_type = PseudoReg) regs) = INR s' ∧
 blast_regs_distinct regs ∧
 blast_reg_rel si s bs ∧
 blasterstate_ok regs si processed max tmpnum ∧
 si_consistent_with_regs si regs ∧
 (* do we really need this? *) cenv_consistent_with_regs regs s ∧
 (* little ugly to have this here? needed for idx = 0. *) regs_ok blast_s.extenv max' max'' regs ⇒
 blast_reg_rel si s' bs
Proof
 simp [regs_ok_def,
       blast_reg_rel_def, blasterstate_ok_def, si_consistent_with_regs_def, cenv_consistent_with_regs_def] \\
 rpt strip_tac' \\
 drule_strip regs_run_PseudoReg \\ simp [] \\ rpt gen_tac \\
 Cases_on ‘ALOOKUP regs (reg, i)’
 >- (drule_first \\ last_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\
     rpt TOP_CASE_TAC \\ rpt strip_tac \\ gvs []) \\
 Cases_on ‘x.reg_type’
 >- (drule_last \\ last_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\
     rpt TOP_CASE_TAC \\ rpt strip_tac \\ gvs []) \\
 drule_strip ALOOKUP_EVERY \\ fs [reg_ok_def] \\
 ntac 3 (last_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac)) \\ drule_first \\ strip_tac \\
 simp [build_combs_si_reg_entry_def] \\ strip_tac \\
 rpt (FULL_CASE_TAC \\ gvs []) \\
 drule_first \\ gvs [rtltype_v_cases, optionTheory.IS_SOME_EXISTS, GENLIST_FUN_EQ, mk_inp_marked_def]
QED

Theorem regs_run_PseudoReg_blast_reg_rel_fext:
 sum_foldM (reg_run fext s) s (FILTER (λ(var,data). data.reg_type = PseudoReg) regs) = INR s' ∧
 blast_regs_distinct regs ∧
 blast_reg_rel_fext fext si s bs ∧
 blasterstate_ok regs si processed max tmpnum ∧
 (* little ugly to have this here? needed for idx = 0. *) regs_ok blast_s.extenv max' max'' regs ∧
 si_consistent_with_regs si regs ∧
 (* do we really need this? *) cenv_consistent_with_regs regs s ⇒
 blast_reg_rel_fext fext si s' bs
Proof
 simp [regs_ok_def,
       blast_reg_rel_fext_def, blasterstate_ok_def, si_consistent_with_regs_def,
       cenv_consistent_with_regs_def] \\
 rpt strip_tac' \\
 drule_strip regs_run_PseudoReg \\ simp [] \\ rpt gen_tac \\
 Cases_on ‘ALOOKUP regs (reg, i)’
 >- (drule_first \\ last_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\
     rpt TOP_CASE_TAC \\ rpt strip_tac \\ gvs []) \\
 Cases_on ‘x.reg_type’
 >- (drule_last \\ last_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\ simp []) \\
 drule_strip ALOOKUP_EVERY \\ fs [reg_ok_def] \\
 ntac 3 (last_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac)) \\ drule_first \\ strip_tac \\
 simp [build_combs_si_reg_entry_def, blast_rel_array_def] \\
 rpt (FULL_CASE_TAC \\ gvs []) \\ drule_first \\
 gvs [rtltype_v_cases, optionTheory.IS_SOME_EXISTS] \\
 fs [GENLIST_FUN_EQ, mk_inp_marked_def, build_combs_si_reg_entry_def]
QED

Theorem cells_run_blast_reg_rel:
 ∀nl bnl s s' bs bs' si fext.
 sum_foldM (cell_run fext) s nl = INR s' ∧
 deterministic_netlist nl ∧
 sum_foldM (cell_run fext) bs bnl = INR bs' ∧
 deterministic_netlist bnl ∧
 blast_reg_rel si s bs ⇒
 blast_reg_rel si s' bs'
Proof
 rpt strip_tac \\
 imp_res_tac run_cells_deterministic_netlist \\
 imp_res_tac cells_run_cget_var_RegVar \\
 match_mp_tac blast_reg_rel_cong \\ asm_exists_tac \\ simp []
QED

Theorem invariant_FOLDR_insert_var_cmp:
 ∀l si. invariant var_cmp si ⇒ invariant var_cmp (FOLDR (λ(k,v) t. insert var_cmp k v t) si l)
Proof
 Induct \\ TRY PairCases \\ simp [insert_thm_var_cmp]
QED

Triviality lookup_FOLDR_insert:
 ∀es k si.
 invariant var_cmp si ⇒  
 lookup var_cmp k (FOLDR (λ(k,v) t. insert var_cmp k v t) si es) =
 case ALOOKUP es k of
   NONE => lookup var_cmp k si
 | SOME v => SOME v
Proof
 Induct \\ TRY PairCases \\ rw [] \\ metis_tac [lookup_insert_var_cmp, invariant_FOLDR_insert_var_cmp]
QED

Triviality build_ffs_si_reg_entires_NetVar_lem:
 ∀regs es s n. sum_option_flatMap (build_ffs_si_reg_entry s) regs = INR es ⇒ ALOOKUP es (NetVar n) = NONE 
Proof
 Induct \\ TRY PairCases \\ rw [sum_option_flatMap_def, sum_bind_INR] \\ every_case_tac
 >- (drule_first \\ simp []) \\
 fs [sum_bind_INR] \\ drule_first \\ gvs [build_ffs_si_reg_entry_def] \\
 every_case_tac \\ fs [sum_bind_INR] \\ every_case_tac \\ gvs [sum_bind_INR]
QED

Theorem invariant_ffs_si:
 ffs_si blast_s regs = INR si ∧
 invariant var_cmp blast_s.si ⇒
 invariant var_cmp si
Proof
 rw [ffs_si_def, sum_map_INR] \\ rw [invariant_FOLDR_insert_var_cmp]
QED

Theorem lookup_NetVar_ffs_si:
 ∀regs blast_s si n.
 ffs_si blast_s regs = INR si ∧
 invariant var_cmp blast_s.si ⇒
 lookup var_cmp (NetVar n) si = lookup var_cmp (NetVar n) blast_s.si
Proof
 rw [ffs_si_def, sum_map_INR] \\
 drule_strip build_ffs_si_reg_entires_NetVar_lem \\
 drule_strip lookup_FOLDR_insert \\ fs []
QED

Theorem ffs_si_blast_rel:
 ∀regs fext s bs blast_s si max regs' tmpnum' max'.
 ffs_si blast_s regs = INR si ∧
 blasterstate_ok regs' blast_s.si processed max' tmpnum' ∧ (* <-- we need just invariant *)
 blast_rel fext blast_s.si max s bs ⇒
 blast_rel fext si max s bs
Proof
 rewrite_tac [blasterstate_ok_def] \\
 rpt strip_tac \\ drule_strip lookup_NetVar_ffs_si \\ fs [blast_rel_def] \\ rpt strip_tac \\ drule_first \\
 rpt TOP_CASE_TAC \\ gs [blast_rel_bool_def, blast_rel_array_def]
QED

Triviality not_in_regs_not_in_ffs_entries:
 ∀regs reg i blast_s es.
 sum_option_flatMap (build_ffs_si_reg_entry blast_s) regs = INR es ∧ ¬MEM (reg, i) (MAP FST regs) ⇒
 ¬MEM (RegVar reg i) (MAP FST es)
Proof
 Induct \\ TRY PairCases \\ simp [sum_option_flatMap_def, sum_bind_INR] \\ rpt strip_tac' \\
 every_case_tac >- drule_first \\ gvs [sum_bind_INR, build_ffs_si_reg_entry_def] \\
 every_case_tac \\ gvs [sum_bind_INR] \\ drule_first \\ every_case_tac \\ gvs [sum_bind_INR]
QED

Triviality build_ffs_si_reg_entires_lem:
 ∀regs es s.
 sum_option_flatMap (build_ffs_si_reg_entry s) regs = INR es ∧
 blast_regs_distinct regs ⇒
 ∀reg i.
 case ALOOKUP regs (reg,i) of
   NONE => ALOOKUP es (RegVar reg i) = NONE
 | SOME rdata =>
     ∃res. build_ffs_si_reg_entry s ((reg,i),rdata) = INR res ∧
           ALOOKUP es (RegVar reg i) = OPTION_MAP SND res
Proof
 rewrite_tac [blast_regs_distinct_def, blast_reg_name_def] \\
 Induct \\ TRY PairCases \\ simp [sum_option_flatMap_def, sum_bind_INR] \\
 rpt strip_tac' \\ IF_CASES_TAC
 >- (gvs [] \\ every_case_tac
     >- (drule_first \\ gs [GSYM ALOOKUP_NONE] \\ first_x_assum (qspecl_then [‘h0’, ‘h1’] mp_tac) \\
         simp []) \\
     gvs [sum_bind_INR, build_ffs_si_reg_entry_def] \\
     every_case_tac \\ fs [sum_bind_INR] \\ every_case_tac \\ gvs [sum_bind_INR]) \\

 Cases_on ‘x''’ \\ gvs [sum_bind_INR, build_ffs_si_reg_entry_def] \\

 Cases_on ‘h2.reg_type’ \\ Cases_on ‘h2.type’ \\ Cases_on ‘h2.init’ \\ Cases_on ‘h2.inp’ \\
 gvs [sum_bind_INR] \\
 gvs [CaseEq"inp_trans_marked", sum_bind_INR] \\ IF_CASES_TAC \\ gs []
QED

Theorem ffs_si_ffs_si_consistent_with_regs:
 ∀s regs si regs' tmpnum' max'.
 ffs_si s regs = INR si ∧
 blasterstate_ok regs' s.si processed max' tmpnum' ∧ (* <-- we need just invariant *)
 blast_regs_distinct regs ∧
 si_consistent_with_regs s.si regs ⇒
 ffs_si_consistent_with_regs s si regs
Proof
 rw [ffs_si_def, blasterstate_ok_def, sum_map_INR,
     si_consistent_with_regs_def, ffs_si_consistent_with_regs_def] \\
 drule_strip build_ffs_si_reg_entires_lem \\
 drule_strip lookup_FOLDR_insert \\
 rpt (first_x_assum (qspecl_then [‘reg’, ‘i’] assume_tac)) \\ TOP_CASE_TAC \\ fs [] \\
 fs [build_ffs_si_reg_entry_def, build_combs_si_reg_entry_def] \\ every_case_tac \\ fs [sum_bind_INR] \\
 every_case_tac \\ gvs [sum_bind_INR]
QED

Theorem blast_cell_input_not_pseudo_in:
 ∀inp blast_s regs tinp.
 blast_cell_input blast_s inp = INR tinp ∧
 si_consistent_with_regs blast_s.si regs ⇒
 cell_input_not_pseudo regs inp ∨ tinp = ArrayInp []
Proof
 Cases \\ simp [cell_input_not_pseudo_def] \\ Cases_on ‘v’ \\ simp [cell_input_not_pseudo_def] \\
 rename1 ‘RegVar reg i’ \\ rpt gen_tac \\
 simp [blast_cell_input_def, si_consistent_with_regs_def] \\
 TOP_CASE_TAC >- (rpt strip_tac \\ first_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\
                  rw [build_combs_si_reg_entry_def] \\ fs [] \\
                  every_case_tac \\ fs [mk_inp_marked_def]) \\
 TOP_CASE_TAC >- (TOP_CASE_TAC \\ rpt strip_tac \\ first_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\
                  rw [build_combs_si_reg_entry_def] \\ every_case_tac \\ gvs []) \\
 TOP_CASE_TAC \\ rw [sum_map_INR] \\ first_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\
 rw [build_combs_si_reg_entry_def] \\ every_case_tac \\ gvs []
 >- (Cases_on ‘n’ \\ gvs [sum_mapM_INR, GENLIST_CONS, mk_inp_marked_def, inp_marked_get_def])
 >- (gs [inp_marked_get_INR, revEL_GENLIST, mk_inp_marked_def])
 >- (Cases_on ‘v'’ \\ simp [] \\ drule_strip sum_mapM_MEM \\ disch_then (qspec_then ‘h’ mp_tac) \\
     rw [inp_marked_get_INR] \\ strip_tac \\ drule_strip MEM_rev_slice \\ fs [MEM_GENLIST, mk_inp_marked_def])
QED

(* Maybe strange name for this thm? *)
Theorem ffs_si_blast_reg_rel_fext:
 ∀regs fext s bs blast_s si combs_max ffs_max processed.
 si_consistent_with_regs blast_s.si regs ∧
 ffs_si_consistent_with_regs blast_s si regs ∧
 cenv_consistent_with_regs regs s ∧
 blast_reg_rel_fext fext blast_s.si s bs ∧
 blast_rel fext blast_s.si ffs_max s bs ∧
 regs_ok blast_s.extenv combs_max ffs_max regs ∧
 combs_max ≤ ffs_max ∧
 blasterstate_ok regs blast_s.si processed ffs_max blast_s.tmpnum ∧
 rtltype_extenv_n blast_s.extenv fext ∧
 (∀reg i rdata.
  ALOOKUP regs (reg,i) = SOME rdata ∧ rdata.reg_type = PseudoReg ⇒
  OPTION_ALL (λinp. cell_input_not_pseudo regs inp ⇒
                    ∃v. cell_inp_run fext s inp = INR v ∧
                        rtltype_v v rdata.type ∧
                        cget_var s (RegVar reg i) = INR v) rdata.inp) ⇒
 blast_reg_rel_fext fext si s bs
Proof
 rw [ffs_si_consistent_with_regs_def, regs_ok_def] \\
 qpat_assum ‘si_consistent_with_regs _ _’ (strip_assume_tac o REWRITE_RULE [si_consistent_with_regs_def]) \\
 
 simp [blast_reg_rel_fext_def] \\ conj_tac >- fs [blast_reg_rel_fext_def] \\ rpt gen_tac \\
 rpt (first_x_assum (qspecl_then [‘reg’, ‘i’] assume_tac)) \\ TOP_CASE_TAC \\
 Cases_on ‘ALOOKUP regs (reg,i)’ >- (fs [cenv_consistent_with_regs_def] \\
                                     first_x_assum (qspecl_then [‘reg’, ‘i’] assume_tac) \\ gs []) \\
 drule_strip ALOOKUP_EVERY \\ gs [reg_ok_def] \\
 Cases_on ‘x.reg_type’
 (* Reg *)
 >- (fs [blast_reg_rel_fext_def] \\
     first_x_assum (qspecl_then [‘reg’, ‘i’] assume_tac) \\
     gvs [build_combs_si_reg_entry_def, build_ffs_si_reg_entry_def] \\
     every_case_tac \\ gvs [blast_rel_array_def, mk_inp_marked_def]) \\
 (* PseudoReg *)
 gvs [build_combs_si_reg_entry_def, build_ffs_si_reg_entry_def, sum_bind_INR] \\
 gs [optionTheory.IS_SOME_EXISTS, blast_pseudoreg_inp_def, sum_bind_INR] \\

 Cases_on ‘x.inp’
 >- (Cases_on ‘x.init’ \\ fs [cenv_consistent_with_regs_def, blast_reg_rel_fext_def] \\
     rpt (first_x_assum (qspecl_then [‘reg’, ‘0’] assume_tac)) \\
     gvs [] \\
     rename1 ‘ConstInp v’ \\ Cases_on ‘v’ \\
     gvs [blast_cell_input_def, sum_bind_def, cell_inp_run_def, blast_rel_array_def, EL_MAP]) \\

 fs [sum_bind_INR] \\
 reverse (drule_strip blast_cell_input_not_pseudo_in)
 >- (fs [] \\ every_case_tac \\ gvs [sum_bind_INR, sum_check_INR] \\
     fs [cenv_consistent_with_regs_def] \\
     first_x_assum (qspecl_then [‘reg’, ‘0’] mp_tac) \\ simp [rtltype_v_cases, blast_rel_array_def]) \\
 
 TOP_CASE_TAC \\ fs [rtltype_v_cases, blast_rel_array_def] \\ Cases_on ‘binp’ \\ gvs []
 >- (drule_strip blast_cell_inp_run_correct_bool) \\
 fs [sum_bind_INR] \\ drule_strip blast_cell_inp_run_correct_array \\ gvs [EL_MAP]
QED

Theorem blast_pseudoreg_inp_props:
 ∀inp blast_s regs max tinp processed tmpnum.
 blast_pseudoreg_inp blast_s inp = INR tinp ∧
 blasterstate_ok regs blast_s.si processed max tmpnum ∧
 cell_input_lt inp processed ∧ processed ≤ tmpnum (* <-- only needed for less-than bool case *) ⇒
 (case tinp of
    MBoolInp minp => cell_input_marked_not_pseudo regs minp
  | MArrayInp minps => EVERY (cell_input_marked_not_pseudo regs) minps) ∧
 (case tinp of
    MBoolInp minp => blast_cell_input_marked_ok minp processed max tmpnum
  | MArrayInp minps => EVERY (λminp. blast_cell_input_marked_ok minp processed max tmpnum) minps)
Proof
 simp [blast_pseudoreg_inp_def, sum_bind_INR] \\ rpt strip_tac' \\
 drule_strip blast_cell_input_cell_input_marked_ok \\
 drule_strip blast_cell_input_not_pseudo \\
 every_case_tac \\ simp [blast_cell_input_marked_ok_def, cell_input_marked_not_pseudo_def, EVERY_MAP, SF ETA_ss]
QED

Theorem ffs_si_consistent_with_regs_blasterstate_ok:
 ffs_si blast_s regs = INR si ∧
 ffs_si_consistent_with_regs blast_s si regs ∧
 si_consistent_with_regs blast_s.si regs ∧
 regs_ok blast_s'.extenv combs_max ffs_max regs ∧
 combs_max ≤ ffs_max ∧
 (*invariant var_cmp new_si ∧
 (∀n. lookup var_cmp (NetVar m) si = lookup var_cmp (NetVar m) blast_s.si) ∧*)
 blasterstate_ok regs blast_s.si combs_max ffs_max blast_s.tmpnum ⇒
 blasterstate_ok regs si combs_max ffs_max blast_s.tmpnum
Proof
 rewrite_tac [ffs_si_consistent_with_regs_def, si_consistent_with_regs_def, regs_ok_def] \\
 rpt strip_tac' \\ first_assum mp_tac \\ rewrite_tac [blasterstate_ok_def] \\ rw []
 >- drule_strip invariant_ffs_si \\

 drule_strip lookup_NetVar_ffs_si >- fs [] \\
 
 TRY (reverse (Cases_on ‘var’) >- (fs [] \\ rpt drule_first)) \\ rename1 ‘RegVar reg i’ \\
 rpt (first_x_assum (qspecl_then [‘reg’, ‘i’] assume_tac)) \\ FULL_CASE_TAC \\ gvs [] \\
 fs [build_ffs_si_reg_entry_def] >- (rpt (every_case_tac \\ gvs [sum_bind_INR])) \\

 (Cases_on ‘x.reg_type’ >- (fs [] \\ FULL_CASE_TAC \\
                            gvs [EVERY_GENLIST, regs_ok_def,
                                 blast_cell_input_marked_ok_def, blast_cell_input_ok_def,
                                 cell_input_marked_not_pseudo_def, cell_input_not_pseudo_def] \\
                            drule_strip ALOOKUP_EVERY \\ rpt strip_tac \\ drule_strip ALOOKUP_EVERY \\
                            gvs [reg_ok_def])) \\

 fs [sum_bind_INR, regs_ok_def] \\ drule_strip ALOOKUP_EVERY \\

 (Cases_on ‘x.inp’ >- (every_case_tac \\ fs [] \\
                       rename1 ‘ConstInp v’ \\ Cases_on ‘v’ \\
                       gvs [blast_pseudoreg_inp_def, blast_cell_input_def, sum_bind_def,
                            blast_cell_input_marked_ok_def, blast_cell_input_ok_def,
                            cell_input_marked_not_pseudo_def, cell_input_not_pseudo_def,
                            EVERY_MAP])) \\

 gs [sum_bind_INR, reg_ok_def, optionTheory.IS_SOME_EXISTS] \\
 drule_strip blast_pseudoreg_inp_props \\ (impl_tac >- simp [](* metis_tac [cell_input_lt_le]*)) \\
 every_case_tac \\ gvs [sum_bind_INR]
QED

Triviality cell_ok_cell_output_ok:
 ∀cell min max out. cell_ok min max cell ∧ MEM out (cell_output cell) ⇒ cell_output_ok min max out
Proof
 Cases \\ rw [cell_ok_def, cell_output_def]
QED

Theorem blast_netlist_blast_regs_correct_step:
 !combs_nl ffs_nl combs_nl' ffs_nl' fext s s' bs blast_s blast_s' blast_s'' new_si regs regs' min combs_max ffs_max.
 blast_netlist blast_s combs_nl = INR (blast_s', combs_nl') /\
 ffs_si blast_s' regs = INR new_si ∧
 blast_netlist (blast_s' with si := new_si) ffs_nl = INR (blast_s'', ffs_nl') ∧

 blast_regs blast_s'' regs = INR regs' /\

 netlist_step fext s combs_nl ffs_nl regs = INR s' /\

 blast_regs_distinct regs ∧
 cenv_consistent_with_regs regs s ∧
 si_consistent_with_regs blast_s.si regs ∧
 blast_reg_rel blast_s.si s bs /\

 deterministic_netlist combs_nl /\ deterministic_netlist ffs_nl /\
 netlist_ok blast_s.extenv min combs_max combs_nl /\ netlist_ok blast_s.extenv combs_max ffs_max ffs_nl /\
 min ≤ combs_max ∧
 combs_max ≤ ffs_max ∧
 netlist_sorted (combs_nl ++ ffs_nl) /\
 (*si_cells_inv blast_s.si ffs_max (*<--global max here!*) combs_nl /\ (*si_cells_inv blast_s.si ffs_max ffs_nl /\*)*)
 regs_ok blast_s.extenv combs_max ffs_max regs /\

 rtltype_extenv_n blast_s.extenv fext /\
 blasterstate_ok regs blast_s.si min ffs_max blast_s.tmpnum /\
 
 only_regs s ==>
 blast_s''.extenv = blast_s.extenv ∧
 (!reg i. lookup var_cmp (RegVar reg i) blast_s'.si = lookup var_cmp (RegVar reg i) blast_s.si) ∧
 (!reg i. lookup var_cmp (RegVar reg i) blast_s''.si = lookup var_cmp (RegVar reg i) new_si) ∧
 deterministic_netlist combs_nl' ∧ deterministic_netlist ffs_nl' ∧
 blasterstate_ok regs blast_s'.si ffs_max ffs_max blast_s'.tmpnum /\
 ?bs'. netlist_step fext bs combs_nl' ffs_nl' regs' = INR bs' ∧
       blast_rel fext blast_s''.si ffs_max s' bs' ∧
       blast_reg_rel blast_s.si s' bs' ∧
       blast_reg_rel_fext fext blast_s''.si s' bs'
Proof
 rpt strip_tac' \\
 qpat_x_assum ‘blast_netlist _ combs_nl = _’ assume_tac \\
 drule_strip blast_netlist_correct \\
 impl_tac >- fs [netlist_sorted_def, sortingTheory.SORTED_APPEND] \\ strip_tac \\

 qpat_x_assum ‘blast_netlist _ ffs_nl = _’ assume_tac \\
 drule_strip blast_netlist_correct \\ simp [] \\ disch_then drule_strip \\
 disch_then (qspecl_then [‘regs’, ‘ffs_max’] mp_tac) \\
 drule_strip ffs_si_ffs_si_consistent_with_regs \\
 impl_keep_tac >- metis_tac [si_consistent_with_regs_cong] \\ strip_tac \\
 impl_keep_tac >- (fs [netlist_sorted_def, sortingTheory.SORTED_APPEND] \\
                   drule_strip ffs_si_consistent_with_regs_blasterstate_ok
                   (*\\ drule_strip ffs_si_si_cells_inv \\ simp [] \\ disch_then drule_strip*)) \\ strip_tac \\

 fs [netlist_step_def, sum_bind_INR] \\
 conj_tac >- simp [blasterstate_ok_le, SF SFY_ss] \\
 drule_last \\
 drule_strip only_regs_blast_rel \\ first_x_assum (qspecl_then [‘fext’, ‘ffs_max’] assume_tac) \\
 drule_strip blast_reg_rel_blast_reg_rel_fext \\ first_x_assum (qspec_then ‘fext’ assume_tac) \\
 disch_then drule_strip \\

 drule_strip blast_regs_no_PseudoRegs \\
 simp [sum_foldM_def] \\

 drule_strip regs_run_PseudoReg_blast_rel \\
 qspecl_then [‘combs_nl’, ‘combs_nl'’] assume_tac cells_run_blast_reg_rel \\ drule_first \\
 qpat_x_assum ‘sum_foldM _ _ combs_nl = _’ assume_tac \\
 drule_strip cells_run_cenv_consistent_with_regs \\
 drule_strip regs_run_PseudoReg_blast_reg_rel \\
 drule_strip regs_run_PseudoReg_blast_reg_rel_fext \\
 (*impl_keep_tac >- metis_tac [si_consistent_with_regs_cong] \\ fs [] \\ strip_tac \\*)
  
 drule_strip ffs_si_blast_rel \\
 drule_strip regs_run_PseudoReg \\
 drule_first \\
 impl_tac >- (match_mp_tac ffs_si_blast_reg_rel_fext \\
              rpt asm_exists_any_tac \\ simp [] \\
              conj_tac >- metis_tac [regs_run_cenv_consistent_with_regs] \\

              rpt strip_tac \\ drule_first \\ FULL_CASE_TAC \\ fs [] \\ strip_tac \\
              rename1 ‘cell_inp_run _ _ inp = INR _’ \\ Cases_on ‘inp’ \\ fs [cell_inp_run_def] \\
              rename1 ‘VarInp var idx’ \\ Cases_on ‘var’
              >- (fs [sum_bind_INR, cell_input_not_pseudo_def] \\
                  rename1 ‘VarInp (RegVar reg' i') idx’ \\
                  Cases_on ‘ALOOKUP regs (reg', i')’ \\ fs []) \\
              simp []) \\ strip_tac \\

 simp [] \\
 qspecl_then [‘ffs_nl’, ‘ffs_nl'’] assume_tac cells_run_blast_reg_rel \\ drule_first
QED

Theorem si_consistent_with_regs_ffs_si_consistent_with_regs_lookup_Reg:
 si_consistent_with_regs blast_s.si regs ∧
 ffs_si_consistent_with_regs blast_s si' regs ∧
 ALOOKUP regs (reg, i) = SOME rdata ∧ rdata.reg_type = Reg ⇒
 lookup var_cmp (RegVar reg i) si' = lookup var_cmp (RegVar reg i) blast_s.si
Proof
 rw [si_consistent_with_regs_def, ffs_si_consistent_with_regs_def] \\
 rpt (first_x_assum (qspecl_then [‘reg’, ‘i’] assume_tac)) \\
 gs [build_ffs_si_reg_entry_def, build_combs_si_reg_entry_def] \\
 TOP_CASE_TAC \\ simp [GENLIST_FUN_EQ, mk_inp_marked_def]
QED

Triviality regs_run_no_inps:
 ∀j n.
 sum_foldM (reg_run fext snet) sreg
 (FILTER (λ(var,data). data.reg_type = Reg)
  (GENLIST (λi. ((reg,i+j), <|type := CBool_t; reg_type := Reg; init := init (i+j); inp := NONE|>))
           n)) = INR sreg
Proof
 Induct_on ‘n’ \\ simp [sum_foldM_def, GENLIST_CONS, reg_run_def, sum_bind_def, combinTheory.o_DEF] \\
 gen_tac \\ first_x_assum (qspec_then ‘j + 1’ mp_tac) \\ simp [arithmeticTheory.ADD1] \\
 ‘∀i. i + (j + 1) = j + (i + 1)’ by decide_tac \\ pop_assum (REWRITE_TAC o sing)
QED

Triviality blast_regs_correct_array_help:
 !reg fext init inps vs shift bsnet bsbase.
 LENGTH vs = LENGTH inps /\
 (!i. i < LENGTH inps ==> cell_inp_run fext bsnet (EL i inps) = INR (CBool (EL i vs))) ==>
 (* init does not matter here, but have it to match later: *)
 ?bs. sum_foldM (reg_run fext bsnet) bsbase
                (FILTER (λ(var,data). data.reg_type = Reg)
                        (MAPi (λi inp. ((reg,i+shift),
                                        <| type := CBool_t;
                                           reg_type := Reg;
                                           init := SOME (CBool (EL (i+shift) init));
                                           inp := SOME inp|>)) inps)) = INR bs /\
      (!var. cget_var bs var = case var of
               RegVar reg' i' => if reg' = reg /\ shift <= i' /\ i' < LENGTH inps + shift then
                                  INR (CBool (EL (i'-shift) vs))
                                 else
                                  cget_var bsbase var
             | _ => cget_var bsbase var) /\
      bs.fbits = bsbase.fbits
Proof
 (* Much of proof similar to init_run_blasted_array_help proof ... *)
 ntac 3 gen_tac \\ Induct >- (rw [sum_foldM_def] \\ TOP_CASE_TAC) \\ rpt strip_tac \\ Cases_on ‘vs’ \\ fs [] \\
 simp [sum_foldM_def, reg_run_def] \\
 first_assum (qspec_then ‘0’ (rewrite_tac o sing o SIMP_RULE (srw_ss()) [])) \\ simp [sum_bind_def, has_rtltype_v_def] \\
 qmatch_goalsub_abbrev_tac ‘sum_foldM _ bsbase' _’ \\
 drule_first \\ disch_then (qspecl_then [‘shift + 1’, ‘bsnet’, ‘bsbase'’] mp_tac) \\
 impl_tac >- (rpt strip_tac \\ first_x_assum (qspec_then ‘SUC i’ mp_tac) \\ simp []) \\ strip_tac \\
 unabbrev_all_tac \\ qexists_tac ‘bs’ \\ rpt conj_tac
 >- (qpat_x_assum ‘sum_foldM _ _ _ = _’ (assume_tac o GSYM) \\
     simp [combinTheory.o_DEF, arithmeticTheory.ADD1] \\ f_equals_tac \\ simp [FUN_EQ_THM])
 >- (rpt strip_tac \\ simp [] \\ TOP_CASE_TAC
     >- (simp [arithmeticTheory.ADD1] \\ Cases_on ‘n = shift’
         >- (rveq \\ simp [cget_var_cset_var])
         >- (simp [cget_var_cset_var] \\ IF_CASES_TAC \\ fs [] \\
             Cases_on ‘n - shift’ \\ fs [] \\ f_equals_tac \\ rw []))
     >- simp [cget_var_cset_var])
 \\ fs [cset_var_fbits]
QED

Triviality blast_regs_correct_Reg_lem:
 ∀regsall blast_s combs_max ffs_max regs regs' snet sreg bsnet bsreg s' si fext.
 blast_regs blast_s regs = INR regs' ∧
 (*blast_regs_distinct regs ∧*)
 regs_ok blast_s.extenv combs_max ffs_max regs ∧
 rtltype_extenv_n blast_s.extenv fext ∧
 sum_foldM (reg_run fext snet)
           sreg
           (FILTER (λ(var,data). data.reg_type = Reg) regs) = INR s' ∧
 
 blast_reg_rel_fext fext blast_s.si snet bsnet ∧
 blast_rel fext blast_s.si ffs_max snet bsnet ∧
 blast_reg_rel si sreg bsreg ∧

 blast_regs_distinct regsall ∧
 (∀r. MEM r regs ⇒ MEM r regsall) ∧
 
 cenv_consistent_with_regs regsall sreg ⇒
 ∃bs'. sum_foldM (reg_run fext bsnet)
                 bsreg
                 (FILTER (λ(var,data). data.reg_type = Reg) regs') = INR bs' ∧
       blast_reg_rel si s' bs'
Proof
 ntac 4 gen_tac \\ Induct \\ TRY PairCases \\
 fs [blast_regs_def, sum_foldM_INR, blast_regs_distinct_def, blast_reg_name_def, regs_ok_def] \\ rpt gen_tac \\
 reverse TOP_CASE_TAC >- (
  rw [] \\ drule_first \\ fs [GSYM ALOOKUP_NONE] \\
  disch_then irule \\ rw [] \\ 
  first_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\
  IF_CASES_TAC \\ fs []) \\
 
 TOP_CASE_TAC >- (
  TOP_CASE_TAC >- (
    rpt strip_tac \\ gvs [sum_bind_INR, sum_foldM_INR] \\ drule_first \\
    gs [reg_run_def] \\ disch_then irule \\ fs [GSYM ALOOKUP_NONE] \\
    metis_tac []) \\

  simp [sum_bind_INR] \\ rpt strip_tac \\
  every_case_tac \\ gvs [sum_bind_INR, sum_foldM_INR, reg_run_def, reg_ok_def] \\
  drule_strip blast_cell_inp_run_correct_bool \\ impl_tac >- simp [] \\ strip_tac \\
  simp [has_rtltype_v_correct, rtltype_v_cases] \\
  first_x_assum match_mp_tac \\ rpt asm_exists_tac \\

  fs [SF DNF_ss] \\
  drule_strip ALOOKUP_ALL_DISTINCT_MEM \\
  
  conj_tac >- (
    fs [blast_reg_rel_def, cget_var_cset_var] \\ rpt gen_tac \\
    IF_CASES_TAC >- (
      rw [] \\ fs [cenv_consistent_with_regs_def] \\
      rpt (first_x_assum (qspecl_then [‘h0’, ‘0’] mp_tac)) \\ rw [rtltype_v_cases] \\ fs []) \\
                   
    first_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\ rpt TOP_CASE_TAC \\ fs [] \\ metis_tac []) \\

  fs [cenv_consistent_with_regs_def] \\ rw [cget_var_cset_var] \\
  simp [rtltype_v_cases] \\ TOP_CASE_TAC) \\

 rpt TOP_CASE_TAC >- (
  rw [sum_bind_INR] \\ fs [sum_foldM_INR, FILTER_APPEND, sum_foldM_append] \\
  gvs [reg_run_def, sum_bind_def, Q.SPEC ‘0’ regs_run_no_inps |> SIMP_RULE (srw_ss()) []] \\
  first_x_assum match_mp_tac \\ rpt asm_exists_tac) \\

 simp [sum_bind_INR] \\ rpt strip_tac \\ every_case_tac \\ fs [sum_bind_INR, sum_check_INR] \\ rveq \\
 gs [sum_foldM_INR, sum_bind_INR, reg_run_def, FILTER_APPEND, sum_foldM_append] \\ rveq \\
 gvs [reg_ok_def] \\
 drule_strip blast_cell_inp_run_correct_array \\ impl_tac >- simp [] \\ strip_tac \\
 drule_strip blast_regs_correct_array_help \\
 first_x_assum (qspecl_then [‘h0’, ‘l’, ‘0’, ‘bsreg’] strip_assume_tac) \\ fs [] \\

 first_x_assum match_mp_tac \\ rpt asm_exists_tac \\
 fs [SF DNF_ss] \\ drule_strip ALOOKUP_ALL_DISTINCT_MEM \\
 conj_tac >- (
  fs [blast_reg_rel_def, cget_var_cset_var] \\ rpt gen_tac \\
  IF_CASES_TAC >- (
    rw [] \\ fs [cenv_consistent_with_regs_def] \\
    rpt (first_x_assum (qspecl_then [‘h0’, ‘0’] mp_tac)) \\
    rw [] \\ gs [rtltype_v_cases, GENLIST_FUN_EQ]) \\

  first_x_assum (qspecl_then [‘reg’, ‘i’] mp_tac) \\ rpt TOP_CASE_TAC \\ fs [] \\ metis_tac []) \\

 fs [cenv_consistent_with_regs_def] \\ rw [cget_var_cset_var] \\ fs [rtltype_v_cases]
QED

Theorem blast_regs_correct_Reg:
 ∀regs regs' si blast_s s s' bs fext combs_max ffs_max.
 blast_regs blast_s regs = INR regs' ∧
 blast_regs_distinct regs ∧
 regs_ok blast_s.extenv combs_max ffs_max regs ∧
 rtltype_extenv_n blast_s.extenv fext ∧
 sum_foldM (reg_run fext s)
           (s with env := FILTER (is_RegVar ∘ FST) s.env)
           (FILTER (λ(var,data). data.reg_type = Reg) regs) = INR s' ∧

 blast_rel fext blast_s.si ffs_max s bs ∧
 blast_reg_rel_fext fext blast_s.si s bs ∧
 blast_reg_rel si s bs ∧
                    
 cenv_consistent_with_regs regs s ⇒
 ∃bs'. sum_foldM (reg_run fext bs)
                 (bs with env := FILTER (is_RegVar ∘ FST) bs.env)
                 (FILTER (λ(var,data). data.reg_type = Reg) regs') = INR bs' ∧
       blast_reg_rel si s' bs'
Proof
 rpt strip_tac \\
 match_mp_tac blast_regs_correct_Reg_lem \\ rpt asm_exists_tac \\ qexists_tac ‘regs’ \\
 fs [blast_reg_rel_def, cget_var_def, ALOOKUP_FILTER_FST, is_RegVar_def, cenv_consistent_with_regs_def]
QED

Theorem blast_netlist_blast_regs_correct:
 !combs_nl ffs_nl n combs_nl' ffs_nl' fext s s' bs blast_s blast_s' blast_s'' new_si regs regs' min combs_max ffs_max.
 blast_netlist blast_s combs_nl = INR (blast_s', combs_nl') /\
 ffs_si blast_s' regs = INR new_si ∧
 blast_netlist (blast_s' with si := new_si) ffs_nl = INR (blast_s'', ffs_nl') ∧

 blast_regs blast_s'' regs = INR regs' /\

 netlist_run fext s combs_nl ffs_nl regs n = INR s' /\

 blast_regs_distinct regs ∧
 cenv_consistent_with_regs regs s ∧
 si_consistent_with_regs blast_s.si regs ∧
 blast_reg_rel blast_s.si s bs /\

 deterministic_netlist combs_nl /\ deterministic_netlist ffs_nl /\
 netlist_ok blast_s.extenv min combs_max combs_nl /\ netlist_ok blast_s.extenv combs_max ffs_max ffs_nl /\
 min ≤ combs_max ∧
 combs_max ≤ ffs_max ∧
 netlist_sorted (combs_nl ++ ffs_nl) /\
 (*si_cells_inv blast_s.si ffs_max combs_nl /\*)
 regs_ok blast_s.extenv combs_max ffs_max regs /\

 rtltype_extenv blast_s.extenv fext /\
 blasterstate_ok regs blast_s.si min ffs_max blast_s.tmpnum /\
 
 only_regs s ==>
 blast_s''.extenv = blast_s.extenv ∧
 (!reg i. lookup var_cmp (RegVar reg i) blast_s'.si = lookup var_cmp (RegVar reg i) blast_s.si) ∧
 (!reg i. lookup var_cmp (RegVar reg i) blast_s''.si = lookup var_cmp (RegVar reg i) new_si) ∧
 deterministic_netlist combs_nl' ∧ deterministic_netlist ffs_nl' ∧
 blasterstate_ok regs blast_s'.si ffs_max ffs_max blast_s'.tmpnum /\
 ?bs'. netlist_run fext bs combs_nl' ffs_nl' regs' n = INR bs' ∧
       blast_rel (fext n) blast_s''.si ffs_max s' bs' ∧
       blast_reg_rel blast_s.si s' bs' ∧
       blast_reg_rel_fext (fext n) blast_s''.si s' bs'
Proof
 ntac 2 gen_tac \\ Induct >- (
  simp [netlist_run_def] \\ rpt strip_tac' \\
  qspecl_then [‘combs_nl’, ‘ffs_nl’] assume_tac blast_netlist_blast_regs_correct_step \\ drule_first \\
  fs [rtltype_extenv_rtltype_extenv_n]) \\

 simp_tac bool_ss [netlist_run_def, sum_bind_INR] \\ rpt strip_tac' \\ drule_first \\ simp [] \\

 drule_strip ffs_si_ffs_si_consistent_with_regs \\
 impl_keep_tac >- metis_tac [si_consistent_with_regs_cong] \\ strip_tac \\

 drule_strip rtltype_extenv_rtltype_extenv_n \\ first_x_assum (qspec_then ‘n’ assume_tac) \\
 rev_drule_strip netlist_run_cenv_consistent_with_regs \\
 drule_strip blast_regs_correct_Reg \\ simp [] \\ disch_then drule_strip \\ simp [] \\

 rev_drule_strip regs_run_cenv_consistent_with_regs \\
 impl_tac >- fs [cenv_consistent_with_regs_def, cget_var_def, ALOOKUP_FILTER_FST, is_RegVar_def] \\ strip_tac \\
 rev_drule_strip regs_run_only_regs \\
 impl_tac >- simp [only_regs_def, cget_var_def, ALOOKUP_FILTER_FST, is_RegVar_def] \\ strip_tac \\

 qspecl_then [‘combs_nl’, ‘ffs_nl’] assume_tac blast_netlist_blast_regs_correct_step \\ drule_first \\
 impl_tac >- fs [rtltype_extenv_rtltype_extenv_n] \\ simp []
QED

(** blast_regs + init_run **)

(* TODO: Rename to reg_idx_ok or something like that? *)
Definition reg_init_ok_def:
 reg_init_ok ((reg,i),rdata) ⇔ i = 0 (*∧ OPTION_ALL (λv. rtltype_v v rdata.type) rdata.init*)
End

Theorem regs_ok_EVERY_reg_init_ok:
 ∀extenv combs_max ffs_max regs. regs_ok extenv combs_max ffs_max regs ⇒ EVERY reg_init_ok regs
Proof
 rw [regs_ok_def] \\ irule EVERY_MONOTONIC \\ asm_exists_any_tac \\ PairCases \\ rw [reg_ok_def, reg_init_ok_def]
QED

Definition blast_reg_init_rel_def:
 blast_reg_init_rel regs s bs <=>
  bs.fbits = s.fbits /\
  ∀reg. case cget_var s (RegVar reg 0) of
          INL e => T
        | INR (CBool b) => ∀rdata. ALOOKUP regs (reg, 0) = SOME rdata ∧ rdata.reg_type = Reg ⇒
                                   cget_var bs (RegVar reg 0) = INR (CBool b)
        | INR (CArray b) =>
           ∀rdata. ALOOKUP regs (reg, 0) = SOME rdata ∧ rdata.reg_type = Reg ⇒ 
                   ∀i. i < LENGTH b ⇒ cget_var bs (RegVar reg i) = INR (CBool (EL i b))
End

Theorem blast_reg_init_rel_cset_var_bool:
 blast_reg_init_rel si s bs ∧ rtltype_v v CBool_t ⇒
 blast_reg_init_rel si (cset_var s (RegVar reg 0) v) (cset_var bs (RegVar reg 0) v)
Proof
 rw [blast_reg_init_rel_def, rtltype_v_cases, cset_var_fbits] \\ rw [cget_var_cset_var]
QED

Theorem blast_reg_init_rel_blast_reg_rel:
 ∀regs si s bs.
 blast_reg_init_rel regs s bs ∧
 si_consistent_with_regs si regs ∧
 EVERY reg_init_ok regs ∧
 (∀reg i v. cget_var s (RegVar reg i) = INR v ⇒ ∃rdata. ALOOKUP regs (reg, i) = SOME rdata) ⇒
 cenv_consistent_with_regs regs s ⇒
 blast_reg_rel si s bs
Proof
 rw [blast_reg_init_rel_def, si_consistent_with_regs_def, cenv_consistent_with_regs_def, blast_reg_rel_def] \\
 TOP_CASE_TAC \\ drule_first \\ 
 rpt (first_x_assum (qspecl_then [‘reg’, ‘i’] assume_tac)) \\
 imp_res_tac ALOOKUP_EVERY \\ gs [reg_init_ok_def] \\
 first_x_assum (qspec_then ‘reg’ mp_tac) \\ rpt TOP_CASE_TAC \\ rw [] \\
 fs [build_combs_si_reg_entry_def, rtltype_v_cases] \\ every_case_tac \\
 gvs [GENLIST_FUN_EQ] \\ Cases_on ‘rdata.reg_type’ \\ fs [mk_inp_marked_def]
QED

Theorem blast_reg_rel_blast_reg_init_rel:
 ∀regs si s bs.
 blast_reg_rel si s bs ∧ si_consistent_with_regs si regs ∧ 
 cenv_consistent_with_regs regs s ⇒
 blast_reg_init_rel regs s bs
Proof
 rw [blast_reg_rel_def, si_consistent_with_regs_def, blast_reg_init_rel_def] \\
 rpt (first_x_assum (qspecl_then [‘reg’, ‘0’] mp_tac)) \\ every_case_tac \\ rw [] \\ imp_res_tac ALOOKUP_EVERY \\
 gs [build_combs_si_reg_entry_def] \\ every_case_tac \\
 gvs [rtltype_v_cases, mk_inp_marked_def, GENLIST_FUN_EQ_gen]
QED

Theorem init_run_blasted_array_help:
 !finp reg reg_type vs l bs shift.
 LENGTH l = LENGTH vs ==>
 ?bs'. init_run bs (MAPi (λi inp. ((reg, i+shift), <| type := CBool_t; reg_type := reg_type; init := SOME (CBool (EL i l)); inp := finp inp|>)) vs) = INR bs' /\
       (!var. cget_var bs' var = case var of
                RegVar reg' i' => if reg' = reg /\ shift <= i' /\ i' < LENGTH l + shift then
                                   INR (CBool (EL (i'-shift) l))
                                  else
                                   cget_var bs var
              | _ => cget_var bs var) /\
       bs'.fbits = bs.fbits
Proof
 ntac 3 gen_tac \\ Induct >- (rw [init_run_def] \\ TOP_CASE_TAC) \\ rpt strip_tac \\ Cases_on ‘l’ \\ fs [] \\
 simp [init_run_def, has_rtltype_v_def] \\ qmatch_goalsub_abbrev_tac ‘init_run bs' _’ \\
 drule_first \\ pop_assum (qspecl_then [‘bs'’, ‘shift + 1’] strip_assume_tac) \\
 unabbrev_all_tac \\ qexists_tac ‘bs''’ \\ rpt conj_tac
 >- (qpat_x_assum ‘init_run _ _ = _’ (assume_tac o GSYM) \\ fs [combinTheory.o_DEF, arithmeticTheory.ADD1] \\ f_equals_tac \\ simp [FUN_EQ_THM])
 >- (rpt strip_tac \\ simp [] \\ TOP_CASE_TAC
  >- (simp [arithmeticTheory.ADD1] \\ Cases_on ‘n = shift’
   >- (rveq \\ simp [cget_var_cset_var])
   >- (simp [cget_var_cset_var] \\ IF_CASES_TAC \\ fs [] \\
      Cases_on ‘n - shift’ \\ fs [] \\ f_equals_tac \\ fs [] \\ rw []))
  >- simp [cget_var_cset_var])
 \\ fs [cset_var_fbits]
QED

(* Holds for any reg_type but that's more general than we need *)
Theorem init_run_blasted_array:
 !finp inps s s' bs reg rdata l regs.
 init_run s [((reg, 0), rdata)] = INR s' /\
 rdata.init = SOME (CArray l) ∧

 blast_regs_distinct regsall ∧
 MEM ((reg, 0), rdata) regsall ∧ 

 blast_reg_init_rel regs s bs ∧
 LENGTH l = LENGTH inps ==>
 ?bs'. init_run bs (MAPi (λi inp. ((reg, i), <|type := CBool_t; reg_type := Reg; init := SOME (CBool (EL i l)); inp := finp inp|>)) inps) = INR bs' /\
       blast_reg_init_rel regs s' bs'
Proof
 simp [blast_regs_distinct_def, blast_reg_name_def] \\ rpt strip_tac' \\
 drule_strip ALOOKUP_ALL_DISTINCT_MEM \\
 drule_strip init_run_blasted_array_help \\
 pop_assum (qspecl_then [‘finp’, ‘reg’, ‘Reg’, ‘bs’, ‘0’] strip_assume_tac) \\
 fs [init_run_def, blast_reg_init_rel_def, cset_var_fbits] \\ rpt strip_tac \\ simp [cget_var_cset_var] \\ IF_CASES_TAC
 >- (gs [has_rtltype_v_correct, rtltype_v_cases, build_combs_si_reg_entry_def] \\
     gen_tac \\ CASE_TAC)
 >- fs []
QED

Triviality MAPi_ignore_second_arg_GENLIST':
 !l f j. MAPi (λi inp. f (i+j)) l = GENLIST (λi. f (i+j)) (LENGTH l)
Proof
 Induct \\ rw [GENLIST_CONS] \\ first_x_assum (qspecl_then [‘f’, ‘j + 1’] mp_tac) \\
 simp [combinTheory.o_DEF, arithmeticTheory.ADD1] \\
 ‘!(a:num) i. j + (i + 1) = i + (j + 1)’ by decide_tac \\ pop_assum (once_rewrite_tac o sing) \\ simp []
QED

Triviality MAPi_ignore_second_arg_GENLIST:
 !l f. MAPi (λi inp. f i) l = GENLIST (λi. f i) (LENGTH l)
Proof
 rpt gen_tac \\ qspecl_then [‘l’, ‘f’, ‘0’] mp_tac MAPi_ignore_second_arg_GENLIST' \\ simp []
QED

Theorem blast_regs_init_correct:
 !regs regs' s s' bs blast_s.
 init_run s regs = INR s' /\
 blast_regs blast_s regs = INR regs' /\
 EVERY reg_init_ok regs /\
 deterministic_regs regs /\
 blast_regs_distinct regsall ∧
 (∀reg. MEM reg regs ⇒ MEM reg regsall) ∧
 blast_reg_init_rel regsall s bs ==>
 ?bs'. init_run bs regs' = INR bs' /\
       blast_reg_init_rel regsall s' bs'
Proof
 Induct >- simp [init_run_def, blast_regs_def] \\
 PairCases \\ rename1 `((reg, i), rdata)` \\
 fs [blast_regs_def, deterministic_regs_def, deterministic_reg_def, reg_init_ok_def] \\
 rpt gen_tac \\ reverse TOP_CASE_TAC

 (* PseudoReg *) >- (
 simp [init_run_def, build_combs_si_reg_entry_def] \\ rpt CASE_TAC \\ rpt strip_tac \\
 gs [mk_inp_marked_def, has_rtltype_v_correct, rtltype_v_cases] \\
 first_x_assum match_mp_tac \\ rpt asm_exists_tac \\
 fs [blast_reg_init_rel_def, cset_var_fbits, cget_var_cset_var] \\ rw [] \\ fs [] \\
 full_simp_tac (srw_ss()++boolSimps.DNF_ss) [] \\ drule_strip ALOOKUP_MEM \\
 imp_res_tac regsall_lem \\ fs [])

 (* Reg *) \\ TOP_CASE_TAC
 
 >- (* bool *) (simp [build_combs_si_reg_entry_def] \\ rpt TOP_CASE_TAC
 >- (rw [sum_bind_INR] \\ fs [init_run_def] \\ rpt TOP_CASE_TAC \\ gs [] \\
     first_x_assum match_mp_tac \\ rpt asm_exists_tac \\ fs [has_rtltype_v_correct, blast_reg_init_rel_cset_var_bool])
 >- (rw [sum_bind_INR] \\ every_case_tac \\ fs [sum_bind_INR] \\ rveq \\ fs [init_run_def] \\
     every_case_tac \\ fs [] \\
     first_x_assum match_mp_tac \\ rpt asm_exists_tac \\ gs [has_rtltype_v_correct, blast_reg_init_rel_cset_var_bool]))

 \\ every_case_tac \\ simp [sum_bind_INR, rtltype_v_cases]
 >- (* array -- genlist case (no inps) *)
 (rw [] \\ fs [init_run_append, Once init_run_cons] \\
 full_simp_tac (srw_ss()++boolSimps.DNF_ss) [GSYM MAPi_ignore_second_arg_GENLIST] \\
 qspecl_then [‘K NONE : 'a -> cell_input option’, ‘l’] mp_tac init_run_blasted_array \\ disch_then drule_strip \\
 simp [combinTheory.K_THM] \\ strip_tac \\ simp [] \\
 first_x_assum match_mp_tac \\ rpt asm_exists_tac)

 \\ (* array -- mapi case (inps) *)
 rpt strip_tac \\ full_case_tac \\ fs [sum_bind_INR, sum_check_INR] \\ rveq \\
 full_simp_tac (srw_ss()++boolSimps.DNF_ss) [init_run_append, Once init_run_cons] \\
 qspecl_then [‘SOME’, ‘l'’] mp_tac init_run_blasted_array \\ disch_then drule_strip \\
 simp [] \\ first_x_assum match_mp_tac \\ rpt asm_exists_tac
QED

Triviality mem_map_blast_reg_name_mem_map_reg_name:
 ∀regs reg i rdata. MEM (blast_reg_name ((reg, i), rdata)) (MAP blast_reg_name regs) ⇒ MEM reg (MAP reg_name regs)
Proof
 rw [MEM_MAP] \\ asm_exists_any_tac \\ PairCases_on ‘y’ \\ fs [blast_reg_name_def, reg_name_def]
QED

Triviality mem_map_blast_reg_name_mem_map_reg_name_unfolded:
 ∀regs reg i. MEM (reg,i) (MAP FST regs) ⇒ MEM reg (MAP reg_name regs)
Proof
 rw [MEM_MAP] \\ asm_exists_any_tac \\ PairCases_on ‘y’ \\ fs [reg_name_def]
QED

Theorem blast_regs_distinct:
 ∀regs regs' blast_s.
 blast_regs blast_s regs = INR regs' ∧ regs_distinct regs ⇒
 (∀reg. MEM reg (MAP reg_name regs') ⇒ MEM reg (MAP reg_name regs)) ∧ blast_regs_distinct regs'
Proof
 Induct >- rw [blast_regs_def, blast_regs_distinct_def] \\
 TRY PairCases \\ simp [blast_regs_def] \\ rpt gen_tac \\ reverse TOP_CASE_TAC
 >- (* PseudoReg *) (rpt strip_tac' \\ drule_strip regs_distinct_tl \\ drule_first \\ simp []) \\

 (* Reg *) TOP_CASE_TAC
 >- (every_case_tac \\ simp [sum_bind_INR] \\ rpt strip_tac' \\ every_case_tac \\ fs [sum_bind_INR] \\ rveq \\
    drule_strip regs_distinct_tl \\ drule_first \\ (rw [reg_name_def]
    >- (drule_first \\ simp [])
    >- (fs [blast_regs_distinct_def, regs_distinct_def] \\
        metis_tac [mem_map_blast_reg_name_mem_map_reg_name, reg_name_def])))

 \\ every_case_tac \\ simp [sum_bind_INR] \\ rpt strip_tac' \\ every_case_tac \\ fs [sum_bind_INR] \\ rveq \\
    drule_strip regs_distinct_tl \\ drule_first \\ (rw [reg_name_def]
    >- fs [MAP_GENLIST, MEM_GENLIST, indexedListsTheory.MEM_MAPi, reg_name_def]
    >- (drule_first \\ simp [])
    >- (fs [blast_regs_distinct_def, regs_distinct_def, blast_reg_name_def, reg_name_def,
            MAP_GENLIST, ALL_DISTINCT_GENLIST, indexedListsTheory.MAPi_GENLIST, ALL_DISTINCT_APPEND] \\
        rw [MEM_GENLIST, indexedListsTheory.MEM_MAPi, blast_reg_name_def] \\
        metis_tac [mem_map_blast_reg_name_mem_map_reg_name_unfolded]))
QED

Theorem blast_regs_deterministic:
 ∀regs regs' blast_s. blast_regs blast_s regs = INR regs' ∧ deterministic_regs regs ⇒ deterministic_regs regs'
Proof
 Induct \\ TRY PairCases \\ fs [blast_regs_def, deterministic_regs_def] \\
 rpt gen_tac \\ every_case_tac \\ rw [sum_bind_INR] \\
 every_case_tac \\ gvs [sum_bind_INR, deterministic_reg_def, EVERY_GENLIST, EVERY_MAPi, EVERYi_T, SF SFY_ss]
QED

Theorem blast_regs_reg_props:
 ∀regs regs' blast_s.
 blast_regs blast_s regs = INR regs' ⇒
 EVERY (λ(_,rdata). rdata.reg_type = Reg) regs' ∧
 EVERY (λ(_,rdata). rdata.type = CBool_t) regs'
Proof
 Induct \\ TRY PairCases \\ simp [blast_regs_def] \\ rpt gen_tac \\
 every_case_tac \\ rw [sum_bind_INR] \\
 every_case_tac \\ gvs [sum_bind_INR, EVERY_GENLIST, EVERY_MAPi, EVERYi_T, SF SFY_ss]
QED

Triviality MEM_MAP_reg_name_FST_glue:
 ∀reg regs. MEM reg (MAP reg_name regs) ⇔ ∃i. MEM (reg, i) (MAP FST regs)
Proof
 rw [MEM_MAP, pairTheory.EXISTS_PROD, reg_name_def]
QED

Triviality blast_regs_reverse_lookup_Reg:
 ∀combs_max ffs_max regs regs' blast_s.
 blast_regs blast_s regs = INR regs' ∧
 regs_ok blast_s.extenv combs_max ffs_max regs ∧
 regs_distinct regs ⇒
 (∀reg. MEM reg (MAP reg_name regs') ⇒ MEM reg (MAP reg_name regs)) ∧
 ∀reg i. MEM reg (MAP reg_name regs') ⇒ ∃rdata. ALOOKUP regs (reg,0) = SOME rdata ∧ rdata.reg_type = Reg
Proof
 ntac 2 gen_tac \\ Induct \\ TRY PairCases \\ fs [blast_regs_def, regs_distinct_def] \\ rpt gen_tac \\
 reverse TOP_CASE_TAC >- (rpt strip_tac' \\ fs [regs_ok_def, reg_name_def] \\ metis_tac []) \\
 TOP_CASE_TAC >- (TOP_CASE_TAC \\ simp [sum_bind_INR] \\ rpt strip_tac' \\ every_case_tac \\
                  gvs [sum_bind_INR, regs_ok_def, reg_ok_def, reg_name_def] \\
                  metis_tac []) \\
 every_case_tac \\ rw [sum_bind_INR] \\
 every_case_tac \\ gvs [sum_bind_INR, regs_ok_def, reg_ok_def, reg_name_def,
                        MEM_GENLIST, MAP_GENLIST, indexedListsTheory.MAPi_GENLIST, SF SFY_ss]
QED

(** initial_si **)

(*Theorem EVERY_ALOOKUP:
 ∀P l. ALL_DISTINCT (MAP FST l) ⇒ (EVERY P l ⇔ ∀k v. ALOOKUP l k = SOME v ⇒ P (k, v))
Proof
 rw [EVERY_MEM, pairTheory.FORALL_PROD] \\ metis_tac [ALOOKUP_ALL_DISTINCT_MEM, ALOOKUP_MEM]
QED

Theorem lookup_fromList_var_cmp:
 ∀l k v. lookup var_cmp k (fromList var_cmp l) = ALOOKUP l k
Proof
 Induct >- (EVAL_TAC \\ simp []) \\
 PairCases \\ simp [fromList_cons, lookup_insert_var_cmp, fromList_thm_var_cmp] \\ rw []
QED*)

Triviality lookup_initial_si_not_in_regs:
 ∀regs reg i. ¬MEM (reg, i) (MAP FST regs) ⇒ lookup var_cmp (RegVar reg i) (initial_si regs) = NONE
Proof
 Induct >- (EVAL_TAC \\ simp []) \\ PairCases \\ fs [initial_si_def, reg_name_def] \\
 rw [option_flatMap_def, build_combs_si_reg_entry_def] \\
 every_case_tac \\ simp [fromList_cons, lookup_insert_var_cmp, fromList_thm_var_cmp] \\ rw []
QED

Triviality MEM_IMP_reg_name:
 ∀reg i rdata regs. MEM ((reg, i), rdata) regs ⇒ MEM reg (MAP reg_name regs)
Proof
 rw [MEM_MAP, pairTheory.EXISTS_PROD, reg_name_def] \\ asm_exists_tac
QED

Triviality lookup_initial_si_in_regs:
 ∀regs reg i rdata.
 MEM ((reg, i), rdata) regs ∧ ALL_DISTINCT (MAP FST regs) ⇒
 lookup var_cmp (RegVar reg i) (initial_si regs) = OPTION_MAP SND (build_combs_si_reg_entry ((reg, i), rdata))
Proof
 Induct >- (EVAL_TAC \\ simp []) \\
 PairCases \\ rw []
 >- (simp [initial_si_def, option_flatMap_def, build_combs_si_reg_entry_def] \\ every_case_tac \\
     fs [fromList_cons, lookup_insert_var_cmp, fromList_thm_var_cmp, reg_name_def] \\
     drule_strip lookup_initial_si_not_in_regs \\ fs [initial_si_def]) \\
 drule_first \\
 ‘reg ≠ h0 ∨ i ≠ h1’ by (simp [] \\ rpt strip_tac \\ rveq \\ fs [MEM_MAP]) \\
 fs [initial_si_def, option_flatMap_def, build_combs_si_reg_entry_def] \\
 every_case_tac \\ gvs [fromList_cons, lookup_insert_var_cmp, fromList_thm_var_cmp] \\ rw [GENLIST_FUN_EQ]
QED

(* Alternative name: si_consistent_with_regs_initial_si *)
Theorem lookup_RegVar_initial_si:
 ∀regs. regs_distinct regs (*∧ EVERY reg_init_ok regs*) ⇒ si_consistent_with_regs (initial_si regs) regs
Proof
 rpt strip_tac \\ drule_strip regs_distinct_blast_regs_distinct \\
 fs [regs_distinct_def, blast_regs_distinct_def, blast_reg_name_def, si_consistent_with_regs_def] \\
 rpt gen_tac \\ Cases_on ‘ALOOKUP regs (reg, i)’
 >- (fs [ALOOKUP_NONE] \\ drule_strip lookup_initial_si_not_in_regs) \\
 drule_strip ALOOKUP_MEM \\ drule_strip lookup_initial_si_in_regs \\ simp []
QED

Theorem lookup_NetVar_initial_si:
 ∀regs n. lookup var_cmp (NetVar n) (initial_si regs) = NONE
Proof
 Induct >- (EVAL_TAC \\ simp []) \\
 PairCases \\ rpt strip_tac \\ fs [initial_si_def, option_flatMap_def, build_combs_si_reg_entry_def] \\
 every_case_tac \\ simp [fromList_cons] \\ dep_rewrite.DEP_REWRITE_TAC [lookup_insert_var_cmp] \\
 simp [fromList_thm_var_cmp]
QED

Theorem regs_distinct_alookup_alookup:
 ∀regs reg i i' rdata rdata'.
 regs_distinct regs ∧
 ALOOKUP regs (reg,i) = SOME rdata ∧
 ALOOKUP regs (reg,i') = SOME rdata' ⇒
 i' = i ∧ rdata' = rdata
Proof
 rewrite_tac [regs_distinct_def] \\ Induct \\ TRY PairCases \\ rw [] \\ fs [reg_name_def] \\
 TRY (drule_strip ALOOKUP_MEM) \\ fs [MEM_MAP, pairTheory.FORALL_PROD, reg_name_def] \\ metis_tac []
QED

Theorem blasterstate_ok_initial_si:
 ∀regs tmpnum max. regs_distinct regs ∧ max ≤ tmpnum ⇒ blasterstate_ok regs (initial_si regs) 0 max tmpnum
Proof
 rw [blasterstate_ok_def]
 >- simp [initial_si_def, fromList_thm_var_cmp]
 >- fs [lookup_NetVar_initial_si]
 >- (drule_strip lookup_RegVar_initial_si \\ fs [si_consistent_with_regs_def, build_combs_si_reg_entry_def] \\
     TOP_CASE_TAC) \\
 
 (reverse (Cases_on ‘var’) >- fs [lookup_NetVar_initial_si]) \\
 drule_strip lookup_RegVar_initial_si \\ fs [si_consistent_with_regs_def] \\
 first_x_assum (qspecl_then [‘s’, ‘n’] assume_tac)  \\
 gs [build_combs_si_reg_entry_def] \\ every_case_tac \\
 gvs [blast_cell_input_marked_ok_def, blast_cell_input_ok_def, mk_inp_marked_def, 
      cell_input_marked_not_pseudo_def, cell_input_not_pseudo_def, EVERY_GENLIST] \\
 rpt strip_tac \\ metis_tac [regs_distinct_alookup_alookup]
QED

(*Theorem si_cells_inv_initial_si:
 ∀regs max nl. regs_distinct regs ⇒ si_cells_inv (initial_si regs) max nl
Proof
 rw [si_cells_inv_def, si_cell_out_inv_def] \\ TRY (Cases_on ‘var’) \\ fs [lookup_NetVar_initial_si] \\
 drule_strip lookup_RegVar_initial_si \\ fs [si_consistent_with_regs_def] \\
 first_x_assum (qspecl_then [‘s’, ‘n'’] assume_tac) \\ rfs [build_combs_si_reg_entry_def] \\
 every_case_tac \\ gvs [inp_marked_NetVar_inv_def, EVERY_GENLIST, mk_inp_marked_def]
QED*)

(** Outs **)

Definition same_state_outs_def:
 same_state_outs cenv cenv' ⇔ ∀var. sum_alookup cenv' var = sum_alookup cenv var
End

Theorem blast_out_correct:
 blast_out blast_s (var, out) = INR varout' ∧
 out_ok (var, out) ∧
 blast_reg_rel_fext fext blast_s.si s bs ∧
 out_run fext s (var, out) = INR r ⇒
 out_run fext bs varout' = INR r
Proof
 Cases_on ‘out’ \\ rw [blast_out_def, sum_bind_INR, out_ok_def, out_run_def] \\ TOP_CASE_TAC \\
 fs [blast_reg_rel_fext_def, blast_rel_array_def, cell_inp_run_def, blast_cell_input_def] \\
 every_case_tac \\ fs [] \\
 first_x_assum (qspecl_then [‘var’, ‘0’] mp_tac) \\ simp [] \\ TOP_CASE_TAC \\ strip_tac \\
 gvs [out_run_def, cell_inp_run_def, sum_map_INR, sum_bind_INR, sum_mapM_EL, inp_marked_get_def] \\
 qexists_tac ‘MAP CBool l''’ \\ simp [EL_MAP, get_bool_def] \\ rpt strip_tac \\ rpt drule_first \\
 fs [inp_marked_get_INR]
QED

Triviality same_state_outs_cons:
 ∀x x' xs xs'. x = x' ∧ same_state_outs xs xs' ⇒ same_state_outs (x::xs) (x'::xs')
Proof
 ntac 2 Cases \\ rw [same_state_outs_def, sum_alookup_cons]
QED

Theorem blast_out_correct:
 ∀outs outs' blast_s s s' bs bs' fext si.
 blast_outs blast_s outs = INR outs' ∧
 EVERY out_ok outs ∧
 blast_reg_rel_fext fext blast_s.si s bs ∧
 sum_mapM (out_run fext s) outs = INR s' ⇒
 ∃bs'. sum_mapM (out_run fext bs) outs' = INR bs' ∧
       same_state_outs s' bs'
Proof
 Induct >- simp [blast_outs_def, sum_mapM_def, same_state_outs_def] \\
 PairCases \\ fs [blast_outs_def, sum_mapM_INR] \\ rpt strip_tac \\ rveq \\ simp [sum_mapM_INR] \\
 drule_strip blast_out_correct \\ drule_first \\ simp [same_state_outs_cons]
QED

(** Top level thm **)

Definition blasted_circuit_def:
 blasted_circuit (Circuit _ _ regs combs_nl ffs_nl) ⇔
  blast_regs_distinct regs ∧
  EVERY (λ(_, rdata). rdata.reg_type = Reg) regs ∧
  EVERY (λ(_, rdata). rdata.type = CBool_t) regs ∧
  deterministic_regs regs ∧
  deterministic_netlist combs_nl ∧
  ffs_nl = []
End

Theorem blasted_circuit_alt:
 ∀cir.
 blasted_circuit cir ⇔
  blast_regs_distinct (circuit_regs cir) ∧
  EVERY (λ(_, rdata). rdata.reg_type = Reg) (circuit_regs cir) ∧
  EVERY (λ(_, rdata). rdata.type = CBool_t) (circuit_regs cir) ∧
  deterministic_regs (circuit_regs cir) ∧
  deterministic_netlist (circuit_nl_combs cir) ∧
  (circuit_nl_ffs cir) = []
Proof
 Cases \\ simp [blasted_circuit_def, circuit_regs_def, circuit_nl_combs_def, circuit_nl_ffs_def]
QED

Triviality netlist_step_nl_ffs_nil:
 ∀fext s nl_combs nl_ffs regs.
 EVERY (λ(_,rdata). rdata.reg_type = Reg) regs ⇒
 netlist_step fext s (nl_combs ++ nl_ffs) [] regs = netlist_step fext s nl_combs nl_ffs regs
Proof
 simp [netlist_step_def, EVERY_Reg_FILTER_PseudoReg_lem, sum_foldM_append, sum_foldM_def, sum_bind_def]
QED

Triviality netlist_run_nl_ffs_nil:
 ∀n fext s nl_combs nl_ffs regs.
 EVERY (λ(_,rdata). rdata.reg_type = Reg) regs ⇒
 netlist_run fext s (nl_combs ++ nl_ffs) [] regs n = netlist_run fext s nl_combs nl_ffs regs n
Proof
 Induct \\ simp [netlist_run_def, netlist_step_nl_ffs_nil]
QED

Triviality MEM_reg_i_reg_name_lem:
 MEM (reg, i) (MAP FST regs) ⇒ MEM reg (MAP reg_name regs)
Proof
 simp [MEM_MAP, pairTheory.EXISTS_PROD, reg_name_def] \\ metis_tac []
QED
       
Theorem blast_circuit_correct:
 !circuit circuit' blast_s n fext fbits fbits' s keep combs_max ffs_max.
 blast_circuit circuit ffs_max = INR (circuit', blast_s) /\
 circuit_run fext fbits circuit n = INR (s, fbits') /\
 rtltype_extenv (circuit_extenv circuit) fext /\
 circuit_ok 0 combs_max ffs_max circuit /\ circuit_sorted circuit /\ deterministic_circuit circuit ==>
 circuit_extenv circuit' = circuit_extenv circuit ∧
 (∀reg i. MEM (reg, i) (MAP FST (circuit_regs circuit')) ⇒
          ∃rdata. ALOOKUP (circuit_regs circuit) (reg, 0) = SOME rdata ∧ rdata.reg_type = Reg) ∧
 blasted_circuit circuit' ∧
 ?s' fbits''. circuit_run fext fbits circuit' n = INR (s', fbits'') /\
              same_state_outs s s'
Proof
 namedCases ["extenv outs regs combs_nl ffs_nl"] \\ rpt gen_tac \\
 simp [blast_circuit_def, sum_bind_INR, sum_map_INR, circuit_extenv_def, circuit_ok_def,
       circuit_sorted_def, deterministic_circuit_def] \\
 rpt strip_tac' \\
 rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\ fs [circuit_run_def, sum_bind_INR] \\

 (* regs_init *)
 drule_strip regs_ok_EVERY_reg_init_ok \\
 drule_strip lookup_RegVar_initial_si \\
 drule_strip regs_distinct_blast_regs_distinct \\
 drule_strip blast_regs_init_correct \\
 disch_then (qspec_then ‘<|env := []; fbits := fbits|>’ mp_tac) \\
 impl_tac >- (simp [blast_reg_init_rel_def, cget_var_def]) \\

 drule_strip init_run_cenv_consistent_with_reg \\ impl_tac >- simp [] \\
 drule_strip init_run_bound \\ simp [] \\
 drule_strip init_run_only_regs \\ impl_tac >- simp [only_regs_nil] \\
 rpt strip_tac' \\
 
 (* netlist *)
 drule_strip blast_reg_init_rel_blast_reg_rel \\
 qspecl_then [‘combs_nl’, ‘ffs_nl’] assume_tac blast_netlist_blast_regs_correct \\
 drule_first \\ simp [] \\ disch_then drule_strip \\
 impl_tac >- simp [blasterstate_ok_initial_si] \\ strip_tac \\ rveq \\

 (* lift back up to top level *)
 drule_strip blast_regs_distinct \\
 drule_strip blast_regs_reg_props \\
 drule_strip blast_regs_deterministic \\
 drule_strip blast_regs_reverse_lookup_Reg \\
 drule_strip blast_out_correct \\
 fs [circuit_extenv_def, circuit_regs_def, blasted_circuit_def, deterministic_netlist_def, netlist_run_nl_ffs_nil] \\
 (* ad-hoc fix: *)
 metis_tac [MEM_MAP_reg_name_FST_glue]
QED

val _ = export_theory ();
