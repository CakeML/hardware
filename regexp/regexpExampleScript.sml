open hardwarePreamble;

open arithmeticTheory stringTheory;

open dep_rewrite;

open regexp_compilerTheory;

val _ = new_theory "regexpExample";

val _ = guess_lengths ();
val _ = prefer_num ();

(****
 Cleaner DFA semantics
 ****)

(* exec_dfa, but also return last state, and Vector + option wrappers *)
val exec_dfa_state_def = Define `
 (exec_dfa_state finals table n "" = (EL n finals, n)) /\
 (exec_dfa_state finals table n (STRING c t) =
  exec_dfa_state finals table (EL (ORD c) (EL n table)) t)`;

(*val exec_dfa_state_ind = theorem "exec_dfa_state_ind";*)

(*
val cleanup_finals_def = Define `
 cleanup_finals (Vector fs) = fs`;

val cleanup_Vectors_def = Define `
 (cleanup_Vectors [] = []) /\
 (cleanup_Vectors (Vector x::xs) = x :: cleanup_Vectors xs)`;

val cleanup_SOMEs_def = Define `
 (cleanup_SOMEs [] = SOME []) /\
 (cleanup_SOMEs (NONE :: xs) = NONE) /\
 (cleanup_SOMEs (SOME x :: xs) = case cleanup_SOMEs xs of
                                     SOME xs => SOME (x :: xs)
                                   | NONE => NONE)`;

val cleanup_table_def = Define `
 cleanup_table (Vector table) = cleanup_SOMEs (MAP cleanup_SOMEs (cleanup_Vectors table))`;

val cleanup_Vectors_MAP_Vector = Q.store_thm("cleanup_Vectors_MAP_Vector",
 `!xs. cleanup_Vectors (MAP Vector xs) = xs`,
 Induct \\ rw [cleanup_Vectors_def]);
*)

val from_hfinals_def = Define `
 from_hfinals = Vector`;

val from_htable_def = Define `
 from_htable = Vector o (MAP (Vector o MAP SOME))`;

val exec_dfa_state_APPEND = Q.store_thm("exec_dfa_state_APPEND",
 `!str1 str2 finals table n n' accept.
   exec_dfa_state finals table n str1 = (accept, n') /\ str2 <> "" ==>
   exec_dfa_state finals table n (APPEND str1 str2) = exec_dfa_state finals table n' str2`,
 Induct \\ rpt strip_tac \\ fs [exec_dfa_state_def]);

(****
 Regexp example
 ****)

val regexp = Regexp_Type.fromString "fo+bar";
val regexp_res = regexpLib.matcher regexpLib.HOL regexp;

val cert = #certificate regexp_res |> valOf;

local
 val regexp_term = cert |> SPEC_ALL |> concl |> rhs |> rator |> rand
in
val foobar_regex_def = Define `
 foobar_regex = ^regexp_term`;
end;

val cert = cert |> REWRITE_RULE [GSYM foobar_regex_def];

fun mk_list' l ty =
 Vector.foldr listSyntax.mk_cons (listSyntax.mk_nil ty) l;

fun mk_bool b =
 if b then T else F;

val hfinal =
 regexp_res
 |> #final
 |> Vector.map mk_bool
 |> flip mk_list' bool;

val htable =
 regexp_res
 |> #table
 |> Vector.map (flip mk_list' num o Vector.map term_of_int)
 |> flip mk_list' (listSyntax.mk_list_type num);

val valid_state_def = Define `
 valid_state nos n <=> n < nos`;

val valid_trans_def = Define `
 valid_trans nos trans <=>
  LENGTH trans = nos /\
  !s. valid_state nos s ==> LENGTH (EL s trans) = 256 /\
                            (!c. valid_state nos (EL (ORD c) (EL s trans)))`;

val sub_sub_from_clean_table = Q.store_thm("sub_sub_from_clean_table",
 `!nos trans n m.
   valid_trans nos trans /\ valid_state nos n ==>
   sub (sub (from_htable trans) n) (ORD m) = SOME (EL (ORD m) (EL n trans))`,
 rw [valid_state_def, valid_trans_def, from_htable_def, sub_def, combinTheory.o_DEF,
     EL_MAP, ORD_BOUND]);

val valid_state_trans = Q.store_thm("valid_state_trans",
 `!state nos trans n.
   valid_state nos state /\ valid_trans nos trans ==> valid_state nos (EL (ORD n) (EL state trans))`,
 rw [valid_trans_def]);

(* Depends on valid trans and state, so place here... *)
val exec_dfa_state_correct = Q.store_thm("exec_dfa_state_correct",
 `!s nos finals table n.
   valid_trans nos table /\ valid_state nos n ==>
   FST (exec_dfa_state finals table n s) =
   exec_dfa (from_hfinals finals) (from_htable table) n s`,
 Induct \\ rpt strip_tac \\ once_rewrite_tac [exec_dfa_state_def, exec_dfa_def]
 >- simp [from_hfinals_def, sub_def] \\
 drule_strip sub_sub_from_clean_table \\
 simp [] \\ drule_strip valid_state_trans \\
 pop_assum (qspec_then `h` assume_tac) \\
 first_x_assum drule_strip \\ simp []);

val exec_dfa_state_correct_valid_state_lem = Q.prove(
 `!s nos finals table n.
   valid_trans nos table /\ valid_state nos n ==>
   valid_state nos (SND (exec_dfa_state finals table n s))`,
 Induct \\ rw [exec_dfa_state_def, valid_trans_def]);

val exec_dfa_state_correct_valid_state = Q.store_thm("exec_dfa_state_correct_valid_state",
 `!s nos finals table n accept n'.
   valid_trans nos table /\
   valid_state nos n /\
   exec_dfa_state finals table n s = (accept, n') ==>
   valid_state nos n'`,
 rpt strip_tac \\ drule_strip exec_dfa_state_correct_valid_state_lem \\
 pop_assum (qspecl_then [`s`, `finals`] mp_tac) \\ simp []);

(****
 Circuit
 ****)

(* Can we just use alpha here instead? *)
val state_ty = ``:word4``;
val state_size_ty = wordsSyntax.dest_word_type state_ty;
val state_size = state_size_ty |> fcpSyntax.dest_numeric_type |> Arbnumcore.toInt;
(*val state_num_ty =
 Arbnumcore.pow (Arbnumcore.two, state_size)
 |> fcpSyntax.mk_numeric_type
 |> wordsSyntax.mk_word_type;
val state_size = state_size |> Arbnumcore.toInt;*)

val _ = Datatype `
 rc = <| (* IO *)
         accept : bool;

         (* Internal state *)
         state : ^state_ty;
         state_start : ^state_ty;
         state_is_final : ^state_ty -> bool;

         next_state_info : ^state_ty -> word8 -> ^state_ty; (* state -> (char -> state) *)
       |>`;

val _ = Datatype `
 rc_ext = <| new_package : bool; data_valid : bool; data : word8 |>`;

val regexp_def = Define `
 regexp fext (s:rc) =
  let s' = (if fext.new_package then
             s with state := s.state_start
            else if fext.data_valid then
             s with state := s.next_state_info s.state fext.data
            else
             s) in
  s' with <| accept := s'.state_is_final s'.state |>`; (* reject (= ~accept) ignored for now *)

val regexp_alt = Q.store_thm("regexp_alt",
 `!fext s. regexp fext s =
  let s' = (if fext.new_package then
             s with state := s.state_start
            else if fext.data_valid then
             s with state := s.next_state_info s.state fext.data
            else
             s) in
  s' with <| accept := s.state_is_final s'.state |>`,
 rw [regexp_def]);

val circuit_def = Define `
 (circuit init fext 0 = init) /\
 (circuit init fext (SUC n) = regexp (fext n) (circuit init fext n))`;

(* Operations on fext *)

val genlist_option_def = Define `
 (genlist_option f 0 = []) /\
 (genlist_option f (SUC n) = case (f n) of
                              NONE => genlist_option f n
                            | SOME f_n => SNOC f_n (genlist_option f n))`;

val str_of_ext_def = Define `
 str_of_ext ext start len =
  genlist_option (\i. if (ext (start + i)).data_valid then
                        SOME (CHR (w2n (ext (start + i)).data))
                      else
                        NONE) len`;

val str_of_ext_valid_data = Q.store_thm("str_of_ext_valid_data",
 `!ext n m.
   (ext (n + m)).data_valid ==>
   str_of_ext ext n (SUC m) = SNOC (CHR (w2n (ext (n + m)).data)) (str_of_ext ext n m)`,
 rw [str_of_ext_def, genlist_option_def]);

val str_of_ext_not_valid_data = Q.store_thm("str_of_ext_not_valid_data",
 `!ext n m. ~(ext (n + m)).data_valid ==> (str_of_ext ext n (SUC m)) = (str_of_ext ext n m)`,
 rw [str_of_ext_def, genlist_option_def]);

(* More data transformations *)

local
 val hwnos = ``LENGTH ^hfinal`` |> listLib.LENGTH_CONV |> concl |> rhs
in
val hwnos_def = Define `
 hwnos = ^hwnos`;
end;

(* hardcoded state size: *)
val hwfinal_def = Define `
 hwfinal (s:word4) = if w2n s < hwnos then EL (w2n s) ^hfinal else F`;

(* hardcoded state size: *)
val hwtable_def = Define `
 hwtable (s:word4) (c:word8) = if w2n s < hwnos then n2w (EL (w2n c) (EL (w2n s) ^htable)) else (0w:word4)`;

val valid_hardware_state_def = Define `
 valid_hardware_state nos n = (w2n n < nos)`;

val valid_hardware_trans_def = Define `
 valid_hardware_trans nos (trans : 'a word -> word8 -> 'a word) =
  !s c. valid_hardware_state nos s ==> valid_hardware_state nos (trans s c)`;

val from_hardware_trans_def = Define `
  from_hardware_trans nos trans =
   GENLIST (\state_i. GENLIST (w2n o (trans (n2w state_i)) o n2w) 256) nos`;

val from_hardware_sif_def = Define `
  from_hardware_sif nos sif = GENLIST (sif o n2w) nos`;

val valid_hardware_state_trans = Q.store_thm("valid_hardware_state_trans",
 `!nos state trans n.
   valid_hardware_state nos state /\ valid_hardware_trans nos trans ==> valid_hardware_state nos (trans state n)`,
 rw [valid_hardware_trans_def]);

val valid_hardware_state_valid_state_w2n = Q.store_thm("valid_hardware_state_valid_state_w2n",
 `!nos s. valid_hardware_state nos s ==> valid_state nos (w2n s)`,
 rw [valid_hardware_state_def, valid_state_def] \\ Cases_on `s` \\ fs [WORD_LO] \\
 Cases_on `nos < dimword (:'a)` \\ fs []);

val valid_state_valid_hardware_state = Q.store_thm("valid_state_valid_hardware_state",
 `!nos s. valid_state nos s ==> valid_hardware_state nos (n2w s)`,
 rw [valid_state_def, valid_hardware_state_def] \\
 qspecl_then [`dimword (:'a)`, `s`] assume_tac (GEN_ALL MOD_LESS_EQ) \\ fs []);

val valid_hardware_trans_valid_trans = Q.store_thm("valid_hardware_trans_valid_trans",
 `!nos trans.
   valid_hardware_trans nos trans ==>
   valid_trans nos (from_hardware_trans nos trans)`,
 once_rewrite_tac [valid_trans_def, from_hardware_trans_def] \\ rpt strip_tac
 >- (once_rewrite_tac [from_hardware_trans_def] \\ simp [])
 >- (once_rewrite_tac [from_hardware_trans_def] \\ DEP_REWRITE_TAC [EL_GENLIST] \\
    fs [LENGTH_GENLIST, valid_state_def])
 \\ once_rewrite_tac [from_hardware_trans_def] \\ DEP_REWRITE_TAC [EL_GENLIST] \\
    fs [valid_state_def, ORD_BOUND, valid_hardware_state_def, valid_hardware_trans_def] \\
    first_x_assum (qspecl_then [`n2w s`, `n2w (ORD c)`] mp_tac) \\ simp [] \\
    Cases_on `nos < dimword (:'a)` \\ fs [] \\ impl_tac
    >- (fs [MOD_LESS, dimword_def] \\
        qspecl_then [`dimindex (:'a)`, `s`] assume_tac bitTheory.MOD_2EXP_LT \\ simp [])
    \\ simp []);

val EL_from_hardware_trans = Q.store_thm("EL_from_hardware_trans",
 `!nos c s trans.
   valid_state nos s /\ valid_hardware_trans nos trans ==>
   EL (w2n c) (EL s (from_hardware_trans nos trans)) = w2n (trans (n2w s) c)`,
 rpt strip_tac \\ once_rewrite_tac [from_hardware_trans_def] \\
 DEP_REWRITE_TAC [EL_GENLIST] \\ fs [valid_state_def] \\
 Q.ISPEC_THEN `c` mp_tac w2n_lt \\ simp []);

val EL_from_hardware_sif = Q.store_thm("EL_from_hardware_sif",
 `!nos s sif. valid_state nos s ==> EL s (from_hardware_sif nos sif) = sif (n2w s)`,
 rpt strip_tac \\ simp [from_hardware_sif_def] \\ `sif (n2w s) = (sif o n2w) s` by simp [] \\
 pop_assum (fn th => PURE_REWRITE_TAC [th]) \\ match_mp_tac EL_GENLIST \\ fs [valid_state_def]);

val ORD_CHR_w2n_8 = Q.store_thm("ORD_CHR_w2n_8",
 `!(w:word8). ORD (CHR (w2n w)) = w2n w`,
 gen_tac \\ Q.ISPEC_THEN `w` mp_tac w2n_lt \\ simp [ORD_CHR]);

(****
 circuit correctness
 ****)

val circuit_constants = Q.store_thm("circuit_constants",
 `!n init ext.
  (circuit init ext n).state_start = init.state_start /\
  (circuit init ext n).state_is_final = init.state_is_final /\
  (circuit init ext n).next_state_info = init.next_state_info`,
 Induct \\ rw [circuit_def, regexp_def]);

val circuit_accept_correct = Q.store_thm("circuit_accept_correct",
 `!init ext state n.
   (circuit init ext (SUC n)).accept = init.state_is_final (circuit init ext (SUC n)).state`,
 ntac 3 gen_tac \\ Induct >- rw [circuit_def, regexp_def] \\
 once_rewrite_tac [circuit_def] \\ simp [regexp_alt, circuit_constants]);

(* TODO: Cleanup proof... *)
(* NOTE: Maybe want to say something about accept for each cycle instead, i.e. construct the string by
         searching backwards in time to previous new_package or beginning of time instead; in the end it
         depends on what users of the circuit need I guess... *)
val circuit_correct = Q.store_thm("circuit_correct",
 `!nos init ext m n.
   valid_hardware_state nos init.state /\
   valid_hardware_state nos init.state_start /\
   valid_hardware_trans nos init.next_state_info /\
   (ext n).new_package ==>
    (!p. p <= m ==> ~(ext (n + p)).new_package) ==>
     (case exec_dfa_state (from_hardware_sif nos init.state_is_final)
                          (from_hardware_trans nos init.next_state_info)
                          (w2n init.state_start)
                          (str_of_ext ext (n + 1) m) of (accept, state) =>
      (circuit init ext (SUC (n + m))).accept = accept /\
      (circuit init ext (SUC (n + m))).state = n2w state)`,
 rpt strip_tac \\ Induct_on `m` >- simp [] \\ rpt strip_tac \\ TOP_CASE_TAC \\
 qpat_x_assum `_ ==> _` mp_tac \\ impl_tac >- simp [] \\ TOP_CASE_TAC \\ strip_tac \\
 once_rewrite_tac [circuit_def] \\ simp [regexp_alt, circuit_constants] \\
 IF_CASES_TAC

 (* new data *)
 >- (simp [] \\ PURE_REWRITE_TAC [GSYM ADD_SUC] \\
 qabbrev_tac `s = circuit init ext (SUC (n + m))` \\
 qspecl_then [`ext`, `n + 1`, `m`] mp_tac str_of_ext_valid_data \\ impl_tac >- fs [ADD1] \\
 strip_tac \\ fs [] \\ drule exec_dfa_state_APPEND \\
 disch_then (qspec_then `STRING (CHR (w2n (ext (m + (n + 1))).data)) ""` mp_tac) \\
 rewrite_tac [exec_dfa_state_def, ORD_CHR_w2n_8] \\ strip_tac \\ fs [] \\ rveq \\

 DEP_REWRITE_TAC [EL_from_hardware_trans] \\ CONJ_TAC
 >- metis_tac [exec_dfa_state_correct_valid_state,
               valid_hardware_state_valid_state_w2n,
               valid_hardware_trans_valid_trans]
 >- (DEP_REWRITE_TAC [EL_from_hardware_sif] \\ simp [ADD1] \\
    metis_tac [valid_hardware_state_valid_state_w2n,
               valid_hardware_state_trans,
               valid_state_valid_hardware_state,
               exec_dfa_state_correct_valid_state,
               valid_hardware_state_valid_state_w2n,
               valid_hardware_trans_valid_trans]))

 (* no new data, rewrite as above *)
 \\ qsuff_tac `str_of_ext ext (n + 1) (SUC m) = str_of_ext ext (n + 1) m`
  >- (strip_tac \\ fs [ADD_SUC] \\ rveq \\ fs [GSYM ADD_SUC, circuit_accept_correct])
  \\ match_mp_tac str_of_ext_not_valid_data \\ fs [ADD1]);

val circuit_correct_clean = Q.store_thm("circuit_correct_clean",
 `!nos init ext m n.
   valid_hardware_state nos init.state /\
   valid_hardware_state nos init.state_start /\
   valid_hardware_trans nos init.next_state_info /\
   (ext n).new_package /\
   (!p. p <= m ==> ~(ext (n + p)).new_package) ==>
   (circuit init ext (SUC (n + m))).accept =
   exec_dfa (from_hfinals (from_hardware_sif nos init.state_is_final))
            (from_htable (from_hardware_trans nos init.next_state_info))
            (w2n init.state_start)
            (str_of_ext ext (n + 1) m)`,
 rpt strip_tac \\ drule circuit_correct \\ rpt (disch_then drule) \\
 TOP_CASE_TAC \\ DEP_REWRITE_TAC [GSYM exec_dfa_state_correct] \\
 simp [] \\ metis_tac [valid_hardware_trans_valid_trans, valid_hardware_state_valid_state_w2n]);

val lt_step = Q.prove(
 `!P n m. (n < m <=> P) ==> (n < SUC m <=> (P \/ n = m))`,
 rw [] \\ DECIDE_TAC);

val lt_base = Q.prove(`n < 1 <=> n = 0`, DECIDE_TAC);

val lt_256 = funpow (256 - 1) (MATCH_MP lt_step) lt_base |> EVAL_RULE;
val lt_states = funpow (7 - 1) (MATCH_MP lt_step) lt_base |> EVAL_RULE; (* <-- TODO: hardcoded *)

(* Slow but works *)
val valid_hardware_trans_hwtable = prove(
 ``valid_hardware_trans hwnos hwtable`` |> inst [ alpha |-> state_size_ty ],
 rw [valid_hardware_trans_def, valid_hardware_state_def, hwnos_def, hwtable_def] \\
 Cases_on `s` \\ fs [] \\ Cases_on `c` \\ fs [] \\

 FULL_SIMP_TAC bool_ss [lt_states] \\ simp [] \\
 FULL_SIMP_TAC bool_ss [lt_256] \\ EVAL_TAC);

val INIT_def = Define `
 INIT s <=>
  s.state = 0w /\
  s.state_start = 0w /\
  s.state_is_final = hwfinal /\
  s.next_state_info = hwtable`;

(*local
 val ss = wordsSyntax.mk_wordii (#start regexp_res, state_size)
in
val circuit_correct_clean' = 
 circuit_correct_clean
 |> Q.SPEC `hwnos`
 |> Q.SPEC `<| state := ^ss; state_start := ^ss;
               state_is_final := hwfinal;
               next_state_info := hwtable |>`
 |> SIMP_RULE (srw_ss()) [valid_hardware_trans_hwtable]
 |> SIMP_RULE (srw_ss()) [valid_hardware_state_def, hwnos_def]
 |> SPEC_ALL
end;*)

val circuit_correct_clean' = Q.prove(
 `INIT s /\
  (ext n).new_package ∧
  (∀p. p ≤ m ⇒ ¬(ext (n + p)).new_package) ⇒
  ((circuit s ext (SUC (n + m))).accept ⇔
   exec_dfa (from_hfinals (from_hardware_sif hwnos hwfinal))
            (from_htable (from_hardware_trans hwnos hwtable)) 0
            (str_of_ext ext (n + 1) m))`,
 rw [INIT_def] \\
 qspecl_then [`hwnos`, `s`, `ext`, `m`, `n`] mp_tac circuit_correct_clean \\ impl_tac
 >- (simp [valid_hardware_trans_hwtable] \\ simp [valid_hardware_state_def, hwnos_def])
 \\ simp []);

(* Evaluate final + table *)
val circuit_correct_clean'' =
 circuit_correct_clean'
 |> CONV_RULE (RAND_CONV (RHS_CONV (RATOR_CONV (RATOR_CONV ((RAND_CONV EVAL) THENC (RATOR_CONV (RAND_CONV EVAL)))))));

(* Evaluate table *)
val cert' = 
 cert
 |> CONV_RULE (STRIP_QUANT_CONV (LHS_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV EVAL)))));

val circuit_correct_regexp = save_thm("circuit_correct_regexp",
 circuit_correct_clean'' |> REWRITE_RULE [cert'] |> GEN_ALL);

val _ = export_theory ();
