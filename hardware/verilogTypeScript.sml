open hardwarePreamble;

open bitstringTheory;

open verilogTheory sumExtraTheory;

(* This should really be replaced by a proper static type system, 
   formalizing the actual Verilog type system. The current "type system" is based on what's needed
   for translation from HOL to Verilog only. *)

val _ = new_theory "verilogType";

val _ = Datatype `
 vertype = VBool_t | VArray_t (num list)`;

(*
val (has_type_rules, has_type_ind, has_type_cases) = Hol_reln `
 (!v. has_type (VBool v) VBool_t) /\
 (!vs i. i <> 0 /\ i = LENGTH vs /\ (!v. MEM v vs ==> has_type v VBool_t) ==>
         has_type (VArray vs) (VArray_t [i])) /\
 (!vs i is. i <> 0 /\ i = LENGTH vs /\ (!v. MEM v vs ==> has_type v (VArray_t is)) ==>
            has_type (VArray vs) (VArray_t (i::is)))`;
*)

val (has_type_rules, has_type_ind, has_type_cases) = Hol_reln `
 (!v. has_type (VBool v) VBool_t) /\
 (!vs i. i = LENGTH vs /\ (!v. MEM v vs ==> has_type v VBool_t) ==>
         has_type (VArray vs) (VArray_t [i])) /\
 (!vs i is. i = LENGTH vs /\ is <> [] /\ (!v. MEM v vs ==> has_type v (VArray_t is)) ==>
            has_type (VArray vs) (VArray_t (i::is)))`;

val has_type_bool = has_type_rules |> CONJUNCT1;
val has_type_array_base = has_type_rules |> CONJUNCT2 |> CONJUNCT1;
val has_type_array_step = has_type_rules |> CONJUNCT2 |> CONJUNCT2;

(*
val has_type_cases_array_base = Q.store_thm("has_type_cases_array_base",
 `!vs i. has_type (VArray vs) (VArray_t [i]) <=>
         (i <> 0 /\ i = LENGTH vs /\ !v. MEM v vs ==> has_type v VBool_t)`,
 rpt gen_tac \\ eq_tac
 >- (once_rewrite_tac [has_type_cases] \\ rw [] \\ fs []
    >- (first_x_assum drule \\ Cases_on `v` \\ simp [has_type_VArray_not_VBool_t])
    \\ (first_x_assum drule \\ once_rewrite_tac [has_type_cases] \\ rw []))
 \\ strip_tac \\ match_mp_tac has_type_array_base \\ simp []);
*)

val has_type_cases_imp = has_type_cases |> SPEC_ALL |> EQ_IMP_RULE |> fst |> GEN_ALL;

val BOOL_def = Define `
  BOOL (b:bool) = \v. v = VBool b`;

val WORD_def = Define `
  WORD (w:'a word) = \v. v = w2ver w`;

(* Arrays are in reverse order as we only have packed arrays in "reverse order"
   in this formalization *)
val WORD_ARRAY_def = Define `
  WORD_ARRAY (a:'a word -> 'b word) v =
   case v of
       VBool _ => F
     | VArray vs => LENGTH vs = dimword(:'a) /\
                    !i. sum_revEL (w2n i) vs = INR (w2ver (a i))`;

val var_has_value_def = Define `
 var_has_value (env:envT) var P = ?v. ALOOKUP env var = SOME v /\ P v`;

val var_has_type_def = Define `
 var_has_type env var ty = ?v. ALOOKUP env var = SOME v /\ has_type v ty`;

(* Old var_has_type definition, used in translator, but should probably be replaced *)
val var_has_type_old_def = Define `
 var_has_type_old env var P = ?hrep. var_has_value env var (P hrep)`;

val nbq_var_has_type_def = Define `
 nbq_var_has_type s var ty = !v. get_nbq_var s var = INR v ==> has_type v ty`;

(* List version of var_has_type and nbq_var_has_type *)
val vars_has_type_def = Define `
 (vars_has_type env [] = T) /\
 (vars_has_type env ((v, ty) :: xs) = (var_has_type env v ty /\ vars_has_type env xs))`;

val nbq_vars_has_type_def = Define `
 (nbq_vars_has_type env [] = T) /\
 (nbq_vars_has_type env ((v, ty) :: xs) = (nbq_var_has_type env v ty /\ nbq_vars_has_type env xs))`;

(** Various lemmas **)

val vars_has_type_append = Q.store_thm("vars_has_type_append",
 `!vs tys1 tys2. vars_has_type vs (tys1 ++ tys2) <=> vars_has_type vs tys1 /\ vars_has_type vs tys2`,
 Induct_on `tys1` >- rw [vars_has_type_def] \\ Cases_on `h` \\ rw [vars_has_type_def] \\ eq_tac \\ simp []);

val same_shape_refl_help = Q.prove(
 `!v1 v2. v1 = v2 ==> same_shape v1 v2`,
 recInduct same_shape_ind \\ rw [same_shape_def]);

val same_shape_refl = Q.store_thm("same_shape_refl",
 `!v. same_shape v v`,
 rw [same_shape_refl_help]);

val same_shape_sym = Q.store_thm("same_shape_sym",
 `!v1 v2. same_shape v1 v2 = same_shape v2 v1`,
 recInduct same_shape_ind \\ rw [same_shape_def] \\ metis_tac []);

val same_shape_trans = Q.store_thm("same_shape_trans",
 `!v1 v2 v3. same_shape v1 v2 /\ same_shape v2 v3 ==> same_shape v1 v3`,
 recInduct same_shape_ind \\ rw [same_shape_def] \\ Cases_on `v3` \\ fs [same_shape_def] \\
 Cases_on `l` \\ fs [same_shape_def]);

val WORD_ver2n = Q.store_thm("WORD_ver2n",
 `!w v. WORD w v ==> ver2n v = INR (w2n w)`,
 rw [WORD_def, ver2n_def, ver2v_def, w2ver_def, sum_mapM_VBool, sum_map_def, v2n_w2v]);

val EXP_n_lt_2n = Q.store_thm("EXP_n_lt_2n",
 `!n. n < 2 ** n`,
 Induct \\ rw [arithmeticTheory.EXP]);

val same_shape_VArray_from_v = Q.store_thm("same_shape_VArray_from_v",
 `!v1 v2. LENGTH v1 = LENGTH v2 ==> same_shape (VArray (MAP VBool v1)) (VArray (MAP VBool v2))`,
 Induct \\ rw [same_shape_def] \\ Cases_on `v2` \\ fs [same_shape_def]);

val same_shape_LENGTH = Q.store_thm("same_shape_LENGTH",
 `!xs ys. same_shape (VArray xs) (VArray ys) ==> LENGTH xs = LENGTH ys`,
 Induct \\ Cases_on `ys` \\ rw [same_shape_def]);

val same_shape_APPEND = Q.store_thm("same_shape_APPEND",
 `!xs x ys y.
   same_shape (VArray xs) (VArray ys) /\ same_shape x y ==>
   same_shape (VArray (xs ++ [x])) (VArray (ys ++ [y]))`,
 Induct \\ Cases_on `ys` \\ rw [same_shape_def]);

val same_shape_VArray_cong = Q.store_thm("same_shape_VArray_cong",
 `!l l'.
   (!n. n < LENGTH l ==> ?ln l'n. sum_revEL n l = INR ln /\ sum_revEL n l' = INR l'n /\
                                  same_shape ln l'n) /\
   LENGTH l = LENGTH l' ==>
   same_shape (VArray l) (VArray l')`,
 Induct \\ Cases_on `l'` \\ rw [same_shape_def]
 >- (first_x_assum (qspec_then `LENGTH l` mp_tac) \\ impl_tac >- DECIDE_TAC \\ fs [sum_revEL_LENGTH])
 \\ first_x_assum match_mp_tac \\ rpt strip_tac \\ fs [] \\
    first_x_assum (qspec_then `n` mp_tac) \\ impl_tac >- DECIDE_TAC \\ metis_tac [sum_revEL_INR_LENGTH]);

val same_shape_VArray_sum_revEL_cong = Q.store_thm("same_shape_VArray_sum_revEL_cong",
 `!l l' n.
   (!(i:'a word). ?lsub. LENGTH lsub = n /\ sum_revEL (w2n i) l = INR (VArray (MAP VBool lsub))) /\
   (!(i:'a word). ?l'sub. LENGTH l'sub = n /\ sum_revEL (w2n i) l' = INR (VArray (MAP VBool l'sub))) /\
   LENGTH l = dimword (:'a) /\
   LENGTH l' = dimword (:'a) ==>
   same_shape (VArray l) (VArray l')`,
 rpt strip_tac \\ match_mp_tac same_shape_VArray_cong \\ rpt strip_tac \\ fs [] \\
 rpt (first_x_assum (qspec_then `n2w n':'a word` assume_tac)) \\
 fs [w2n_n2w] \\ rpt strip_tac \\
 `n' < dimword (:'a)` by metis_tac [dimword_def, EXP_n_lt_2n, arithmeticTheory.LESS_TRANS] \\
 fs [arithmeticTheory.LESS_MOD] \\ match_mp_tac same_shape_VArray_from_v \\ fs []);

val same_shape_w2ver = Q.store_thm("same_shape_w2ver",
 `!(w1:'a word) (w2:'a word). same_shape (w2ver w1) (w2ver w2)`,
 rw [w2ver_def, same_shape_VArray_from_v]);

val same_shape_BOOL = Q.store_thm("same_shape_BOOL",
 `!b1 v1 b2 v2. BOOL b1 v1 /\ BOOL b2 v2 ==> same_shape v1 v2`,
 rw [BOOL_def, same_shape_def]);

val same_shape_WORD = Q.store_thm("same_shape_WORD",
 `!w1 v1 w2 v2. WORD (w1:'a word) v1 /\ WORD (w2:'a word) v2 ==> same_shape v1 v2`,
 rw [WORD_def, w2ver_def, same_shape_VArray_from_v]);

val same_shape_WORD_ARRAY = Q.store_thm("same_shape_WORD_ARRAY",
 `!(w1:'a word -> 'b word) v1 (w2:'a word -> 'b word) v2.
   WORD_ARRAY w1 v1 /\ WORD_ARRAY w2 v2 ==> same_shape v1 v2`,
 rw [WORD_ARRAY_def, w2ver_def] \\ Cases_on `v1` \\ Cases_on `v2` \\ fs [] \\
 match_mp_tac same_shape_VArray_sum_revEL_cong \\ qexists_tac `dimindex (:'b)` \\
 metis_tac [length_w2v]);

(** Has value/type thms **)

(* var_has_value_imp_var_has_type *)

val has_type_VArray_not_VBool_t = Q.store_thm("has_type_VArray_not_VBool_t",
 `!vs. ~has_type (VArray vs) VBool_t`,
 gen_tac \\ once_rewrite_tac [has_type_cases] \\ strip_tac \\ fs []);

val has_type_VBool_not_VArray_t = Q.store_thm("has_type_VBool_not_VArray_t",
 `!b is. ~has_type (VBool b) (VArray_t is)`,
 rpt gen_tac \\ once_rewrite_tac [has_type_cases] \\ strip_tac \\ fs []);

val has_type_VArray_tl = Q.store_thm("has_type_VArray_tl",
 `!y ys.
   has_type (VArray (y::ys)) (VArray_t [SUC (LENGTH ys)]) ==>
   has_type (VArray ys) (VArray_t [LENGTH ys])`,
 rewrite_tac [Once has_type_cases] \\ rw [] \\ match_mp_tac has_type_array_base \\ simp []);

val var_has_value_var_has_type_BOOL = Q.store_thm("var_has_value_var_has_type_BOOL",
 `!var b env.
   var_has_value env var (BOOL b) ==> var_has_type env var VBool_t`,
 rw [var_has_value_def, var_has_type_def, BOOL_def, has_type_rules]);

val var_has_type_old_var_has_type_BOOL = Q.store_thm("var_has_type_old_var_has_type_BOOL",
 `!var env.
   var_has_type_old env var BOOL <=> var_has_type env var VBool_t`,
 rw [var_has_type_old_def] \\ eq_tac
 >- rw [var_has_value_var_has_type_BOOL]
 \\ rw [var_has_type_def, Once has_type_cases, var_has_value_def, BOOL_def] \\ rw []);

val has_type_w2ver = Q.store_thm("has_type_w2ver",
 `!(w:'a word). has_type (w2ver w) (VArray_t [dimindex (:'a)])`,
 rw [w2ver_def] \\ match_mp_tac has_type_array_base \\ rw [MEM_MAP] \\ simp [has_type_rules]);

val var_has_value_var_has_type_WORD = Q.store_thm("var_has_value_var_has_type_WORD",
 `!var (w:'a word) env.
   var_has_value env var (WORD w) ==> var_has_type env var (VArray_t [dimindex (:'a)])`,
 rw [var_has_value_def, var_has_type_def, WORD_def, has_type_w2ver]);

val var_has_type_old_var_has_type_WORD_help = Q.prove(
 `!vs. (!v. MEM v vs ==> has_type v VBool_t) ==> ?bs. vs = MAP VBool bs`,
 Induct \\ rw [] \\ reverse (Cases_on `h`)
 >- (pop_assum (qspec_then `VArray l` mp_tac) \\ simp [has_type_VArray_not_VBool_t]) \\
 last_x_assum mp_tac \\ impl_tac >- simp [] \\ strip_tac \\ qexists_tac `b::bs` \\
 simp []);

val var_has_type_old_var_has_type_WORD = Q.store_thm("var_has_type_old_var_has_type_WORD",
 `!var env.
   var_has_type_old env var (WORD:'a word -> value -> bool) <=>
   var_has_type env var (VArray_t [dimindex (:'a)])`,
 rw [var_has_type_old_def] \\ eq_tac
 >- rw [var_has_value_var_has_type_WORD]
 \\ rw [var_has_type_def, Once has_type_cases, var_has_value_def, WORD_def] \\ rw [w2ver_def] \\
    drule_strip var_has_type_old_var_has_type_WORD_help \\ 
    qexists_tac `v2w bs` \\ match_mp_tac MAP_CONG \\ simp [w2v_v2w]);

val var_has_type_old_var_has_type_WORD_ARRAY = Q.store_thm("var_has_type_old_var_has_type_WORD_ARRAY",
 `!var env.
   var_has_type_old env var (WORD_ARRAY:('a word -> 'b word) -> value -> bool) <=>
   var_has_type env var (VArray_t [dimword (:'a); dimindex (:'b)])`,
 cheat);

val var_has_value_var_has_type_WORD_ARRAY_help = Q.prove(
 `!l (w:'a word -> 'b word) v.
   LENGTH l = dimword (:'a) /\ (!(i:'a word). sum_revEL (w2n i) l = INR (w2ver (w i))) /\ MEM v l ==>
   ?(w':'b word). v = w2ver w'`,
 simp [MEM_EL, sum_revEL_def] \\ rpt strip_tac \\ rveq \\
 first_x_assum (qspec_then `n2w (LENGTH l - n - 1)` assume_tac) \\
 fs [] \\ `(LENGTH l - (n + 1)) MOD dimword (:'a) = (LENGTH l - (n + 1))` by fs [] \\
 fs [] \\ FULL_CASE_TAC \\ fs [] \\ fs [sum_EL_EL] \\
 `LENGTH l − (LENGTH l − (n + 1) + 1) = n` by DECIDE_TAC \\ fs [] \\
 metis_tac []);

val var_has_value_var_has_type_WORD_ARRAY = Q.store_thm("var_has_value_var_has_type_WORD_ARRAY",
 `!var (w:'a word -> 'b word) env.
   var_has_value env var (WORD_ARRAY w) ==>
   var_has_type env var (VArray_t [dimword (:'a); dimindex(:'b)])`,
 rw [var_has_value_def, var_has_type_def, WORD_ARRAY_def] \\
 FULL_CASE_TAC \\ fs [] \\
 match_mp_tac has_type_array_step \\
 simp [dimword_def] \\ rpt strip_tac \\ drule var_has_value_var_has_type_WORD_ARRAY_help \\
 rpt (disch_then drule) \\ strip_tac \\ rveq \\ simp [has_type_w2ver]);

val var_has_type_get_var = Q.store_thm("var_has_type_get_var",
 `!s name ty. var_has_type s.vars name ty ==> ?v. get_var s name = INR v`,
 rw [var_has_type_def, var_has_value_def, get_var_def] \\ TOP_CASE_TAC);

(* Can be generalized *)
val has_type_same_shape_help = Q.store_thm("has_type_same_shape_help",
 `!v. (!v'. same_shape v' v ==> has_type v' VBool_t) <=> has_type v VBool_t`,
 Cases \\ eq_tac \\ rpt strip_tac \\ TRY (Cases_on `v'`) \\ fs [has_type_rules, same_shape_def]
 >- (pop_assum (qspec_then `VArray l` mp_tac) \\ simp [same_shape_refl])
 \\ fs [has_type_VArray_not_VBool_t]);

val same_shape_has_type = Q.store_thm("same_shape_has_type",
 `!v v' ty. same_shape v' v /\ has_type v ty ==> has_type v' ty`,
 cheat);

val has_type_same_shape = Q.store_thm("has_type_same_shape",
 `!v v' ty. has_type v' ty /\ has_type v ty ==> same_shape v' v`,
 cheat);

(*
 recInduct same_shape_ind \\ rpt strip_tac
 >- (Cases_on `ty` \\ fs [has_type_rules, has_type_VBool_not_VArray_t])
 >- drule has_type_cases_imp \\ rw []
    >- match_mp_tac has_type_array_base \\ fs [same_shape_def, same_shape_LENGTH] \\
       rpt strip_tac
       >- (rveq \\ first_assum (qspec_then `y` assume_tac) \\ fs [])
       \\ drule has_type_VArray_tl \\ strip_tac \\ first_x_assum drule \\ strip_tac \\
          once_rewrite_tac [has_type_cases] \\ rw [] \\ pop_assum mp_tac \\
          once_rewrite_tac [has_type_cases] \\ rw [] \\ pop_assum drule \\
          Cases_on `v` >- simp [] \\ once_rewrite_tac [has_type_cases] \\ rw []
    \\ match_mp_tac has_type_array_step \\ fs [same_shape_def, same_shape_LENGTH] \\
       rpt strip_tac
       >- (rveq \\ first_assum (qspec_then `y` assume_tac) \\ fs [])
       \\ 
 >- fs [same_shape_def]
 >- fs [same_shape_def]
 >- fs [same_shape_def]
 >- fs [same_shape_def]
*)

(*
val has_type_same_shape = Q.store_thm("has_type_same_shape",
 `!v ty. has_type v ty ==> !v'. same_shape v' v ==> has_type v' ty`,
 ho_match_mp_tac has_type_ind \\ rpt strip_tac
 >- (Cases_on `v'` \\ fs [same_shape_def, has_type_rules])
 >- Cases_on `v'` \\ fs [same_shape_def] \\ match_mp_tac has_type_array_base \\
    fs [same_shape_LENGTH, same_shape_def, has_type_same_shape_help] \\ rpt strip_tac \\
    first_x_assum match_mp_tac \\ 
*)

val _ = export_theory ();
