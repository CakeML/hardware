structure translatorStmLib =
struct

open hardwarePreamble;

open verilogTheory;

open translatorTheory;
open translatorCoreLib translatorExpLib;

(* TODO: Move *)
val Eval_get_prog = rand;
val Eval_get_hol_prog = rand o rator;
val Eval_exp_get_pred_exp = rand o rand o rator;
val Eval_exp_CONV = RATOR_CONV o RAND_CONV;

(*
Testing:

“s with <| sum := 5w; avg := 4w |>” |> TypeBase.dest_record

TypeBase.updates_of state_ty

mk_eq(“s with <| avg := 5w; sum := 3w |>”,
      “s with <| sum := 3w; avg := 5w |>”) |> simpLib.SIMP_PROVE (srw_ss()) []

“s with <| sum := 3w; avg := 5w |>” |> dest_comb

val state_ty = ``:state``;
val comms = ["avg"];
val rel_pred = “state_rel”;

val tstate = build_tstate rel_pred comms state_ty;
val s = “s:state”;
val s' = “s:state”;

hol2hardware tstate s s' “let s' = s' with <|h0 := 4w; h2 := 2w |>;
                              ss = s' with h0 := 0w in
                              ss with h1 := 1w”

hol2hardware tstate s “if T then (s:state) else s”

hol2hardware tstate s “s with <| sum := s.avg; h0 := 0w; avg := 1w |>”

hol2hardware tstate s “s with <| avg := 1w; avg := 2w |>”

*)

fun rev_record tm = let
 val (ty, ups) = TypeBase.dest_record tm
 val tm' = TypeBase.mk_record (ty, rev ups)
in
 (tm', tm) |> mk_eq |> simpLib.SIMP_PROVE (srw_ss()) []
end;

fun strip_word_case tm = let
 fun strip_word_case_itr var tm =
  if is_cond tm then let
   val (c, ttm, ftm) = dest_cond tm
  in
   if is_eq c then let
    val (var', c) = dest_eq c
   in
    if var' ~~ var then
     (SOME c, ttm) :: strip_word_case_itr var ftm
    else
     [(NONE, tm)]
   end else
    [(NONE, tm)]
  end else
   [(NONE, tm)];

 val (tm, exp) = dest_literal_case tm
 val (var, tm) = dest_abs tm
 val (_, last_case) :: (SOME second_last_exp, second_last_case) :: tms = tm |> strip_word_case_itr var |> rev
 val tms = map (fn (k, v) => (valOf k, v)) tms
in
 (exp, var, last_case, second_last_exp, second_last_case, tms)
end;

fun first_PART_MATCH proj ths tm =
 case ths of
   nil => failwith "No match in list"
 | th::ths => PART_MATCH proj th tm handle HOL_ERR _ => first_PART_MATCH proj ths tm;

fun inst_Eval_env s v th = let
 val name = v |> dest_var |> fst
 val namet = fromMLstring name
 val vinv = predicate_for_value v
 val env_tm = mk_var ("env", “:envT”)
 val assum = mk_var_has_value (env_tm, namet, mk_comb(vinv, v))

 (* TODO: Should generate fresh variable here, but did not find any good API for this... *)
 val forallv = mk_var ("v", value_ty)
 val new_env = listSyntax.mk_cons (pairSyntax.mk_pair (namet, forallv), env_tm)

 val th = th |> DISCH assum
             |> INST [env_tm |-> new_env]
             |> ASM_CONV_RULE (PURE_ONCE_REWRITE_CONV [var_has_value_env_new_var
                                                       (*var_has_type_env_new_var*)]
                               THENC (DEPTH_CONV stringLib.string_EQ_CONV)
                               THENC REWRITE_CONV [])

 val (new_assum, th) = UNDISCH_TM th
 val th = th |> CONV_RULE (Eval_exp_CONV (UNBETA_CONV v))
             |> DISCH new_assum
             |> GEN forallv
in
 th
end;

(* For debugging: val tm = (!tm_trace) |> hd *)
(* val s = ``s:state_circuit`` *)
val tm_trace = ref ([]:term list);

(* Top entry-point (with tracing) *)
fun hol2hardware (tstate:tstate) s s' tm = let
 val () = tm_trace := []
 val r = hol2hardware' tstate s s' tm
 val rtm = r |> concl |> rator |> rand
in
 if identical rtm tm then
  r
 else
  failwith "Ops, rtm != tm!"
end

and hol2hardware' (tstate:tstate) s s' tm = let
 val () = (print "\nhol2hardware' call with tm: ";
           print_term tm;
           print "\n";
           tm_trace := tm :: !tm_trace)
 val ret = hol2hardware'_impl tstate s s' tm
 val () = tm_trace := tl (!tm_trace) (* <-- will only run if above call succeeded *)
in
 ret
end

and hol2hardware'_impl (tstate:tstate) s s' tm =
 (* Skip *)
 if is_var tm then
  if identical tm s' then
   ISPECL [#fext_rel tstate, #rel tstate, s, s'] Eval_Skip
  else
   raise UnableToTranslate (tm, "Unexpected state var")

 (* IfElse *)
 else if is_cond tm then let
  val (cond, tbranch, fbranch) = dest_cond tm
  val c' = hol2hardware_exp tstate s s' cond
  val tbranch' = hol2hardware' tstate s s' tbranch
  val fbranch' = hol2hardware' tstate s s' fbranch
 in
  MATCH_MP Eval_IfElse (LIST_CONJ [c', tbranch', fbranch'])
 end

 (* State sequencing or introduce new variable *)
 else if is_let tm then let
  val (body, arg) = dest_let tm
  val (v, body) = dest_abs body
  val vname = v |> dest_var |> fst |> fromMLstring
 in
 (* state update or just new local variable? *)
  if type_of v = #state_ty tstate then let
   fun trans_to_state_body_form th inners newstateprog = let
    val fext_rel = #fext_rel tstate in
       th |> CONV_RULE (Eval_exp_CONV (UNBETA_CONV inners))
          |> DISCH_ALL
          |> Q.INST [`env` |-> `env'`]
          |> Q.DISCH (`^fext_rel fextv fext /\ prun fextv (vs with vars := env) ^newstateprog = INR vs'`)
          |> Q.INST [`env'` |-> `vs'.vars`]
   end

   fun get_var_bubble_thm th = let
    val precond = th |> concl |> dest_imp |> snd
   in
    if is_imp precond then let
      val precond = precond |> dest_imp |> fst
    in
     SOME bubble_var_has_value
    (*if is_var_has_value precond then
      SOME bubble_var_has_value
    else if is_var_has_type_old precond then
      SOME bubble_var_has_type
    else
      raise UnableToTranslate (th |> concl, "Unknown precondition")*)
    end
    else
      NONE
   end

   fun bubble_var th bubble_thm = let
    val res = MATCH_MP bubble_thm th
    val precond = res |> concl |> dest_imp |> fst |> EVAL_PROVE
    val res = MATCH_MP res precond
   in
    UNDISCH res
   end

   fun bubble_vars th =
    case get_var_bubble_thm th of
      SOME bubble_thm => bubble_vars (bubble_var th bubble_thm)
    | NONE => th
    
   val arg' = hol2hardware' tstate s s' arg
   val body' = hol2hardware' tstate s v body
   val arg'_prog = arg' |> concl |> Eval_get_prog
   (* Lots of work is needed here since let-vars might not be translatable to mutable variables,
      consider e.g. (in pseudocode):

      let x = 2 in
       (let x = 3 in x + 5);
       x + 7 // if we translate "x" to the same mutable variable it is 3 here now!
   *)
   val body' = trans_to_state_body_form body' v arg'_prog
   val body' = bubble_vars body'
   val body' = body' |> Q.GENL [`vs`, `vs'`, `fextv`] |> GEN v |> GEN s
   (* can probably change a few things to use MATCH_MP instead of HO_MATCH_MP here *)
   val result = HO_MATCH_MP Eval_Eval (CONJ arg' body')
  in
   check_inv_Eval "let1" tm result
  end else let
   val arg' = hol2hardware_exp tstate s s' arg
   (* NOTE: In other situations, this might be another expression,
            but this is not relevant in this translation...
      NOTE: Not sure what the above NOTE means... *)
   val body' = hol2hardware' tstate s s' body
   val body' = inst_Eval_env s v body'
   val body' = INST [v |-> (arg' |> concl |> Eval_exp_get_pred_exp)] body'
   val result = LIST_CONJ [#rel_var_inv tstate, arg', body']
                |> MATCH_MP Eval_Let
                |> EVAL_MP
  in
   check_inv_Eval "let2" tm result
  end
 end

 (* Case on word type *)
 else if is_literal_case tm then let
  val (exp, var, last_case, second_last_exp, second_last_case, tms) = strip_word_case tm
  val exp_Eval = hol2hardware_exp tstate s s' exp
  val second_last_Eval = hol2hardware' tstate s s' second_last_case
  val Eval_holexp_CONV = RATOR_CONV o RAND_CONV
 in
  (* If the last term in the case is ARB, we must prove that we never execute that branch...
     Currently, we only handle the special case where all cases are covered in order *)
  if is_arb last_case then let
   val th = MATCH_MP Eval_Case_ARB second_last_Eval
            |> ISPECL [second_last_exp, var]
            |> Q.ID_SPEC (* <-- what happens on collision? *)
            |> EVAL_MP
   val Eval_exp_assum = th |> concl |> dest_imp |> fst
   val th = UNDISCH th
   val th = foldl (fn ((next_exp, next_case), th) => let
                    val next_Eval = hol2hardware' tstate s s' next_case
                   in
                    MATCH_MP Eval_Case_ARB_new_case (CONJ th next_Eval)
                    |> SPEC next_exp
                    |> EVAL_MP
                    |> UNDISCH
                   end) th tms
   val th = MATCH_MP th (ISPEC var word_ls_0)
   val th = (CONV_RULE o Eval_holexp_CONV) (UNBETA_CONV var THENC
                                            REWR_CONV (GSYM literal_case_THM)) th

   (*fun is_Eval_exp tm = case total (fst o dest_const o fst o strip_comb) tm of
                          NONE => false
                        | SOME name => name = "Eval_exp"
   val Eval_exp_assum = th |> hypset |> HOLset.find is_Eval_exp |> valOf*)
   val th = MATCH_MP (DISCH Eval_exp_assum th) exp_Eval
  in
   th
  end else let
   val last_Eval = hol2hardware' tstate s s' last_case
   val th = MATCH_MP Eval_Case_catch_all (CONJ second_last_Eval last_Eval)
            |> ISPECL [second_last_exp, var]
            |> Q.ID_SPEC (* <-- same problem as above? *)
   val Eval_exp_assum = th |> concl |> dest_imp |> fst
   val th = UNDISCH th
   val th = foldl (fn ((next_exp, next_case), th) => let
                    val next_Eval = hol2hardware' tstate s s' next_case
                   in
                    MATCH_MP Eval_Case_catch_all_new_case (CONJ th next_Eval)
                    |> ISPECL [next_exp, var]
                    |> UNDISCH
                   end) th tms
   val th = (CONV_RULE o Eval_holexp_CONV) (UNBETA_CONV var THENC
                                            REWR_CONV (GSYM literal_case_THM)) th
   val th = MATCH_MP (DISCH Eval_exp_assum th) exp_Eval
  in
   th
  end
 end

 (* Must be a variable write *)
 else if is_comb tm then let
  (*val (fupd_arg, arg) = dest_comb tm
  val (fupd, Kval) = dest_comb fupd_arg
  val newval = combinSyntax.dest_K_1 Kval*)
  fun build_key tm = let
   val (f, args) = strip_comb tm
  in
   if is_const f andalso length args = 2 andalso combinSyntax.is_K_1 (hd args) then
     (f |> dest_const |> fst) :: (args |> hd |> combinSyntax.dest_K_1 |> build_key)
   else
     []
  end
 
  val key = build_key tm

  fun opt_to_list NONE = []
    | opt_to_list (SOME x) = [x]
 in
  case lookup_opt key (#write_thms tstate) of
   SOME (base_thm, base_bit_thm, base_slice_thm) =>
   (*if identical arg s' then*) let
    val th = first_PART_MATCH (Eval_get_hol_prog o snd o dest_imp)
                              (opt_to_list base_slice_thm @ opt_to_list base_bit_thm @ [base_thm])
                              tm
    val precond = th |> concl |> dest_imp |> fst
    val precond = if is_conj precond then let
                   val (precond_eval, precond) = dest_conj precond
                   val precond_eval_th = EVAL_PROVE precond_eval
                   val precond_th = precond |> Eval_exp_get_pred_exp |> hol2hardware_exp tstate s s'
                  in
                   CONJ precond_eval_th precond_th
                  end else let
                   val precond_th = precond |> Eval_exp_get_pred_exp |> hol2hardware_exp tstate s s'
                  in
                   precond_th
                  end
    val result = MATCH_MP th precond
   in
    check_inv_Eval "state-base" tm result
   end (*else let
    val newval' = hol2hardware_exp tstate s s' newval
    val arg' = hol2hardware' tstate s s' arg
    val result = MATCH_MP step_thm (CONJ newval' arg') |> EVAL_MP
   in
    check_inv_Eval "state-let" tm result
   end*)
 | NONE =>
   case lookup_opt key (#write_2d_thms tstate) of
    SOME (base_thm, base_slice_thm) => let
     val th = first_PART_MATCH (Eval_get_hol_prog o snd o dest_imp) [base_slice_thm, base_thm] tm
     val (precond_eval, precond) = th |> concl |> dest_imp |> fst |> dest_conj
     val precond_eval_th = EVAL_PROVE precond_eval
     val precond_th = precond |> strip_conj
                              |> map (hol2hardware_exp tstate s s' o Eval_exp_get_pred_exp)
                              |> LIST_CONJ
     val result = MATCH_MP th (CONJ precond_eval_th precond_th)
    in
     check_inv_Eval "state-step" tm result
    end
  | NONE => failwith "Unknown state update"
 end
  
 else
  raise UnableToTranslate (tm, "Unknown case")

(* Main entry-point *)

(* Expected format: step_def fext s s' = ... *)
fun step2hardware tstate step_def = let
 val (elhs, erhs) = step_def |> concl |> strip_forall |> snd |> dest_eq
 val (elhs, s') = dest_comb elhs
 val (elhs, s) = dest_comb elhs
 val th = hol2hardware tstate s s' erhs
 val th = PURE_REWRITE_RULE [GSYM step_def] th (* <-- overkill *)
 val th = th |> Q.GEN ‘env’ |> GENL [s, s']
in
 th
end

end
