structure newTranslatorStmLib =
struct

open hardwarePreamble;

open verilogTheory;

open newTranslatorTheory;
open newTranslatorCoreLib newTranslatorExpLib;

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
   val arg' = hol2hardware' tstate s s' arg
   val body' = hol2hardware' tstate s v body
   val body' = CONV_RULE (RATOR_CONV (RAND_CONV (UNBETA_CONV v))) body'
   val body' = body' |> Q.GEN ‘env’ |> GENL [s, v]
   (*val arg'_prog = arg' |> concl |> EvalS_get_prog*)
  in
   (* can probably change a few things to use MATCH_MP instead of HO_MATCH_MP here *)
   HO_MATCH_MP Eval_Eval (CONJ arg' body')
  end else
   failwith "Non-state let handling disabled for now!"
   (*let
   val arg' = hol2hardware_exp s arg
      (* NOTE: In other situations, this might be another expression,
               but this is not relevant in this translation ... *)
      val body' = hol2hardware_body s body
      val body' = inst_EvalS_env s v body'
      val body' = INST [v |-> (arg' |> concl |> Eval_get_pred_exp)] body'
      val not_state_var = mk_neg (mk_state_var vname) |> EVAL_PROVE (* TODO: We compute this in inst_EvalS_env also ... *)
      val prun_bassn_type_pred_thm = get_prun_bassn_type_pred v
      val result = LIST_CONJ [not_state_var, prun_bassn_type_pred_thm, arg', body']
                   |> MATCH_MP EvalS_Let
                   |> UNDISCH
 end*)
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
  if last_case ~~ arb then let
   val th = MATCH_MP Eval_Case_ARB second_last_Eval
            |> ISPECL [second_last_exp, var]
            |> Q.ID_SPEC (* <-- what happens on collision? *)
            |> EVAL_MP
            |> UNDISCH
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
   val th = MATCH_MP (DISCH_ALL th) exp_Eval (* <-- not robust with DISCH_ALL here *)
  in
   th
  end else let
   val last_Eval = hol2hardware' tstate s s' last_case
   val th = MATCH_MP Eval_Case_catch_all (CONJ second_last_Eval last_Eval)
            |> ISPECL [second_last_exp, var]
            |> Q.ID_SPEC (* <-- same problem as above? *)
            |> UNDISCH
   val th = foldl (fn ((next_exp, next_case), th) => let
                    val next_Eval = hol2hardware' tstate s s' next_case
                   in
                    MATCH_MP Eval_Case_catch_all_new_case (CONJ th next_Eval)
                    |> ISPECL [next_exp, var]
                    |> UNDISCH
                   end) th tms
   val th = (CONV_RULE o Eval_holexp_CONV) (UNBETA_CONV var THENC
                                            REWR_CONV (GSYM literal_case_THM)) th
   val th = MATCH_MP (DISCH_ALL th) exp_Eval (* <-- not robust with DISCH_ALL here *)
  in
   th
  end
 end

 (* Must be a variable write *)
 else if is_comb tm andalso (tm |> rator |> is_comb) then let
  val (fupd_arg, arg) = dest_comb tm
  val (fupd, Kval) = dest_comb fupd_arg
  val newval = combinSyntax.dest_K_1 Kval
  val key = fupd |> dest_const |> fst
 in
  case lookup_opt key (#write_thms tstate) of
   SOME (base_thm, base_bit_thm, step_thm) =>
   if is_fcp_update newval then let
    (* TODO: Move *)
    val Eval_get_hol_prog = rand o rator
    val Eval_exp_get_pred_exp = rand o rand o rator

    val th = valOf base_bit_thm (* should be fine doing valOf here... *)
    val th = PART_MATCH (Eval_get_hol_prog o snd o dest_imp) th tm
    val (precond_eval, precond) = th |> concl |> dest_imp |> fst |> dest_conj
    val precond_eval_th = EVAL_PROVE precond_eval
    val precond_th = precond |> Eval_exp_get_pred_exp |> hol2hardware_exp tstate s s'
   in
    MATCH_MP th (CONJ precond_eval_th precond_th)
   end else if identical arg s' then let
    val newval' = hol2hardware_exp tstate s s' newval
   in
    MATCH_MP base_thm newval'
   end else let
    val newval' = hol2hardware_exp tstate s s' newval
    val arg' = hol2hardware' tstate s s' arg
   in
    MATCH_MP step_thm (CONJ newval' arg') |> EVAL_MP
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
