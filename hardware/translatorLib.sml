structure translatorLib =
struct

open preamble;

open arithmeticTheory bitstringTheory indexedListsTheory optionTheory wordsTheory wordsSyntax;
open dep_rewrite wordsLib;
open bitstringSyntax boolSyntax combinSyntax fcpSyntax numSyntax stringSyntax sumSyntax;

open sumExtraTheory verilogTheory verilogTypeTheory verilogMetaTheory translatorTheory ag32MachineTheory;
open ag32ConfigLib translatorCoreLib;
open verilogSyntax;

(** Various declarations **)

val env_tm = ``env : envT``;
(* fext must be named fext, simplifies  *)
val fext_tm = mk_var ("fext", fext_ty);

(** Syntax for translatorTheory **)

local val s = HolKernel.syntax_fns1 "translator" in
  val (state_var_tm, mk_state_var, dest_state_var, is_state_var) = s "state_var"
end;

local val s = HolKernel.syntax_fns3 "verilogType" in
  val (var_has_value_tm, mk_var_has_value, dest_var_has_value, is_var_has_value) = s "var_has_value"
  val (_, _, dest_var_has_type, _) = s "var_has_type"
  val (_, _, _, is_var_has_type_old) = s "var_has_type_old"
end;

(*
local val s = HolKernel.syntax_fns5 "translator" in
  val (Eval_tm, mk_Eval, dest_Eval, is_Eval) = s "Eval"
end;
*)

(** Implementation **)

(** Eval predicates **)

(* Just to make proofs less verbose ... *)

fun build_relS_var_thm ltm tm = let
  val var = tm |> rator |> rator |> rand |> fromHOLstring
  val th = mk_imp (ltm, tm) |> (flip o curry) prove (fs [relS_def])
                            |> PURE_REWRITE_RULE [relS_var_def] |> GEN_ALL
in
  (var, th)
end;

val relS_singles = relS_def
 |> SPEC_ALL |> concl |> dest_eq
 |> (fn (ltm, rtm) => map (build_relS_var_thm ltm) (strip_conj rtm))
 |> Redblackmap.fromList String.compare;

fun relSs var = Redblackmap.find (relS_singles, var);

(*``Eval fext s env P expression`` |> (RATOR_CONV o RAND_CONV) (ONCE_REWRITE_CONV [mk_thm ([], ``expression = ARB``)])*)

(*Eval_env_CONV *)
val Eval_exp_CONV = RATOR_CONV o RAND_CONV; (* maybe incorrect *)
(*Eval_pred_CONV *)

val Eval_get_pred_exp = rand o rand o rator;
val Eval_get_prog = rand;

val EvalS_get_prog = rand;
val EvalS_get_hol_prog = rand o rator;

(** Translator implementation **)

(** Error checking **)

val check_inv_fail = ref T;

fun check_inv_err name tm result tm2 = let
  in if tm2 = tm then result else let
    val _ = (check_inv_fail := tm)
    val _ = (show_types_verbosely := true)
    val _ = print ("\n\nTranslation failed at '" ^ name ^ "'\n\ntarget:\n\n")
    val _ = print_term tm
    val _ = print "\n\nbut derived:\n\n"
    val _ = print_term tm2
    val _ = print "\n\n\n"
    val _ = (show_types_verbosely := false)
    in failwith "check_inv" end end;

fun check_inv_Eval name tm result = let
  val tm2 = result |> concl |> rator |> rand |> rand
  in check_inv_err name tm result tm2 end;

fun check_inv_EvalS name tm result = let
  val tm2 = result |> concl |> rator |> rand
  in check_inv_err name tm result tm2 end;

fun prun_bassn_works_for var = let
  val accessor = lookup var accessors
  val ty = lookup var accessors |> type_of |> dom_rng |> snd
in
  if is_word_type ty then
    INST_TYPE [ alpha |-> dest_word_type ty ] prun_bassn_works_WORD
  else
    prun_bassn_works_BOOL
end;

fun get_prun_bassn_type_pred tm =
  let
    val ty = type_of tm
  in
    if is_type ty then let
      val (tname, tl) = dest_type ty
    in
      if tname = "bool" then
        prun_bassn_type_pred_BOOL
      else if tname = "fun" then let
        val (alpha', beta') = dom_rng ty
        val alpha' = dest_word_type alpha'
        val beta' = dest_word_type beta'
      in
        INST_TYPE [ alpha |-> alpha', beta |-> beta' ] prun_bassn_type_pred_WORD_ARRAY
      end else if is_word_type ty then
        INST_TYPE [ alpha |-> dest_word_type ty ] prun_bassn_type_pred_WORD
      else
        raise UnableToTranslateTy (ty, "no prun_bassn_type_pred for type")
    end
    else raise UnableToTranslateTy (ty, "just a type variable")
  end;

(** Eval thms and hol2hardware_exp **)

(* Note that we generate a too general type for words, so make sure to use e.g. ISPEC *)
fun get_var_thm ty =
  if is_bool_type ty then
    var_thm_BOOL
  else if is_word_type ty then
    var_thm_WORD
  else
    raise UnableToTranslateTy (ty, "no var_thm for type");

fun build_Eval_Var (name, accessf) = let
  val nameHOL = fromMLstring name
  val typepred = accessf |> dest_const |> snd |> dom_rng |> snd |> predicate_for_type_ty
in
  Q.prove(`!s. Eval fext s env (^typepred (^accessf s)) (Var ^nameHOL)`,
          rw [Eval_def, relSs name, erun_def, erun_get_var_def])
end;

val Eval_Vars = map (fn (name, accessf) => (accessf, build_Eval_Var (name, accessf))) accessors;

fun build_Eval_InputVar (name, accessf) = let
  val nameHOL = fromMLstring name
  val typepred = accessf |> dest_const |> snd |> dom_rng |> snd |> predicate_for_type_ty
in
  Q.prove(`!s. Eval fext s env (^typepred (^accessf fext)) (InputVar ^nameHOL)`,
          rw [Eval_def, relS_fextv_def, erun_def, erun_get_var_def, BOOL_def, WORD_def])
end;

val Eval_InputVars = map (fn (name, accessf) => (accessf, build_Eval_InputVar (name, accessf)))
                         fext_accessors;

(*val foo = Eval_InputVars |> hd |> snd |> Q.SPEC `s`*)

val Eval_T = SPEC ``T`` Eval_bool;
val Eval_F = SPEC ``F`` Eval_bool;

val builtin_binops = [
  Eval_BOOL_And, Eval_BOOL_Equal, Eval_BOOL_Or,

  Eval_WORD_And, Eval_WORD_Or, Eval_WORD_Xor,

  Eval_WORD_ShiftArithR, Eval_WORD_ShiftLogicalL, Eval_WORD_ShiftLogicalR,

  Eval_WORD_Minus, Eval_WORD_Plus, Eval_WORD_Times, Eval_WORD_Mod,

  Eval_WORD_Equal, Eval_WORD_LessThan, Eval_WORD_LowerThan,
  Eval_WORD_LessThanOrEqual, Eval_WORD_LowerThanOrEqual
  ]
  |> map (fn th => (th |> SPEC_ALL |> UNDISCH |> concl
                       |> Eval_get_pred_exp |> strip_comb |> fst, th));

fun dest_builtin_binop tm = let
  val (px, r) = dest_comb tm
  val (p, l) = dest_comb px
  val (x, th) = first (fn (x, _) => can (match_term x) p) builtin_binops
  val (ss, ii) = match_term x p
  val th = INST ss (INST_TYPE ii th)
  in (p, l, r, th) end handle HOL_ERR _ => failwith "Not a builtin operator";

(* TODO: Move? *)
fun EVAL_MP th = let
  val ant = th |> concl |> dest_imp |> fst |> EVAL_PROVE
in
  MP th ant
end;

(* Translator for pure expressions (exp) *)
fun hol2hardware_exp s tm =
  (* CASE: True *)
  if same_const tm T then
    SPEC s Eval_T

  (* CASE: False *)
  else if same_const tm F then
    SPEC s Eval_F

  (* CASE: Variable *)
  (* TODO: Add check that the name+type is not the same as state var? *)
  else if is_var tm then let
    val (vname, ty) = dest_var tm
    val th = get_var_thm ty
  in
    th |> ISPECL [s, tm, fromMLstring vname] |> UNDISCH
  end

  (* CASE: Binary operations *)
  else if can dest_builtin_binop tm then let
    val (p, x1, x2, lemma) = dest_builtin_binop tm
    val th1 = hol2hardware_exp s x1
    val th2 = hol2hardware_exp s x2
    val result = MATCH_MP lemma (CONJ th1 th2)
  in
    check_inv_Eval "binop" tm result
  end

  (* CASE: Neg? *)
  else if is_neg tm then let
    val arg = dest_neg tm
  in
    (* Special case for ArrayNotEqual *)
    if is_eq arg then let
      val (argl, argr) = dest_eq arg
      val thl = hol2hardware_exp s argl
      val thr = hol2hardware_exp s argr
      (* TODO: Somewhat hacky: *)
      val eval_thm = if (type_of argl) = bool then Eval_BOOL_NotEqual else Eval_WORD_NotEqual
      val result = MATCH_MP eval_thm (CONJ thl thr)
    in
      check_inv_Eval "neg" tm result
    end else let
      val th = hol2hardware_exp s arg
    in
      MATCH_MP Eval_neg th
    end
  end

  (* CASE: Inline if *)
  else if is_cond tm then let
    val (cond, lbranch, rbranch) = dest_cond tm
    val preconds = map (hol2hardware_exp s) [cond, lbranch, rbranch]
  in
    MATCH_MP Eval_InlineIf (LIST_CONJ preconds)
  end

  (* CASE: Word constant, e.g. 22w *)
  (* TODO: Do we need to evaluate this down to bits? *)
  else if is_n2w tm andalso is_numeral (rand tm) then let
    val dim = dim_of tm in
    SPECL [s, rand tm] (INST_TYPE [alpha |-> dim] Eval_word_const) end

  (* CASE: word_bit *)
  (* NOTE: This only translates array indexing, as this is what's needed for Ag32 *)
  (* TODO: Could add better error message for when indexing outside the array (EVAL will just fail currently) *)
  else if is_word_bit tm then let
    val (i, var) = dest_word_bit tm
    val precond = hol2hardware_exp s var
    val ret = MATCH_MP Eval_word_bit precond
    val ret = SPEC i ret
    val precond = ret |> concl |> dest_imp |> fst |> EVAL_PROVE
  in
    MATCH_MP ret precond
  end

  (* CASE: word_extract *)
  else if is_word_extract tm then let
    val (high, low, arg, size) = dest_word_extract tm
    val precond = hol2hardware_exp s arg
    val ret = MATCH_MP Eval_word_extract precond
    val ret = ret |> ISPECL [high, low] |> INST_TYPE [ beta |-> size ]
    val precond = ret |> concl |> dest_imp |> fst |> EVAL_PROVE
    val ret = MP ret precond
  in
    ret
  end

  (* CASE: zero extend? *)
  else if is_w2w tm then let
    val (arg, out_dim) = dest_w2w tm
    (*val in_dim = dim_of arg
    val precond = mk_less (mk_dimindex in_dim, mk_dimindex out_dim) |> EVAL_PROVE*)
    val arg' = hol2hardware_exp s arg
  in
    arg' |> MATCH_MP Eval_w2w |> INST_TYPE [ beta |-> out_dim ] |> (CONV_RULE o RAND_CONV o RAND_CONV) EVAL
  end

  (* CASE: zero extend? (Almost identical to w2w.) *)
  else if is_sw2sw tm then let
    val (arg, out_dim) = dest_sw2sw tm
    val in_dim = dim_of arg
    val precond = mk_leq (mk_dimindex in_dim, mk_dimindex out_dim) |> EVAL_PROVE
    val arg' = hol2hardware_exp s arg
  in
    MATCH_MP Eval_sw2sw (CONJ precond arg')
  end

  else if is_v2w tm then let
    val (arg, out_dim) = dest_v2w tm
    val precond = mk_less (term_of_int 1, mk_dimindex out_dim) |> EVAL_PROVE
    val (arg, _) = listSyntax.dest_cons arg
    val arg' = hol2hardware_exp s arg
    val result = MATCH_MP Eval_v2w (CONJ precond arg')
  in
    check_inv_Eval "v2w" tm result
  end

  else if is_word_concat tm then let
    val (tml, tmr) = dest_word_concat tm
    val evall = hol2hardware_exp s tml
    val evalr = hol2hardware_exp s tmr
    val result = MATCH_MP Eval_word_concat (CONJ evall evalr)
    (* TODO: Could add length check here ... *)
    val gammasum = Arbnum.+ (tml |> size_of, tmr |> size_of) |> mk_numeric_type
    val result = INST_TYPE [ gamma |-> gammasum ] result
    val result = EVAL_MP result
  in
    check_inv_Eval "word_concat" tm result
  end

  (* CASE: Other compound expression, e.g. state projection ("state var")? *)
  else if is_comb tm then let
    val (f, arg) = dest_comb tm
  in
    (* SUBCASE: State selector? *)
    if arg = s then
      case lookup_same f Eval_Vars of
          SOME result => SPEC s result
        | NONE => raise UnableToTranslate (tm, "Unknown state projection")

    (* SUBCASE: External read? *)
    else if arg = fext_tm then
      case lookup_same f Eval_InputVars of
          SOME result => SPEC s result
        | NONE => raise UnableToTranslate (tm, "Unknown fext projection")

    (* SUBCASE: Array indexing? Just assume it is for now... TODO *)
    else let
      val f' = hol2hardware_exp s f
      val arg' = hol2hardware_exp s arg
    in
      MATCH_MP Eval_WORD_ARRAY_indexing (CONJ f' arg')
    end

    (*else
      raise UnableToTranslate (tm, "Unknown comb case, not state projection")*)
  end

  else raise UnableToTranslate (tm, "Unknown case");

(*
Testing:
val tm = ``(3 >< 1) s.instruction * ((2 >< 0) s.instruction):word3``;
val tm = ``s.PC - fext.data_rdata + r + Tr``;
val tm = ``(3 >< 1) fext.data_rdata + r + Tr``;
val tm = ``(5w:10 word) @@ (b:15 word)``

val s = ``s:state_circuit``;

hol2hardware_exp s tm
*)

(** EvalS thms and hol2hardware_body **)

(* Assignments *)

(* TODO: Can probably derive these from the step thms, just use program = Skip! *)

fun build_update_base_stmt field fupd pred =
  let
    val field_str = fromMLstring field
  in
   ``!s env w exp.
      Eval fext s env (^pred w) exp ==>
      EvalS fext s env (^fupd (K w) s) (BlockingAssign (Var ^field_str) exp)``
  end;

fun update_base_tac field =
 rw [Eval_def, EvalS_def, prun_def] \\ drule_first \\ drule_strip (relSs field) \\

 imp_res_tac same_shape_BOOL \\
 imp_res_tac same_shape_WORD \\
 imp_res_tac same_shape_WORD_ARRAY \\

 simp [sum_bind_def, prun_bassn_def, assn_def, sum_for_def, sum_map_def] \\
 fs [relS_def, relS_var_def, get_var_cleanup];

fun build_slice_update_base_stmt field fupd facc =
  let
    val field_str = fromMLstring field
  in
   ``!s env (w:'a word) exp hb lb.
      Eval fext s env (WORD w) exp ==>
      EvalS fext s env (^fupd (K (bit_field_insert hb lb w (^facc s))) s)
                       (BlockingAssign (ArraySlice (Var ^field_str) [] hb lb) exp)``
  end;

(* TODO: *)
val slice_update_base_tac = cheat;

val update_base_thms =
 zip updates accessors
 |> map (fn ((field, fupd), (_, facc)) =>
            let
              val pred = fupd |> type_of |> dom_rng |> fst |> dom_rng |> fst |> predicate_for_type_ty
              val base_thm = [prove (build_update_base_stmt field fupd pred,
                                     update_base_tac field)]
              val slice_thm = if same_const pred WORD_tm
                              then [prove (build_slice_update_base_stmt field fupd facc,
                                           slice_update_base_tac)]
                              else []
            in (fupd, append slice_thm base_thm) end);

(* Need special thms for WORD_ARRAY updates, because we have += on the rhs *)

(* Add base update thms of special form, simply assume that other form not used *)

fun build_WORD_ARRAY_update_base_stmt vname projf updatef = let
  val vnameHOL = fromMLstring vname
in
  ``!s env i ie v ve.
     Eval fext s env (WORD i) ie /\
     Eval fext s env (WORD v) ve ==>
     EvalS fext s env (^updatef (K ((i =+ v) (^projf s))) s)
                      (BlockingAssign (ArrayIndex (Var ^vnameHOL) [ie]) ve)``
end;

fun WORD_ARRAY_update_base_tac name =
 rw [Eval_def, EvalS_def, prun_def] \\
 drule_first \\ drule_first \\
 simp [sum_bind_def, prun_def] \\
 drule_strip (relSs name) \\ Cases_on `v'` >- fs [WORD_ARRAY_def] \\
 imp_res_tac WORD_ver2n \\
 drule_strip prun_bassn_correct \\
 asm_exists_tac \\ fs [relS_def, relS_var_def, WORD_ARRAY_def, WORD_def] \\
 rw [combinTheory.UPDATE_def];

fun build_WORD_ARRAY_slice_update_base_stmt vname projf updatef = let
  val vnameHOL = fromMLstring vname
in
  ``!s env i ie v ve hb lb.
     Eval fext s env (WORD i) ie /\
     Eval fext s env (WORD v) ve ==>
     EvalS fext s env (^updatef (K ((i =+ bit_field_insert hb lb v (^projf s i)) (^projf s))) s)
                      (BlockingAssign (ArraySlice (Var ^vnameHOL) [ie] hb lb) ve)``
end;

fun WORD_ARRAY_slice_update_base_tac name = cheat;

(* Note that we do not have step thms for WORD_ARRAYs *)
val WORD_ARRAY_update_base_thms =
 zip updates accessors
 |> filter (fn (_, (_, facc)) => (facc |> type_of |> dom_rng |> snd |> dest_type |> fst) = "fun")
 |> map (fn ((name, updf), (_, projf)) =>
         (updf,
          [prove (build_WORD_ARRAY_slice_update_base_stmt name projf updf,
                  WORD_ARRAY_slice_update_base_tac name),
           prove (build_WORD_ARRAY_update_base_stmt name projf updf,
                  WORD_ARRAY_update_base_tac name)]));

(* A note about the order of writing to fields:

  The internal representation in HOL of nested writes are not in the same order
  as visualized, at least not in the visualization is interpreted as something
  "executing" from left to right:

  <| PC := 5w; PC := 2w |>.PC = 5w

  Left to right sequential execution is the obvious Verilog program to translate this to,
  but the writes will be in opposite order than visualized.

  I tried switching the order of fields in the translation, but ran into troubles, :(.

  TODO: Could switch order inside HOL, using some CONV, before translating? *)

fun build_update_step_stmt var fupd = let
 val var_str = fromMLstring var
 val pred = fupd |> type_of |> dom_rng |> fst |> dom_rng |> fst |> predicate_for_type_ty
in
 ``!s f fv env w exp.
    Eval fext s env (^pred w) exp /\
    EvalS fext s env f fv ==>
    EVERY (\var. ~MEM var (vwrites fv)) (evreads exp) ==>
    EvalS fext s env (^fupd (K w) f) (Seq fv (BlockingAssign (Var ^var_str) exp))``
end;

fun update_step_tac var =
 rw [EVERY_MEM, Eval_def, EvalS_def, prun_def] \\
 drule_first \\ drule_first \\ simp [sum_bind_def] \\
 qspecl_then [`fextv`, `ver_s'`, `exp`, `ver_s with vars := env`] mp_tac erun_cong \\
 impl_tac >- (drule_strip prun_same_after \\ simp []) \\ rw [sum_bind_def] \\
 drule_strip (prun_bassn_works_for var) \\
 drule_strip (relSs var) \\
 rpt (disch_then drule) \\
 simp [] \\ fs [relS_def, relS_var_def, get_var_set_var];

val update_step_thms =
 zip updates accessors
 |> filter (fn (_, (_, facc)) => (facc |> type_of |> dom_rng |> snd |> dest_type |> fst) <> "fun")
 |> map (fn ((field, fupd), _) => (fupd, prove (build_update_step_stmt field fupd,
                                                update_step_tac field)));

(* E.g., s with PC := 0w is a update.
   We know that everything is in this list, but these are not always the thm we want to use! *)
fun is_update tm =
  let
    val update = tm |> rator |> rator
  in
    lookup_same update update_base_thms |> isSome
  end;

fun inst_EvalS_env s v th = let
(*  val () = (print "\n"; print_term v; print "\n"; print_thm th; thm_fail := th)*)
  val name = v |> dest_var |> fst
  val namet = fromMLstring name
  val vinv = predicate_for_type v
  val assum = mk_var_has_value (env_tm, namet, mk_comb(vinv, v))
  (*val var_has_type_cleanup = assum |> PART_MATCH (fst o dest_imp) var_has_value_imp_var_has_type |> UNDISCH*)
  (* TODO: Should generate fresh variable here, but did not find any good API for this... *)
  val forallv = mk_var ("v", value_ty)
  val new_env = listSyntax.mk_cons (pairSyntax.mk_pair (namet, forallv), env_tm)
(*  val () = th |> DISCH assum |> print_thm *)
(*  val Eval_env_CONS' = SPEC namet Eval_env_CONS
  val comp = Eval_env_CONS' |> SPEC_ALL |> concl |> dest_imp |> fst |> EVAL_PROVE
  val Eval_env_CONS' = MATCH_MP Eval_env_CONS' comp
  val has_type_env_CONS_WORD' = MATCH_MP has_type_env_CONS_WORD comp*)

  (* This is relevant if we have nested lets using the same variable name ... *)
  (*val th = th |> DISCH (var_has_type_cleanup |> concl)
                |> flip MP var_has_type_cleanup*)

  (* Actual lifting *)
  val th = th |> DISCH assum
              |> INST [env_tm |-> new_env]
              |> ASM_CONV_RULE (PURE_ONCE_REWRITE_CONV [var_has_value_env_new_var,
                                                        var_has_type_env_new_var]
                                THENC (DEPTH_CONV stringLib.string_EQ_CONV)
                                THENC REWRITE_CONV [])
(*  val () = print_thm th*)
  val (new_assum, th) = UNDISCH_TM th
  val th = th |> CONV_RULE (Eval_exp_CONV (UNBETA_CONV v))
              |> DISCH new_assum
              |> GEN forallv
in
  th
end;

(* newstateprog is a vprog, often a sequence of state updates (but not always) *)
(* val (th, inners, newstateprog) = (body', v, arg'_prog) *)
fun trans_to_state_body_form th inners newstateprog =
  th |> CONV_RULE (Eval_exp_CONV (UNBETA_CONV inners))
     |> DISCH_ALL
     |> Q.INST [`env` |-> `env'`]
     |> Q.DISCH (`relS_fextv fextv fext /\ prun fextv (vs with vars := env) ^newstateprog = INR vs'`)
     |> Q.INST [`env'` |-> `vs'.vars`];

fun get_var_bubble_thm th = let
  val precond = th |> concl |> dest_imp |> snd
in
  if is_imp precond then let
    val precond = precond |> dest_imp |> fst
  in
    if is_var_has_value precond then
      SOME bubble_var_has_value
    else if is_var_has_type_old precond then
      SOME bubble_var_has_type
    else
      raise UnableToTranslate (th |> concl, "Unknown precondition")
  end
  else
    NONE
end;

fun bubble_var th bubble_thm = let
  val res = MATCH_MP bubble_thm th
  val precond = res |> concl |> dest_imp |> fst |> EVAL_PROVE
  val res = MATCH_MP res precond
in
  UNDISCH res
end;

(* val th = trans_to_state_body_form body' v arg'_prog *)
(* val SOME bubble_thm = get_var_bubble_thm th *)
fun bubble_vars th =
  case get_var_bubble_thm th of
      SOME bubble_thm => bubble_vars (bubble_var th bubble_thm)
    | NONE => th;

datatype case_body_itr_type = FullMatch | CatchAllMatch

fun first_PART_MATCH proj ths tm =
  case ths of
      nil => failwith "No match in list"
    | th::ths => PART_MATCH proj th tm
                 handle HOL_ERR _ => first_PART_MATCH proj ths tm;


(* For debugging: val tm = (!tm_trace) |> hd *)
(* val s = ``s:state_circuit`` *)
val tm_trace = ref ([]:term list);

(* This is just a wrapper function with tracing, calling hol2hardware_body_impl *)
fun hol2hardware_trace s tm = let
  val () = tm_trace := []
in
  hol2hardware_body s tm
end

and hol2hardware_body s tm = let
  val () = (print "\nhol2hardware_body call: ";
            print_term tm;
            print "\n";
            tm_trace := tm :: !tm_trace)
  val ret = hol2hardware_body_impl s tm
  val () = tm_trace := tl (!tm_trace) (* <-- will only run if above call succeeded *)
in
  ret
end

and hol2hardware_body_impl s tm =
  (* CASE: Case on word type *)
  if is_literal_case tm then let
    val result = hol2hardware_case_body s tm
  in
    check_inv_EvalS "case" tm result
  end

  (* CASE: Do nothing *)
  (* TODO: Is this what we want? Probably? *)
  else if is_var tm then
    if tm = s then
      SPEC s EvalS_Skip
    else
      raise UnableToTranslate (tm, "Unknown state var")

  (* CASE: State variable update *)
  else if is_update tm then let
    val (fupd_arg, arg) = dest_comb tm
    val (fupd, Kval) = dest_comb fupd_arg
    val (Kfun, newval) = dest_comb Kval
  in
    (* val SOME base_thms = lookup_same fupd WORD_ARRAY_update_base_thms *)
    case lookup_same fupd WORD_ARRAY_update_base_thms of
        (* TODO: assumes everything is base here... also assumes structure... probably ok for Ag32 *)
        (* TODO: do we check that we are using the correct state variable here? no? *)
        SOME base_thms =>
        let
          val th = first_PART_MATCH (EvalS_get_hol_prog o snd o dest_imp) base_thms tm
          val precond = th |> concl |> dest_imp |> fst |> strip_conj
                           |> map (hol2hardware_exp s o Eval_get_pred_exp)
                           |> LIST_CONJ
        in
          MATCH_MP th precond
        end

      | NONE =>
        if arg = s then
          case lookup_same fupd update_base_thms of
              SOME base_thms =>
              let
                val th = first_PART_MATCH (EvalS_get_hol_prog o snd o dest_imp) base_thms tm
                val precond = th |> concl |> dest_imp |> fst |> Eval_get_pred_exp |> hol2hardware_exp s
              in
                MATCH_MP th precond
              end
            | NONE => failwith "Impossible: Missing base update thm?"
        else
          case lookup_same fupd update_step_thms of
              SOME step_thm =>
              let
                val newval_thm = hol2hardware_exp s newval
                val nest = hol2hardware_body s arg
                val ret = MATCH_MP step_thm (LIST_CONJ [newval_thm, nest])
                val comp = ret |> concl |> dest_imp |> fst
              in
                MP ret (EVAL_PROVE comp)
              end
            | NONE => failwith "Impossible: Missing step update thm?"
  end

  (* CASE: Let, both state update and new local variable *)
  else if is_let tm then let
    val (body, arg) = dest_let tm
    val (v, body) = dest_abs body
    val vname = v |> dest_var |> fst |> fromMLstring
  in
    (* state update or just new local variable? *)
    if type_of arg = state_ty then let
      val arg' = hol2hardware_body s arg
      val body' = hol2hardware_body v body
      val arg'_prog = arg' |> concl |> EvalS_get_prog
      val body' = trans_to_state_body_form body' v arg'_prog |> bubble_vars
      val body' = body' |> Q.GENL [`vs`, `vs'`, `fextv`] |> GEN v
      (* TODO: Why do we need HO_ here? Fails without, "captures bound variable".
               Might interact with other bugs? *)
      (*val () = (thm1_fail := arg'; thm2_fail := body')*)
      val result = HO_MATCH_MP EvalS_EvalS (CONJ arg' body')
    in check_inv_EvalS "let_state" tm result end
    else let
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
    in check_inv_EvalS "let_var" tm result end
  end

  (* CASE: If statement *)
  else if is_cond tm then let
    val (cond, tbranch, fbranch) = dest_cond tm
    val c' = hol2hardware_exp s cond
    val tbranch' = hol2hardware_body s tbranch
    val fbranch' = hol2hardware_body s fbranch
  in
    MATCH_MP EvalS_If (LIST_CONJ [c', tbranch', fbranch'])
  end

  else
    raise UnableToTranslate (tm, "Unknown case")

and hol2hardware_case_body s tm = let
    val (body, v) = dest_literal_case tm
    (* TODO: Should work as no other variable should be called v in body? *)
    val (v_inner, body) = dest_abs body
    val body = subst [ v_inner |-> v ] body
    val v_Eval = hol2hardware_exp s v
    val (itr_type, result) = hol2hardware_case_body_itr s v_Eval body
    val result = case itr_type of
                     FullMatch => MATCH_MP result (ISPEC v word_ls_0) (* TODO: Unify instead? *)
                   | CatchAllMatch => result
in
  result |> (CONV_RULE o Eval_exp_CONV) (UNBETA_CONV v THENC
                                         RATOR_CONV (ALPHA_CONV v_inner) THENC
                                         REWR_CONV (GSYM literal_case_THM))
end

(* v_Eval is a micro-optimization so we do not have to re-translate the condition variable each time *)
and hol2hardware_case_body_itr s v_Eval tm = let
  val (cond, tb, fb) = dest_cond tm
  val (condl, condr) = dest_eq cond
  val ft_Eval = hol2hardware_body s tb
in
  (* TODO: might have to look deeper than this, because default case might start with an unrelated if stmt *)
  if is_cond fb then let (* step base *)
    val (itr_type, fb_Eval) = hol2hardware_case_body_itr s v_Eval fb
  in
    case itr_type of
        FullMatch =>
        let
          val oldbound = fb_Eval |> concl |> dest_imp |> fst |> rator |> rand
          val newbound = condr
          val precond = mk_eq (oldbound,
                               mk_word_add(newbound, mk_word (Arbnumcore.one, size_of newbound)))
          val bound_match = precond |> EVAL
        in
          if same_const (bound_match |> concl |> rhs) T then
            (FullMatch, MATCH_MP EvalS_Case_ARB_new_case
                                 (LIST_CONJ [EQT_ELIM bound_match, v_Eval, fb_Eval, ft_Eval]))
          else
            raise UnableToTranslate (tm, "Bounds do not match...")
        end
      | CatchAllMatch =>
        let
          val result = MATCH_MP EvalS_Case_catch_all_new_case
                                (LIST_CONJ [v_Eval, fb_Eval, ft_Eval])
          val result = ISPEC condr result
        in
          (CatchAllMatch, result)
        end
  end
  else (* base cases *) let
    val word_t = mk_word_T (dim_of condl)
    val word_t_val = word_t |> EVAL |> SYM
    val is_max = mk_eq (condr, word_t) |> EVAL |> concl |> rhs
  in
    if same_const is_max T then
      (FullMatch, MATCH_MP EvalS_Case_ARB (LIST_CONJ [word_t_val, v_Eval, ft_Eval]))
    else if same_const is_max F then (* <-- assume the case ends with a match all *)
      if fb = s then let
        val result = MATCH_MP EvalS_Case_catch_all_NONE (LIST_CONJ [v_Eval, ft_Eval])
        val result = ISPEC condr result
      in
        (CatchAllMatch, result)
      end else let
        val fb_Eval = hol2hardware_body s fb
        val result = MATCH_MP EvalS_Case_catch_all_SOME (LIST_CONJ [v_Eval, ft_Eval, fb_Eval])
        val result = ISPEC condr result
      in
        (CatchAllMatch, result)
      end
    else
      raise UnableToTranslate (tm, "Failed to evaluate bound, something is wrong")
  end
end;

(*
Testing:

val tm = ``s with PC := 5w``;
val tm = ``let t = 10w; r = T in s with <| PC := 5w + t + fext.data_rdata;
                                           ALU_res := s.acc_arg;
                                           acc_arg_ready := r |>``;
val tm = ``let s' = s with PC := 5w in s' with ALU_res := s.PC``;

val res = hol2hardware_body s tm;
*)

(* Translates a step function to hardware ... assumes thms of form: !s. [...] OR !fext s. [...] *)
fun hol2hardware_step_function th = let
  val (vars, funth) = th |> concl |> strip_forall
  val s = case length vars of
              1 => (* s *) vars |> hd
            | 2 => (* fext s *) vars |> tl |> hd
            | _ => failwith "Unknown form"
  val ret = hol2hardware_trace s (rhs funth)
in
  (* TODO: No error handling here if no match... *)
  REWRITE_RULE [GSYM th] ret
end;

(* TODO: WORD_ARRAY *)
fun vars_has_type_cleanup th = let
  val th = th
   |> DISCH_ALL
   (* Might do too much: *)
   |> SIMP_RULE (srw_ss()) [var_has_type_old_var_has_type_BOOL, var_has_type_old_var_has_type_WORD]
   |> UNDISCH_ALL
  val newhyp = th
   |> hyp
   |> map ((fn (_, var, ty) => pairSyntax.mk_pair (var, ty)) o dest_var_has_type)
   |> flip (curry listSyntax.mk_list) ``:string # vertype``
   |> (fn tm => ``vars_has_type env ^tm``)
in
 prove (mk_imp (newhyp, th |> concl), simp [vars_has_type_def, DISCH_ALL th]) |> UNDISCH_ALL
end;

(*
Testing:

vars_has_type_cleanup res

*)

(* Top-level function, translator for state functions *)

(*
fun hol2hardware tm =
    let
      val (s, f) = dest_abs tm
    in
      hol2hardware_body s f (* TODO: Add GEN here? *)
    end;

(* Rebuilds named function to anonymous function, and apply hol2hardware *)
fun hol2hardware_named thm =
  let
    val (s, def_eq) = thm |> concl |> dest_forall
    val def = mk_abs (s, (rhs def_eq))
  in
    hol2hardware def
  end;
*)

end
