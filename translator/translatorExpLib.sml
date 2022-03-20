structure translatorExpLib =
struct

open hardwarePreamble;

open stringSyntax bitstringSyntax;
open sumExtraTheory;
open verilogTheory verilogMetaTheory verilogTypeTheory;

open translatorTheory;
open translatorCoreLib;

(* Needed for proving tstate stuff: *)
open sumExtraTheory verilogMetaTheory;

(*val check_inv_fail = ref T;*)

fun check_inv_err name tm result tm2 = let
  in if identical tm2 tm then result else let
    (*val _ = (check_inv_fail := tm)*)
    (*val _ = (show_types_verbosely := true)*)
    val _ = print ("\n\nTranslation failed at '" ^ name ^ "'\n\ntarget:\n\n")
    val _ = print_term tm
    val _ = print "\n\nbut derived:\n\n"
    val _ = print_term tm2
    val _ = print "\n\n\n"
    (*val _ = (show_types_verbosely := false)*)
    in failwith "check_inv" end end;

fun check_inv_Eval_exp name tm result = let
  val tm2 = result |> concl |> rator |> rand |> rand
  in check_inv_err name tm result tm2 end;

fun check_inv_Eval name tm result = let
  val tm2 = result |> concl |> rator |> rand
  in check_inv_err name tm result tm2 end;

val Eval_exp_exp = rand o rator;

val builtin_binops = [
  Eval_exp_BOOL_And, Eval_exp_BOOL_Or, Eval_exp_BOOL_Equal,

  Eval_exp_WORD_And, Eval_exp_WORD_Or, Eval_exp_WORD_Xor,

  Eval_exp_WORD_ShiftArithR, Eval_exp_WORD_ShiftLogicalL, Eval_exp_WORD_ShiftLogicalR,

  Eval_exp_WORD_Minus, Eval_exp_WORD_Plus, Eval_exp_WORD_Times,

  Eval_exp_WORD_Equal, Eval_exp_WORD_LessThan, Eval_exp_WORD_LowerThan,
  Eval_exp_WORD_LessThanOrEqual, Eval_exp_WORD_LowerThanOrEqual]
  |> map (fn th => (th |> SPEC_ALL |> UNDISCH |> concl
                       |> Eval_exp_exp |> rand |> strip_comb |> fst, th));

fun dest_builtin_binop tm = let
  val (px, r) = dest_comb tm
  val (p, l) = dest_comb px
  val (x, th) = first (fn (x, _) => can (match_term x) p) builtin_binops
  val (ss, ii) = match_term x p
  val th = INST ss (INST_TYPE ii th)
  in (p, l, r, th) end handle HOL_ERR _ => failwith "Not a builtin operator";

(** Tstate **)

type tstate = { fext_ty : hol_type,
                fext_rel : term,
                state_ty : hol_type,
                rel : term,
                is_rel_var : term,
                rel_var_inv : thm,
                module_rel : term,
                comms : string list,
                read_thms : (term * thm) list,
                write_thms : (string list * (thm * thm option * thm option)) list,
                write_2d_thms : (string list * (thm * thm)) list,
                fext_read_thms : (term * thm) list,
                module_rel_rel : thm,
                rel_module_rel : thm };

fun build_Eval_exp_var fext_rel_const rel_const rel comms (name, accessf, ty) = let
  val nameHOL = fromMLstring name
  val typepred = predicate_for_type ty
  val th =
   if mem name comms then
    Q.prove(`!s s'. Eval_exp ^fext_rel_const ^rel_const fext s s' env (^typepred (^accessf s)) (Var ^nameHOL)`,
             rw [Eval_exp_def, erun_def, erun_get_var_def, rel, state_rel_cvar_def])
   else
    Q.prove(`!s s'. Eval_exp ^fext_rel_const ^rel_const fext s s' env (^typepred (^accessf s')) (Var ^nameHOL)`,
            rw [Eval_exp_def, erun_def, erun_get_var_def, rel, state_rel_var_def])
 in
  CONV_RULE (TRY_CONV (STRIP_QUANT_CONV (RATOR_CONV (RAND_CONV (RAND_CONV BETA_CONV))))) th
 end;

fun build_update_stmts comms fext_rel rel field fupd facc ty = let
 val fieldHOL = fromMLstring field
 val pred = predicate_for_type ty
 val assn = if mem field comms then NonBlockingAssign_tm else BlockingAssign_tm
in
 (``!s s' w exp.
     Eval_exp ^fext_rel ^rel fext s s' env (^pred w) exp ==>
     Eval ^fext_rel ^rel fext s s' env (^fupd s' w) (^assn (NoIndexing ^fieldHOL) (SOME exp))``,
  (if is_word_type ty then
    ``!s s' i env w exp.
       i < dimindex(:'a) /\
       Eval_exp ^fext_rel ^rel fext s s' env (BOOL w) exp ==>
       Eval ^fext_rel ^rel fext s s' env (^fupd s' ((i :+ w) (^facc s')))
                                         (^assn (Indexing ^fieldHOL 0 (Const (n2ver i))) (SOME exp))``
   |> inst [ alpha |-> dest_word_type ty ]
   |> SOME
  else
   NONE),
  (if is_word_type ty then let
    val beta_size = dest_word_type ty
   in
   ``!s env (w:'a word) exp hb lb.
      (dimindex(:'a) = hb + 1 - lb /\ lb <= hb /\ hb < dimindex(:'b)) /\
      Eval_exp ^fext_rel ^rel fext s s' env (WORD w) exp ==>
      Eval ^fext_rel ^rel fext s s' env (^fupd s' (bit_field_insert hb lb w (^facc s')))
                                        (^assn (SliceIndexing ^fieldHOL [] hb lb) (SOME exp))``
   |> inst [ beta |-> beta_size ]
   |> SOME
  end else
   NONE))
end;

fun update_base_tac rel =
 rw [EVERY_MEM, Eval_exp_def, Eval_def, prun_def] \\
 rpt drule_first \\
 simp [sum_bind_def, sum_for_def, sum_map_def,
       prun_assn_rhs_def, prun_bassn_def, prun_nbassn_def, assn_def] \\
 fs [rel, state_rel_var_def, state_rel_cvar_def,
     get_var_cleanup, get_cvar_rel_set_var_neq, get_cvar_rel_set_nbq_var];

fun update_base_bit_tac rel =
 rw [Eval_exp_def, Eval_def, prun_def] \\
 drule_first \\
 fs [rel, state_rel_var_def, state_rel_cvar_def, WORD_def, BOOL_def] \\ rveq \\
 simp [sum_bind_def, sum_map_def, sum_for_def, prun_assn_rhs_def, prun_bassn_def, prun_nbassn_def, assn_def,
       erun_def, ver2n_n2ver, GSYM get_cvar_rel_get_use_nbq_var, get_use_nbq_var_F,
       w2ver_def, v2ver_def, get_VArray_data_def, get_VBool_data_def] \\
 dep_rewrite.DEP_REWRITE_TAC [prun_set_var_index_ok_idx] \\ simp [bitstringTheory.length_w2v, sum_map_def] \\
 simp [get_var_cleanup, get_cvar_rel_set_var_neq, get_cvar_rel_set_nbq_var, w2ver_def, v2ver_def] \\
 simp [GSYM revLUPDATE_MAP, revLUPDATE_fcp_update];

fun prove_update_thms fext_rel_const rel rel_const comms (field, field_data:allfieldinfo) = let
 val fupd = #fupd field_data
 val facc = #accessor field_data
 val key = #fupd_key field_data (*fupd |> dest_const |> fst*)
 val (base_stmt, base_bit_stmt, base_slice_stmt) =
     build_update_stmts comms fext_rel_const rel_const field fupd facc (#ty field_data)

 val base_thm = prove (base_stmt, update_base_tac rel)
 val base_thm = CONV_RULE (DEPTH_CONV BETA_CONV) base_thm

 val base_slice_thm = Option.map (fn tm => prove (tm, cheat (*update_base_slice_tac rel*))) base_slice_stmt
 val base_slice_thm = Option.map (fn th => CONV_RULE (DEPTH_CONV BETA_CONV) th) base_slice_thm

 val base_bit_thm = Option.map (fn tm => prove (tm, update_base_bit_tac rel)) base_bit_stmt
 val base_bit_thm = Option.map (fn th => CONV_RULE (DEPTH_CONV BETA_CONV) th) base_bit_thm
in
 (key, (base_thm, base_bit_thm, base_slice_thm))
end;

fun build_update_stmts_2d comms fext_rel_const rel_const field fupd facc = let
 val fieldHOL = fromMLstring field
 val ty = fupd |> type_of |> dom_rng |> fst |> dom_rng |> fst
 val state_ty = fupd |> type_of |> dom_rng |> snd |> dom_rng |> fst
 val pred = predicate_for_type ty
 val (prev_s, assn) = if mem field comms then
                       (mk_var ("s", state_ty), NonBlockingAssign_tm)
                      else
                       (mk_var ("s'", state_ty), BlockingAssign_tm)

 val el_size = facc |> type_of |> dom_rng |> snd |> dom_rng |> snd |> dest_word_type
in
 (``!s s' i ie v ve.
    T /\
    (Eval_exp ^fext_rel_const ^rel_const fext s s' env (WORD i) ie /\
    Eval_exp ^fext_rel_const ^rel_const fext s s' env (WORD v) ve) ==>
    Eval ^fext_rel_const ^rel_const fext s s' env (^fupd (K ((i =+ v) (^facc ^prev_s))) s')
                                                  (^assn (Indexing ^fieldHOL 0 ie) (SOME ve))``,
  ``!s s' i ie (v:'a word) ve hb lb.
     (dimindex(:'a) = hb + 1 − lb /\ lb <= hb /\ hb < dimindex(:'b)) /\
     (Eval_exp ^fext_rel_const ^rel_const fext s s' env (WORD i) ie /\
      Eval_exp ^fext_rel_const ^rel_const fext s s' env (WORD v) ve) ==>
     Eval ^fext_rel_const ^rel_const fext s s' env
          (^fupd (K ((i =+ bit_field_insert hb lb v (^facc ^prev_s i)) (^facc ^prev_s))) s')
          (^assn (SliceIndexing ^fieldHOL [ie] hb lb) (SOME ve))``
 |> inst [ beta |-> el_size ])
end;

fun state_rel_field rel field = let
 fun subterm tm1 tm2 = can (find_term (can (match_term tm1))) tm2
    
 val fieldHOL = fromMLstring field
 val (imp_lhs, conjs) = rel |> concl |> strip_forall |> snd |> dest_eq
 val conjs = strip_conj conjs
 val i = index (subterm fieldHOL) conjs
 val thm = mk_imp (imp_lhs, el (i+1) conjs)
in
 thm |> simpLib.SIMP_PROVE (srw_ss()) [rel] |> GEN_ALL
end;

(* Inefficient! *)
fun update_base_2d_tac rel field =
 rw [Eval_def, Eval_exp_def, prun_def] \\
 drule_first \\ drule_first \\ drule_strip (state_rel_field rel field) \\
 fs [state_rel_var_def, WORD_def, WORD_ARRAY_cases] \\ fs [sum_revEL_INR] \\
 simp [prun_assn_rhs_def, prun_bassn_def, assn_def, prun_set_var_index_ok_idx,
       ver2n_w2ver, get_use_nbq_var_def, get_VArray_data_def,
       sum_for_def, sum_map_def, sum_bind_def] \\
 fs [rel, state_rel_var_def, state_rel_cvar_def, get_cvar_rel_set_var_neq, get_var_cleanup] \\
 fs [WORD_ARRAY_def, WORD_def, combinTheory.UPDATE_def] \\ gen_tac \\
 dep_rewrite.DEP_REWRITE_TAC [sum_revEL_revEL] \\
 dep_rewrite.DEP_REWRITE_TAC [revEL_revLUPDATE_valid_idxes] \\
 rw [] \\ gs [w2n_lt];

(* Also inefficient! *)
fun update_base_slice_2d_tac rel field =
 cheat; (* Fix later... *)

(* TODO: Step thms missing for now *)
fun prove_update_thms_2d fext_rel_const rel rel_const comms (field, field_data:allfieldinfo) = let
 val fupd = #fupd field_data
 val facc = #accessor field_data
 val key = fupd |> dest_const |> fst
 val (base_stmt, base_slice_stmt) = build_update_stmts_2d comms fext_rel_const rel_const field fupd facc
 val base_thm = prove (base_stmt, update_base_2d_tac rel field)
 val base_slice_thm = prove (base_slice_stmt, update_base_slice_2d_tac rel field)
in
 ([key], (base_thm, base_slice_thm))
end;

fun build_fext_read_thms fext_rel_const rel fext_rel (name, accessf) = let
 val nameHOL = fromMLstring name
 val typepred = accessf |> dest_const |> snd |> dom_rng |> snd |> predicate_for_type
in
  Q.prove(`!s s'. Eval_exp ^fext_rel_const ^rel fext s s' env (^typepred (^accessf fext)) (InputVar ^nameHOL)`,
          rw [Eval_exp_def, erun_def, erun_get_var_def, fext_rel,
              BOOL_def, WORD_def])
end;

fun build_module_rel_rel rel rel_const module_rel module_rel_const =
 prove(“∀s env fbits. ^module_rel_const s env ⇒ ^rel_const s s <|vars := env; nbq := []; fbits := fbits|>”,
       rw [module_rel, rel] \\
       FIRST [match_mp_tac module_state_rel_var_state_rel_var, match_mp_tac module_state_rel_var_state_rel_cvar] \\
       first_assum ACCEPT_TAC);

fun build_rel_module_rel rel rel_const module_rel module_rel_const =
 prove(“∀hol_s ver_s step. ^rel_const hol_s (step hol_s) ver_s ⇒
                           ^module_rel_const (step hol_s) (ver_s.nbq ++ ver_s.vars)”,
       rw [rel, module_rel] \\
       FIRST [match_mp_tac state_rel_var_module_state_rel_var \\ first_assum ACCEPT_TAC,
       match_mp_tac state_rel_cvar_module_state_rel_var \\ first_assum ACCEPT_TAC]);

fun prove_rel_var_inv rel rel_const is_rel_var is_rel_var_const =
 prove(“!var v s s' ver_s.
        ~(^is_rel_var_const) var ==>
       ^rel_const s s' (ver_s with vars := (var, v)::env) = ^rel_const s s' (ver_s with vars := env)”,
       simp [rel, is_rel_var, state_rel_var_set_var, state_rel_cvar_set_var]);

(* rel and rel_comb should be full defs

Debugging:
val fext_rel = fextv_rel_def;
val rel = state_rel_def;
val is_rel_var = is_state_rel_var_def;
val module_rel = module_state_rel_def;
*)
fun build_tstate fext_rel rel is_rel_var module_rel abstract_fields comms fext_ty state_ty = let
 val fext_rel_const = fext_rel |> concl |> strip_forall |> snd |> lhs |> strip_comb |> fst;
 val rel_const = rel |> concl |> strip_forall |> snd |> lhs |> strip_comb |> fst;
 val is_rel_var_const = is_rel_var |> concl |> strip_forall |> snd |> lhs |> strip_comb |> fst;
 val module_rel_const = module_rel |> concl |> strip_forall |> snd |> lhs |> strip_comb |> fst;
 
 val var_thms =
 all_fields_of state_ty
 |> map (fn (field, data) =>
            (#inner_accessor data,
             build_Eval_exp_var fext_rel_const rel_const rel comms (field, #accessor data, #ty data)))
 val (update_thms_2d, update_thms) =
 all_fields_of state_ty
 |> partition (fn (_, data) => (data |> #ty |> dest_type |> fst) = "fun");
 val update_thms =
 update_thms
 |> map (prove_update_thms fext_rel_const rel rel_const comms);
 val update_thms_2d =
 update_thms_2d
 |> map (prove_update_thms_2d fext_rel_const rel rel_const comms);
 val fext_read_thms =
 TypeBase.fields_of fext_ty
 |> filter (fn (f, _) => not (mem f abstract_fields))
 |> map (fn (field, field_data : TypeBase.rcd_fieldinfo) =>
            (#accessor field_data,
             build_fext_read_thms fext_rel_const rel_const fext_rel (field, #accessor field_data)))
 val module_rel_rel = build_module_rel_rel rel rel_const module_rel module_rel_const
 val rel_module_rel = build_rel_module_rel rel rel_const module_rel module_rel_const

 val rel_var_inv = prove_rel_var_inv rel rel_const is_rel_var is_rel_var_const
in
 { fext_ty = fext_ty, fext_rel = fext_rel_const,
   state_ty = state_ty, rel = rel_const, is_rel_var = is_rel_var_const, rel_var_inv = rel_var_inv,
   module_rel = module_rel_const,
   comms = comms,
   read_thms = var_thms, write_thms = update_thms, write_2d_thms = update_thms_2d,
   fext_read_thms = fext_read_thms,
   module_rel_rel = module_rel_rel,
   rel_module_rel = rel_module_rel } : tstate
end;

(* Test:

val state_ty = ``:avg_state``;
val fext_ty = ``:avg_ext_state``;

val tstate = build_tstate state_rel_def comms state_ty;
val s = “s:avg_state”;
val s' = “s':avg_state”;

hol2hardware_exp tstate s s' ``T``;
hol2hardware_exp tstate s s' ``roo:5 word``;
hol2hardware_exp tstate s s' ``s.avg + s'.h0``;

*)

(* Translator for expressions:
   translator state -> original hol state -> current hol state -> term to translate -> trans thm *)
fun hol2hardware_exp (tstate:tstate) s s' tm =
  (* True *)
  if same_const tm T then
   ISPECL [T, #fext_rel tstate, #rel tstate, s, s'] Eval_exp_bool

  (* False *)
  else if same_const tm F then
   ISPECL [F, #fext_rel tstate, #rel tstate, s, s'] Eval_exp_bool
        
  (* Variable *)
  (* TODO: Add check that the name+type is not the same as state var? *)
  else if is_var tm then let
   fun get_var_thm ty =
    if ty = bool then
     var_thm_BOOL
    else if is_word_type ty then
     var_thm_WORD
    else
     raise UnableToTranslateTy (ty, "no var_thm for type")
  
    val (vname, ty) = dest_var tm
    val th = get_var_thm ty
  in
    th |> ISPECL [#fext_rel tstate, #rel tstate, s, s', tm, fromMLstring vname] |> UNDISCH
  end

 (* Binary operation *)
 else if can dest_builtin_binop tm then let
  val (p, x1, x2, lemma) = dest_builtin_binop tm
  val th1 = hol2hardware_exp tstate s s' x1
  val th2 = hol2hardware_exp tstate s s' x2
  val th = MATCH_MP lemma (CONJ th1 th2)
 in
  th
 end

 (* Negation *)
 else if is_neg tm then let
  val arg = dest_neg tm
  val th = hol2hardware_exp tstate s s' arg
 in
  MATCH_MP Eval_exp_neg th
 end

 (* Inline if *)
 else if is_cond tm then let
  val (cond, lbranch, rbranch) = dest_cond tm
  val preconds = map (hol2hardware_exp tstate s s') [cond, lbranch, rbranch]
 in
  MATCH_MP Eval_exp_InlineIf (LIST_CONJ preconds)
 end

 (* Word constant, e.g. 22w *)
 (* TODO: Do we need to evaluate this down to bits? *)
 else if is_n2w tm andalso is_numeral (rand tm) then let
  val dim = dim_of tm
 in
  Eval_exp_word_const
  |> INST_TYPE [alpha |-> dim]
  |> ISPECL [#fext_rel tstate, #rel tstate, s, s', rand tm]
 end

 else if is_word_concat tm then let
  val (tml, tmr) = dest_word_concat tm
  val evall = hol2hardware_exp tstate s s' tml
  val evalr = hol2hardware_exp tstate s s' tmr
  val result = MATCH_MP Eval_exp_word_concat (CONJ evall evalr)
  (* TODO: Could add length check here ... *)
  val gammasum = Arbnum.+ (tml |> size_of, tmr |> size_of) |> mk_numeric_type
  val result = INST_TYPE [ gamma |-> gammasum ] result
  val result = EVAL_MP result
 in
  (*check_inv_Eval_exp "word_concat" tm*) result
 end

 (* CASE: word_bit *)
 (* NOTE: This only translates array indexing, as this is what's needed for Ag32 *)
 (* TODO: Could add better error message for when indexing outside the array (EVAL will just fail currently) *)
 else if is_word_bit tm then let
  val (i, var) = dest_word_bit tm
  val precond = hol2hardware_exp tstate s s' var
  val ret = MATCH_MP Eval_exp_word_bit precond
  val ret = SPEC i ret
  val precond = ret |> concl |> dest_imp |> fst |> EVAL_PROVE
 in
  MATCH_MP ret precond
 end

 (* CASE: word_extract *)
 else if is_word_extract tm then let
  val (high, low, arg, size) = dest_word_extract tm
  val precond = hol2hardware_exp tstate s s' arg
  val ret = MATCH_MP Eval_exp_word_extract precond
  val ret = ret |> ISPECL [high, low] |> INST_TYPE [ beta |-> size ]
  val precond = ret |> concl |> dest_imp |> fst |> EVAL_PROVE
  val ret = MP ret precond
 in
  ret
 end

 (* CASE: zero extend? *)
 else if is_w2w tm then let
  val (arg, out_dim) = dest_w2w tm
  val arg' = hol2hardware_exp tstate s s' arg
  val result = MATCH_MP Eval_exp_w2w arg'
  val result = INST_TYPE [ beta |-> out_dim ] result
 in
  ((CONV_RULE o RAND_CONV o RAND_CONV) SIZES_CONV) result
 end

 (* CASE: sign extend? (Almost identical to w2w.) *)
 else if is_sw2sw tm then let
  val (arg, out_dim) = dest_sw2sw tm
  val in_dim = dim_of arg
  val precond = mk_leq (mk_dimindex in_dim, mk_dimindex out_dim) |> EVAL_PROVE
  val arg' = hol2hardware_exp tstate s s' arg
  val result = MATCH_MP Eval_exp_sw2sw (CONJ precond arg')
 in
  ((CONV_RULE o RAND_CONV o RAND_CONV) SIZES_CONV) result
 end

 else if is_v2w tm then let
  val (arg, out_dim) = dest_v2w tm
  val precond = mk_less (term_of_int 1, mk_dimindex out_dim) |> EVAL_PROVE
  val (arg, _) = listSyntax.dest_cons arg
  val arg' = hol2hardware_exp tstate s s' arg
  val result = MATCH_MP Eval_exp_v2w (CONJ precond arg')
 in
  ((CONV_RULE o RAND_CONV o RAND_CONV) SIZES_CONV) result
 end

 (* Other compound expression, e.g. state projection *)
 else if is_comb tm then let
  val (f, arg) = dest_comb tm
 in
  (* SUBCASE: Read of communication variable? *)
   case lookup_same f (#read_thms tstate) of
    SOME th => check_inv_Eval_exp "state-read" tm (SPECL [s, s'] th) (* TODO: Add better error checking *)
  | NONE =>
  (* SUBCASE: External read? *)
    if is_var arg andalso (arg |> dest_var |> fst) = "fext" then
     case lookup_same f (#fext_read_thms tstate) of
            SOME result => check_inv_Eval_exp "external-read" tm (SPECL [s, s'] result)
          | NONE => raise UnableToTranslate (tm, "Unknown fext projection")
    (* SUBCASE: Array indexing? Just assume it is for now... TODO *)
     else let
      (* Strips state var as well... *)
      val (f, args) = strip_comb tm
      val f = mk_comb (f, hd args)
      val args = tl args
      val f' = hol2hardware_exp tstate s s' f
      val args' = map (hol2hardware_exp tstate s s') args
      val precond = LIST_CONJ (f' :: args')
      val result = case length args' of
                       1 => MATCH_MP Eval_exp_WORD_ARRAY_indexing precond
                   (*| 2 => MATCH_MP Eval_WORD_ARRAY_indexing2 precond*)
                     | _ => raise UnableToTranslate (tm, "Unsupported indexing")
     in
      check_inv_Eval_exp "state-read-indexing" tm result
     end
   (*else raise UnableToTranslate (tm, "Unknown comb case, not state projection")*)
 end

 else raise UnableToTranslate (tm, "Unknown case");

(** old things to be integrated: *)
(*
  (* CASE: Other compound expression, e.g. state projection ("state var")? *)
  else if is_comb tm then let
    val (f, arg) = dest_comb tm
  in
    (* SUBCASE: State selector? *)
    if identical arg s then
      case lookup_same f Eval_Vars of
          SOME result => SPEC s result
        | NONE => raise UnableToTranslate (tm, "Unknown state projection")

    (* SUBCASE: External read? *)
    else if identical arg fext_tm then
      case lookup_same f Eval_InputVars of
          SOME result => SPEC s result
        | NONE => raise UnableToTranslate (tm, "Unknown fext projection")

    (* SUBCASE: Array indexing? Just assume it is for now... TODO *)
    (*else let
      (* Strips state var as well... *)
      val (f, args) = strip_comb tm
      val f = mk_comb (f, hd args)
      val args = tl args
      val f' = hol2hardware_exp s f
      val args' = map (hol2hardware_exp s) args
      val precond = LIST_CONJ (f' :: args')
    in
      case length args' of
         1 => MATCH_MP Eval_WORD_ARRAY_indexing precond
       | 2 => MATCH_MP Eval_WORD_ARRAY_indexing2 precond
       | _ => raise UnableToTranslate (tm, "Unsupported indexing")
    end*)

    else
      raise UnableToTranslate (tm, "Unknown comb case, not state projection")
  end

  else raise UnableToTranslate (tm, "Unknown case");*)

(*
Testing:
val tm = ``(3 >< 1) s.instruction * ((2 >< 0) s.instruction):word3``;
val tm = ``s.PC - fext.data_rdata + r + Tr``;
val tm = ``(3 >< 1) fext.data_rdata + r + Tr``;
val tm = ``(5w:10 word) @@ (b:15 word)``

val s = ``s:state_circuit``;

hol2hardware_exp s tm
*)

end
