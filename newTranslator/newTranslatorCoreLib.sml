structure newTranslatorCoreLib =
struct

open hardwarePreamble;

open fcpSyntax wordsSyntax;

open verilogSyntax;

exception UnableToTranslate of term * string;
exception UnableToTranslateTy of hol_type * string;

(** Type predicates **)

fun predicate_for_type ty =
  if is_type ty then let
    val (tname, tl) = dest_type ty
  in
    if tname = "bool" then
      BOOL_tm
    else if tname = "fun" then let
      val (alpha', beta') = dom_rng ty
      val ipred = predicate_for_type beta'
      val alpha' = dest_word_type alpha'
      val pred = inst [ alpha |-> alpha' ] WORD_ARRAY_tm
    in
      mk_icomb (pred, ipred)
    end else if is_word_type ty then
      inst [ alpha |-> dest_word_type ty ] WORD_tm
    else
      raise UnableToTranslateTy (ty, "no predicate for type")
  end
  else raise UnableToTranslateTy (ty, "just a type variable");

val predicate_for_value = predicate_for_type o type_of;

fun hol2ver_for_type ty =
 if ty = bool then
  VBool_tm
 else if is_word_type ty then let
  val alpha' = dest_word_type ty
 in
  inst [ alpha |-> alpha' ] w2ver_tm
 end else
  raise UnableToTranslateTy (ty, "unknown type");

fun verty_for_type ty =
  if is_type ty then let
    val (tname, tl) = dest_type ty
  in
    if tname = "bool" then
      VBool_t_tm
    (*else if tname = "fun" then let
      val (args, res) = strip_fun ty
      val args = map (curry Arbnumcore.pow Arbnumcore.two o dest_numeric_type o dest_word_type) args
      val res = if res = bool then
                  []
                else (* otherwise assume we have word ... *)
                  [res |> dest_word_type |> dest_numeric_type]
    in
      mk_VArray_t (args @ res)
    end*) else if is_word_type ty then let
      val n = ty |> dest_word_type |> dest_numeric_type
    in
      mk_VArray_t n
    end else
    raise UnableToTranslateTy (ty, "unknown type")
  end
  else raise UnableToTranslateTy (ty, "just a type variable");

(*
fun build_fextv_others include_time vars = let
 val vars = pred_setSyntax.mk_set vars
 val tm = if include_time then
           ``!var. var ∉ ^vars ==> fextv (n:num) var = INL UnknownVariable``
          else
            ``!var. var ∉ ^vars ==> fextv var = INL UnknownVariable``
in
 inst [ alpha |-> ``:value`` ] tm
end;
*)

(** Handling X values in HOL circuits **)

(* Limited error-handling for now *)
fun add_x_init filled oracle ((field, field_data : TypeBase.rcd_fieldinfo), (inits, shift)) =
 case lookup_opt field filled of
   SOME _ => (inits, shift)
 | NONE => let
    val ty = #ty field_data
    val fupd = #fupd field_data
    val (tname, _) = dest_type ty
   in
    if tname = "bool" then
     (mk_comb (fupd, combinSyntax.mk_K_1(mk_comb(oracle, term_of_int shift), ty)) :: inits, shift + 1)
    else if is_word_type ty then let
     val n = ty |> dest_word_type |> dest_numeric_type
     val ggenlist_tm = “ggenlist”
     val v = bitstringSyntax.mk_v2w (list_mk_icomb(ggenlist_tm, [oracle, term_of_int shift, mk_numeral n]),
                                    dest_word_type ty)
     val inits' = mk_comb (fupd, combinSyntax.mk_K_1(v, ty)) :: inits
    in
     (inits', shift + Arbnumcore.toInt n)
    end else
     raise UnableToTranslateTy (ty, "unknown type")
   end;

fun add_x_inits det_values = let
 val oracle = mk_var("fbits", “:num -> bool”)
 val (state_ty, filled) = TypeBase.dest_record det_values
 (* We do this in two steps to get oracle reads in the right order: *)
 val inits = TypeBase.fields_of state_ty |> foldl (add_x_init filled oracle) ([], 0) |> fst
in
 foldl (fn (init, tm) => mk_comb(init, tm)) det_values inits
end;

end
