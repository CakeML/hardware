structure verilogTranslatorCoreLib =
struct

open hardwarePreamble;

open fcpSyntax wordsSyntax;

open verilogSyntax;

exception UnableToTranslate of term * string;
exception UnableToTranslateTy of hol_type * string;

(** Type predicates **)

fun predicate_for_type_ty ty =
  if is_type ty then let
    val (tname, tl) = dest_type ty
  in
    if tname = "bool" then
      BOOL_tm
    else if tname = "fun" then let
      val (alpha', beta') = dom_rng ty
      val ipred = predicate_for_type_ty beta'
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

(* TODO: Rename function? *)
fun predicate_for_type tm =
 tm |> type_of |> predicate_for_type_ty;

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
    else if tname = "fun" then let
      val (args, res) = strip_fun ty
      val args = map (curry Arbnumcore.pow Arbnumcore.two o dest_numeric_type o dest_word_type) args
      val res = if res = bool then
                  []
                else (* otherwise assume we have word ... *)
                  [res |> dest_word_type |> dest_numeric_type]
    in
      mk_VArray_t (args @ res)
    end else if is_word_type ty then let
      val n = ty |> dest_word_type |> dest_numeric_type
    in
      mk_VArray_t [n]
    end else
    raise UnableToTranslateTy (ty, "unknown type")
  end
  else raise UnableToTranslateTy (ty, "just a type variable");

fun build_fextv_others include_time vars = let
 val vars = pred_setSyntax.mk_set vars
 val tm = if include_time then
           ``!var. var ∉ ^vars ==> fextv (n:num) var = INL UnknownVariable``
          else
            ``!var. var ∉ ^vars ==> fextv var = INL UnknownVariable``
in
 inst [ alpha |-> ``:value`` ] tm
end;

end
