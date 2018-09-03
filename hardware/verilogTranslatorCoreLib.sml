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
      val alpha' = dest_word_type alpha'
      val beta' = dest_word_type beta'
    in
      inst [ alpha |-> alpha', beta |-> beta' ] WORD_ARRAY_tm
    end else if is_word_type ty then
      inst [ alpha |-> dest_word_type ty ] WORD_tm
    else
      raise UnableToTranslateTy (ty, "no predicate for type")
  end
  else raise UnableToTranslateTy (ty, "just a type variable");

(* TODO: Rename function? *)
fun predicate_for_type tm = predicate_for_type_ty (type_of tm);

fun hol2ver_for_type ty =
  if ty = bool then
    VBool_tm
  else if is_word_type ty then let
    val alpha' = dest_word_type ty
  in
    inst [ alpha |-> alpha' ] w2ver_tm
  end else
    raise UnableToTranslateTy (ty, "unknown type");

(* I think this is a duplicate of a function available elsewhere? *)
fun verty_for_type ty =
  if is_type ty then let
    val (tname, tl) = dest_type ty
  in
    if tname = "bool" then
      VBool_t_tm
    else if tname = "fun" then let
      val (alpha', beta') = dom_rng ty
      val alpha' = alpha' |> dest_word_type |> dest_numeric_type
      val beta' = beta' |> dest_word_type |> dest_numeric_type
    in
      mk_VArray_t [Arbnumcore.pow (Arbnumcore.two, alpha'), beta']
    end else if is_word_type ty then let
      val n = ty |> dest_word_type |> dest_numeric_type
    in
      mk_VArray_t [n]
    end else
    raise UnableToTranslateTy (ty, "unknown type")
  end
  else raise UnableToTranslateTy (ty, "just a type variable");

end