structure translatorCoreLib =
struct

open hardwarePreamble;

open fcpSyntax wordsSyntax;

open verilogSyntax;

exception UnableToTranslate of term * string;
exception UnableToTranslateTy of hol_type * string;

type allfieldinfo = { ty : hol_type, accessor : term, inner_accessor : term, fupd_key : string list, fupd : term };

fun all_fields_of ty : (string * allfieldinfo) list =
 all_fields_of' ty ty []

and all_fields_of' base_ty ty accessors =
 TypeBase.fields_of ty |> map (all_fields_of_field base_ty accessors) |> flatten

and all_fields_of_field base_ty accessors (f, fd) = let
  val accessors = (#accessor fd) :: accessors
  val fty = #ty fd
 in
  if TypeBase.is_record_type fty then let
   fun mk_K_11 tm = combinSyntax.mk_K_1 (tm, type_of tm)
   fun try_drop_abs tm = if is_abs tm then (tm |> dest_abs |> snd) else tm
   fun try_drop_comb tm = if is_comb tm then (tm |> dest_comb |> snd) else tm

   fun comb_depth tm =
    if is_comb tm then 1 + (tm |> dest_comb |> snd |> comb_depth) else 0

   fun apply_while f condf tm =
     if condf tm then apply_while f condf (f tm) else tm

   fun new_fupt fupt accessor = let
    (* kind of a hack, to handle nested records inside records *)
    val s = accessor |> try_drop_abs |> apply_while (snd o dest_comb) (fn tm => (comb_depth tm) >= (length accessors))
    val (vs, tm) = strip_abs fupt
    val tm = list_mk_comb (#fupd fd, [mk_K_11 tm, s])
    val tm = list_mk_abs (vs, tm)
   in
    tm
   end

   fun update_fupd (f, res_fd : allfieldinfo) =
    (f, { ty = #ty res_fd,
          accessor = #accessor res_fd,
          inner_accessor = #inner_accessor res_fd,
          fupd_key = (#fupd fd |> dest_const |> fst) :: #fupd_key res_fd,
          fupd = new_fupt (#fupd res_fd) (#accessor res_fd) })
  in
   all_fields_of' base_ty fty accessors |> map update_fupd
  end else let
   val s = mk_var ("s", base_ty)
   val ac = if length accessors = 1 then (hd accessors) else (foldr mk_comb s accessors |> curry mk_abs s)

   val fupd_accessor = if length accessors = 1 then s else (dest_abs ac |> snd |> dest_comb |> snd)
   val e = mk_var ("e", fty)
   val fupd = list_mk_comb (#fupd fd, [combinSyntax.mk_K_1 (e, fty), fupd_accessor])
            |> curry list_mk_abs [s, e]
  in
   [(f, { ty = fty, accessor = ac, inner_accessor = #accessor fd, fupd_key = [#fupd fd |> dest_const |> fst], fupd = fupd })]
  end
 end;

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
  end else
   raise UnableToTranslateTy (ty, "just a type variable");

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
    else if tname = "fun" then let
      val (args, res) = strip_fun ty
      val args = map (curry Arbnumcore.pow Arbnumcore.two o dest_numeric_type o dest_word_type) args
      val res = if res = bool then
                  []
                else (* otherwise assume we have word ... *)
                  [res |> dest_word_type |> dest_numeric_type]
    in
      case (args @ res) of
         [i1] => mk_VArray_t i1
       | [i1, i2] => mk_VArray2_t i1 i2
       | _ => raise UnableToTranslateTy (ty, "unknown type")
    end else if is_word_type ty then let
      val n = ty |> dest_word_type |> dest_numeric_type
    in
      mk_VArray_t n
    end else
    raise UnableToTranslateTy (ty, "unknown type")
  end else
   raise UnableToTranslateTy (ty, "just a type variable");

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
