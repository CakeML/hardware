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

datatype rec_hol_record = HOLRecord of string * hol_type * (rec_hol_record list) | HOLRecordField of string * hol_type * (term option);

fun rec_dest_record_field filled_fields (f, f_data) = let
 val prevval = lookup_opt f filled_fields
 val ty = #ty f_data
in
 if TypeBase.is_record_type ty then let
  val filled_fields = case prevval of
                        NONE => []
                      | SOME tm => tm |> TypeBase.dest_record |> snd
  val allfields = TypeBase.fields_of ty
 in
  HOLRecord (f, ty, map (rec_dest_record_field filled_fields) allfields)
 end else
  HOLRecordField (f, ty, prevval)
end;

fun rec_dest_record tm : rec_hol_record = let
 val (ty, filled_fields) = TypeBase.dest_record tm
 val allfields = TypeBase.fields_of ty
in
 HOLRecord ("", ty, map (rec_dest_record_field filled_fields) allfields)
end;

fun rec_mk_record r =
 case r of
   HOLRecord (field, ty, rr) => [(field, TypeBase.mk_record (ty, rr |> map rec_mk_record |> flatten))]
 | HOLRecordField (field, ty, v) => (case v of NONE => [] | SOME tm => [(field, tm)]);

fun rec_record_map f r =
 case r of
   HOLRecord (field, ty, rr) => HOLRecord (field, ty, map (rec_record_map f) rr)
 | HOLRecordField (field, ty, v) => HOLRecordField (field, ty, f ty v);

fun add_x_inits det_values = let
 val shift = ref 0

 fun add_x_init oracle ty v =
  case v of
    SOME tm => SOME tm
  | NONE => SOME (
     if ty = bool then let
      val shift_old = !shift;
      val _ = (shift := shift_old + 1)
     in
      mk_comb (oracle, term_of_int shift_old)
     end else if is_word_type ty then let
      val n = ty |> dest_word_type |> dest_numeric_type
      val ggenlist_tm = mk_const ("ggenlist", “:(num -> α) -> num -> num -> α list”)
      val shift_old = !shift;
      val _ = (shift := shift_old + (Arbnumcore.toInt n))
     in
      bitstringSyntax.mk_v2w (list_mk_icomb (ggenlist_tm, [oracle, term_of_int shift_old, mk_numeral n]),
                              dest_word_type ty)
     end else
      raise UnableToTranslateTy (ty, "unknown/unsupported type"))

 val oracle = mk_var("fbits", “:num -> bool”)
 val r = rec_dest_record det_values
 val r = rec_record_map (add_x_init oracle) r
 val r = r |> rec_mk_record |> hd |> snd
in
 r
end;

end
