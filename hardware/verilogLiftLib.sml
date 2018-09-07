structure verilogLiftLib =
struct

open combinSyntax fcpSyntax wordsSyntax stringSyntax;

open verilogTypeTheory;

open verilogTranslatorConfigLib;

open verilogSyntax;

local
val (var_has_type_tm, mk_var_has_type, dest_var_has_type, is_var_has_type) = syntax_fns3 "verilogType" "var_has_type";
in
fun var_has_type_to_old_CONV tm =
 if is_abs tm then
   ABS_CONV var_has_type_to_old_CONV tm
 else if is_var_has_type tm then let
   val (_, _, ty) = dest_var_has_type tm
 in
   if is_VBool_t ty then (* BOOL *)
     PURE_REWRITE_CONV [GSYM var_has_type_old_var_has_type_BOOL] tm
   else if is_VArray_t ty then let
     val is = dest_VArray_t ty
     val len = length is
   in
     if len = 1 then (* WORD, TODO: assumes numerals in index position *) let
       val dimindex_rw = is |> hd |> dest_numeral |> mk_numeric_type |> mk_dimindex |> EVAL |> SYM
     in
       PURE_REWRITE_CONV [dimindex_rw, GSYM var_has_type_old_var_has_type_WORD] tm
     end else if len = 2 then (* WORD_ARRAY, TODO: does not work if index same... *) let
       val dimword_rw = is |> hd |> dest_numeral |> Arbnumcore.log2 |> mk_numeric_type |> mk_dimword |> EVAL |> SYM
       val dimindex_rw = is |> tl |> hd |> dest_numeral |> mk_numeric_type |> mk_dimindex |> EVAL |> SYM
     in
       PURE_REWRITE_CONV [dimword_rw, dimindex_rw, GSYM var_has_type_old_var_has_type_WORD_ARRAY] tm
     end else
       ALL_CONV tm
   end else
     ALL_CONV tm
 end else if is_comb tm then
   COMB_CONV var_has_type_to_old_CONV tm
 else ALL_CONV tm
end;

val relM_backwards_tac =
 CONV_TAC var_has_type_to_old_CONV \\

 simp [var_has_type_old_def, var_has_value_def] \\

 disch_then (MAP_EVERY (REPEAT_TCL CHOOSE_THEN ASSUME_TAC) o CONJUNCTS) \\

 (fn g as (asl, _) => let
     val hol_s = foldr (fn (assm, acc) => let
                          val (lconj, rconj) = dest_conj assm
                          val name = lconj |> lhs |> rand |> fromHOLstring
                          val update = lookup name updates
                          val rep = rconj |> rator |> rand
                        in
                          mk_comb(mk_comb (update, (mk_K_1 (rep, type_of rep))), acc)
                        end)
                       (mk_arb state_ty)
                       asl
  in
    EXISTS_TAC hol_s g
  end) \\

 simp [];

end
