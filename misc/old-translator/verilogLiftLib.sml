structure verilogLiftLib =
struct

open combinSyntax fcpSyntax wordsSyntax stringSyntax;

open verilogTypeTheory;

open verilogTranslatorConfigLib;

open verilogSyntax;

local
val (var_has_type_tm, mk_var_has_type, dest_var_has_type, is_var_has_type) = syntax_fns3 "verilogType" "var_has_type";

fun thm_pred th = th |> SPEC_ALL |> concl |> lhs |> rand

val conv_thms =
 [var_has_type_old_var_has_type_BOOL,
  var_has_type_old_var_has_type_WORD,
  var_has_type_old_var_has_type_WORD_ARRAY_BOOL,
  var_has_type_old_var_has_type_WORD_ARRAY,
  var_has_type_old_var_has_type_WORD_ARRAY_WORD_ARRAY]
 |> map (fn th => (thm_pred th, th));

fun lookup_match_term x nil = failwith "unknown verilog type"
  | lookup_match_term x ((k, v) :: ls) = if can (match_term k) x then v else lookup_match_term x ls;
in
fun var_has_type_to_old_CONV tm =
 if is_abs tm then
   ABS_CONV var_has_type_to_old_CONV tm
 else if is_var_has_type tm then let
   val (_, var, ty) = dest_var_has_type tm
   val pred = var |> fromHOLstring |> predicate_for_var
   (* inefficient but works: *)
   val pred_thm = lookup_match_term pred conv_thms
   val pred_thm = PART_MATCH (rand o lhs) pred_thm pred
                  |> CONV_RULE (RHS_CONV (RAND_CONV EVAL))
                  |> SYM
 in
  PURE_REWRITE_CONV [pred_thm] tm
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
