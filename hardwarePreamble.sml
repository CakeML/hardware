structure hardwarePreamble = struct

(* basic *)
open HolKernel Parse boolLib bossLib BasicProvers;

(* Additional *)
open listTheory wordsTheory;
open numLib wordsLib mp_then;

(* Project libraries *)
open hardwareMiscTheory;

(*
Setup:
guess_lengths ();
prefer_num ();
*)

(* Borrowed from cakeml: *)
val rveq = rpt BasicProvers.VAR_EQ_TAC;
val asm_exists_tac = goal_assum drule;
val asm_exists_any_tac = goal_assum (first_assum o mp_then Any mp_tac);

(* *)

fun drule_strip_tac (g as (tms, tm)) = let
  val tm = tm |> dest_imp |> fst |> strip_forall |> snd
in
 if not (is_imp tm) orelse is_neg tm then
   strip_tac g
 else
   FAIL_TAC "drule_strip_tac" g
end;

fun drule_strip th = drule th \\ rpt (disch_then drule) \\ TRY drule_strip_tac \\ rveq;
val drule_first = first_x_assum drule \\ rpt (disch_then drule) \\ TRY drule_strip_tac;
val drule_last = last_x_assum drule \\ rpt (disch_then drule) \\ TRY drule_strip_tac;

fun strip_disch_tac (g as (tms, tm)) =
 if not (is_neg tm) andalso is_imp tm then
   strip_tac g
 else
   FAIL_TAC "strip_disch_tac" g;

val strip_tac' = gen_tac ORELSE strip_disch_tac;

val f_equals_tac = rpt (AP_THM_TAC ORELSE AP_TERM_TAC);

fun flip f x y = f y x;

fun sing x = [x];

fun fst_map f = map (fn (fst, snd) => (f fst, snd));

fun snd_map f = map (fn (fst, snd) => (fst, f snd));

(* Filters list l by the list of bools in filterl, if true, keep element, otherwise, drop it *)
(* TODO: Should maybe raise something better *)
fun filter_by_list l filterl =
 case (l, filterl) of
     ([], []) => []
   | (x::xs, y::ys) => append (if y then [x] else []) (filter_by_list xs ys)
   | (_, _) => raise Empty;

fun EVAL_PROVE tm = EVAL tm |> EQT_ELIM;

fun EVAL_MP th = let
  val ant = th |> concl |> dest_imp |> fst |> EVAL_PROVE
in
  MP th ant
end;

fun lookup x nil = failwith "Unknown key"
  | lookup x ((k, v) :: ls) = if x = k then v else lookup x ls;

fun lookup_opt x [] = NONE
  | lookup_opt x ((k, v) :: ls) = if x = k then SOME v else lookup_opt x ls;

(* lookup from for terms *)
fun lookup_term x nil = failwith "Unknown term"
  | lookup_term x ((k, v) :: ls) = if identical x k then v else lookup_term x ls;

(* lookup from assoc list based on key sameness *)
fun lookup_same x nil = NONE
  | lookup_same x ((k, v) :: ls) = if same_const x k then SOME v else lookup_same x ls;

(* TODO: This is the same as Lib.can? (Not sure!) *)
fun can f x = (f x; true) handle HOL_ERR _ => false;

fun ASM_CONV_RULE c = (CONV_RULE c) o (HYP_CONV_RULE (K true) c);

(*fun drule th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th));*)

fun is_bool_type ty =
  is_type ty andalso (ty |> dest_type |> fst) = "bool";

(* https://stackoverflow.com/a/33606353 *)
fun writeFile filename content =
  let val fd = TextIO.openOut filename
      val _ = TextIO.output (fd, content) handle e => (TextIO.closeOut fd; raise e)
      val _ = TextIO.closeOut fd
  in () end;

end
