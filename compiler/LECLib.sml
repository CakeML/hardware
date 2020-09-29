structure LECLib =
struct

open hardwarePreamble;

open LECTheory;

open SMLRTLLib;

open listSyntax optionSyntax RTLSyntax;

(* LEC infrastructure *)

fun cache_cmp ((k1net, k1idx), (k2net, k2idx)) = let
 val netcmp = Int.compare (k1net, k2net) in
  if netcmp = EQUAL then
   case (k1idx, k2idx) of
     (NONE, NONE) => EQUAL
   | (NONE, SOME k2idx) => LESS
   | (SOME k1idx, NONE) => GREATER
   | (SOME k1idx, SOME k2idx) => Int.compare (k1idx, k2idx)
  else
   netcmp
 end;

(* Mutable state! NOTE: No need to have init here... use reset instead. *)
val cache = ref (Redblackmap.mkDict cache_cmp : (int * int option, thm) Redblackmap.dict);

val Cell2_thms = Redblackmap.fromList Term.compare [(“CAnd”, Eval_CAnd),
                                                    (“COr”, Eval_COr),
                                                    (“CEqual”, Eval_CEqual)];

val Eval_nl = rand o rator o rator;

(* Assumes everything has been blasted to bools already *)
(* Trivial limitation for now: Might produce incorrect results for reg names that end with digits *)
fun boolify_inp nl inp =
 if is_ConstInp inp then let
  val b = inp |> dest_ConstInp |> dest_CBool
 in
  SPECL [b, nl] Eval_ConstInp
 end else if is_ExtInp inp then let
  val (var, idx) = dest_ExtInp inp
  val var' = var |> stringLib.fromHOLstring
 in
  if is_none idx then
   Eval_ExtInp_NONE |> SPECL [var, mk_var ("fext_" ^ var', bool), nl] |> UNDISCH_ALL
  else let
   val idx = dest_some idx
   val idx' = idx |> dest_numeral |> Arbnumcore.toString
  in
   Eval_ExtInp_SOME |> SPECL [var, idx, mk_var ("fext_" ^ var' ^ "_" ^ idx', bool), nl] |> UNDISCH_ALL
 end end else if is_VarInp inp then let
  val (var, idx) = dest_VarInp inp
  val idx = if is_none idx then NONE else SOME (idx |> dest_some |> int_of_term)
 in
  if is_RegVar var andalso (* should never have idx: *) not (isSome idx) then let
   val (reg, i) = var |> dest_RegVar
   val reg' = reg |> stringLib.fromHOLstring
   val i' = i |> dest_numeral |> Arbnumcore.toString
   val regi = mk_var (reg' ^ i', bool)
  in
   Eval_RegVar_CBool |> SPECL [reg, i, regi, nl] |> UNDISCH_ALL
  end else if is_NetVar var then let
   val n = var |> dest_NetVar |> int_of_term
  in 
   Redblackmap.find (!cache, (n, idx))
  end else
   failwith "Unknown VarInp"
 end else
  failwith "Unknown cell input";

fun boolify_cell nl nl_distinct cellmem =
let
 val cell = cellmem |> concl |> dest_mem |> fst
 val () = print (term_to_string cell ^ "\n")
in
 if is_Cell1 cell then let
  val (t, out, in1) = dest_Cell1 cell
  val () = if t ~~ ``CNot`` then () else failwith "Non-neg 1-input cell?"
  val thm = MATCH_MP Eval_CNot nl_distinct |> UNDISCH
  val in1_thm = boolify_inp nl in1
  val thm = MATCH_MP thm (CONJ cellmem in1_thm)
  val () = cache := Redblackmap.insert (!cache, (out |> int_of_term, NONE), thm)
 in
  thm
 end else if is_Cell2 cell then let
  val (t, out, in1, in2) = dest_Cell2 cell
  val t_thm = Redblackmap.find (Cell2_thms, t)
  val t_thm = MATCH_MP t_thm nl_distinct |> UNDISCH
  val in1_thm = boolify_inp nl in1
  val in2_thm = boolify_inp nl in2
  val thm = MATCH_MP t_thm (LIST_CONJ [cellmem, in1_thm, in2_thm])
  val () = cache := Redblackmap.insert (!cache, (out |> int_of_term, NONE), thm)
 in
  thm
 end else if is_CellMux cell then let
  val (out, in1, in2, in3) = dest_CellMux cell
  val thm = MATCH_MP Eval_mux nl_distinct |> UNDISCH
  val ins = map (boolify_inp nl) [in1, in2, in3]
  val thm = MATCH_MP thm (LIST_CONJ (cellmem::ins))
  val () = cache := Redblackmap.insert (!cache, (out |> int_of_term, NONE), thm)
 in
  thm
 end else if is_CellLUT cell then let
  val (out, ins, tb) = dest_CellLUT cell
  val thm = lookup (ins |> listSyntax.dest_list |> fst |> length) [(2, Eval_LUT2), (3, Eval_LUT3), (4, Eval_LUT4), (5, Eval_LUT5), (6, Eval_LUT6)]
  val thm = MATCH_MP thm nl_distinct |> UNDISCH
  val precond = ins |> dest_list |> fst |> map (boolify_inp nl) |> cons cellmem |> LIST_CONJ
  val thm = MATCH_MP thm precond
  val thm = CONV_RULE (RAND_CONV (REWRITE_CONV [gen_lut_cond_def, LIST_REL_def])) thm
  val () = cache := Redblackmap.insert (!cache, (out |> int_of_term, NONE), thm)
 in
  thm
 end else if is_Carry4 cell then let
   val (out, cout, cin, lin, rin) = dest_Carry4 cell
   val thm = MATCH_MP Eval_Carry4 nl_distinct |> UNDISCH
   val precond = cellmem ::
                 (boolify_inp nl cin) ::
                 (lin |> dest_list |> fst |> map (boolify_inp nl)) @
                 (rin |> dest_list |> fst |> map (boolify_inp nl)) @
                 [mk_eq (out, cout) |> mk_neg |> EVAL_PROVE] |> LIST_CONJ
   val thm = MATCH_MP thm precond
   val [out0, out1, out2, out3, cout0, cout1, cout2, cout3] = CONJUNCTS thm

   val out = int_of_term out
   val cout = int_of_term cout
   val () = cache := Redblackmap.insert (!cache, (out, SOME 0), out0)
   val () = cache := Redblackmap.insert (!cache, (out, SOME 1), out1)
   val () = cache := Redblackmap.insert (!cache, (out, SOME 2), out2)
   val () = cache := Redblackmap.insert (!cache, (out, SOME 3), out3)
   val () = cache := Redblackmap.insert (!cache, (cout, SOME 0), cout0)
   val () = cache := Redblackmap.insert (!cache, (cout, SOME 1), cout1)
   val () = cache := Redblackmap.insert (!cache, (cout, SOME 2), cout2)
   val () = cache := Redblackmap.insert (!cache, (cout, SOME 3), cout3)
 in
  thm
 end else
  failwith "unknown cell"
end;

fun prove_ALL_DISTINCT_FLAT_MAP_cell_output nl_def = let
 (* Copied from permLib *)
 val num_ALL_DISTINCT_CONV = permLib.ALL_DISTINCT_CONV
  (MATCH_MP comparisonTheory.good_cmp_Less_irrefl_trans comparisonTheory.num_cmp_good)
  (fn x => fn y => numSyntax.int_of_term x < numSyntax.int_of_term y) EVAL
 val nl = nl_def |> concl |> lhs
in
 “ALL_DISTINCT (FLAT (MAP cell_output ^nl))”
 |> ((RAND_CONV EVAL) THENC num_ALL_DISTINCT_CONV)
 |> EQT_ELIM
end;

fun boolify_netlist nl_def = let
 val nl_distinct = prove_ALL_DISTINCT_FLAT_MAP_cell_output nl_def;
 val nl = nl_def |> concl |> lhs;
 val cells = MATCH_MP all_mems nl_def
             |> PURE_REWRITE_RULE [EVERY_MEM_compute]
             |> CONJUNCTS |> butlast; (* last element is always T *)
in
 app (K () o (boolify_cell nl nl_distinct)) cells (* val cell = cells |> hd *)
end;

fun reset_boolify_state () = cache := Redblackmap.mkDict cache_cmp;

fun cleanup_inp_eq_thm th extenv regs = let
 val cleanup_cget_var_var = rand o rand o rhs
 fun cleanup_extenv_var tm = if boolSyntax.is_exists tm then
                              (rand o rand o rhs o rand o snd o boolSyntax.dest_exists) tm
                             else
                              tm |> rhs |> rand |> rand
 (*val extenv_fext_val = rand o rhs o lhand o snd o boolSyntax.dest_exists*)
 val st_nl_overlap_nl = rand
 fun is_st_nl_overlap tm = (tm |> strip_comb |> fst) ~~ “st_nl_overlap”
                                                    
 val (cget_var_hyps, other_hyps) = th |> hyp |> partition (fn tm => is_eq tm andalso is_cget_var (lhs tm))
 val (st_nl_overlap_hyps, extenv_hyps) = other_hyps |> partition is_st_nl_overlap

 val th = foldr (fn (tm, th) =>
                    MP (DISCH tm th) (cleanup_populated_by_regs_only_st_nl_overlap |> ISPECL [regs, st_nl_overlap_nl tm] |> UNDISCH_ALL))
                    th st_nl_overlap_hyps
 val th = DISCH “populated_by_regs_only ^regs st” th
                                              
 val th = foldr (fn (tm, th) => th |> DISCH tm
                                   |> GEN (cleanup_cget_var_var tm)
                                   |> HO_MATCH_MP cleanup_cget_var_CBool_imp
                                   |> EVAL_MP) th cget_var_hyps

 val cleanup_extenv_CBool' = SPEC extenv cleanup_extenv_CBool
 val cleanup_extenv_CArray' = SPEC extenv cleanup_extenv_CArray
 val th = foldr (fn (tm, th) => let
                                 val th_match = if tm |> boolSyntax.is_exists then
                                                 cleanup_extenv_CArray'
                                                else
                                                 cleanup_extenv_CBool'
                                in
                                 th |> DISCH tm
                                    |> GEN (cleanup_extenv_var tm)
                                    |> Ho_Rewrite.REWRITE_RULE [GSYM PULL_EXISTS]
                                    |> (fn th => MP th (PART_MATCH (rand o rand) th_match (th |> concl |> lhand) |> UNDISCH |> EVAL_MP)) end) th extenv_hyps
 val th = DISCH_ALL th |> REWRITE_RULE [AND_IMP_INTRO]
in
 th
end;

fun build_inp_thm extenv regs cache newcache (n, idx) = let
 val inp_thm = Redblackmap.find (cache, (n, idx))
 val new_inp_thm = Redblackmap.find (newcache, (n, idx))
 val th = MATCH_MP same_output_in_diff_netlist (CONJ inp_thm new_inp_thm)
 val c = start_time ();
 val precond = th |> concl |> lhand |> minisatProve.SAT_PROVE;
 val () = end_time c;
 val th = MP th precond;
 val th = cleanup_inp_eq_thm th extenv regs
in
 th
end;

(* Top-level entry point: Expects the original circuit (as a term) and the new netlist (as a term) as input *)
fun lec circuit oldnl_def newnl_def = let
 (* TODO: Could sanity check that we have the correct oldnl_def here... *)
 val (extenv, regs, _) = dest_Circuit circuit

 val () = reset_boolify_state ()
 val () = print "Boolifying original netlist...\n"
 val c = start_time ();
 val () = boolify_netlist oldnl_def
 val () = end_time c;
 val nl_cache = !cache

 val () = reset_boolify_state ()
 val () = print "Boolifying tech. mapped netlist...\n"
 val c = start_time ();
 val () = boolify_netlist newnl_def
 val () = end_time c;
 val newnl_cache = !cache

 val th = SPECL [oldnl_def |> concl |> lhs, newnl_def |> concl |> lhs, regs, extenv] circut_run_cong

 val () = print "Proving all reg inputs equal using SAT...\n"
 val c = start_time ();
 fun inp_to_cache_key (VarInp (NetVar n, idx)) = (n, idx)
 (* set_goal ([], th |> concl |> lhand) *)

 fun cell_inp_run_eq_tac (asm, g) = let
  val inp_key = g |> rhs |> rand |> extract_cell_input |> inp_to_cache_key
  val inp_key_str = (inp_key |> fst |> Int.toString) ^ (case inp_key |> snd of
                                                          NONE => ""
                                                        | SOME idx => "[" ^ Int.toString idx ^ "]")
  val () = print ("Proving input " ^ inp_key_str ^ " eqv.\n")
  val c = start_time ();
 in
  drule_strip (build_inp_thm extenv regs nl_cache newnl_cache inp_key) \\ kall_tac (end_time c)
 end (asm, g)
 val precond = prove(th |> concl |> lhand,
                     rewrite_tac [EVERY_DEF, reg_inp_rel_trivial] \\ rpt conj_tac \\
                     rw [reg_inp_rel_def] \\ cell_inp_run_eq_tac)
 val () = end_time c;
 val th = MP th precond

 val () = print "Validating tech. mapped netlist...\n"
 val th = EVAL_MP th
in
 th
end;

(*
(* Example *)
val nl = ``[
 Cell2 CAnd 0 (VarInp (RegVar "a" 0) NONE) (VarInp (RegVar "b" 0) NONE);
 Cell2 CAnd 1 (VarInp (RegVar "c" 0) NONE) (VarInp (RegVar "d" 0) NONE);
 Cell2 CAnd 2 (VarInp (NetVar 0) NONE) (VarInp (NetVar 1) NONE);
 Cell2 COr 3 (VarInp (NetVar 2) NONE) (VarInp (NetVar 2) NONE);
 Carry4 (* out cout: *) 4 5 (ConstInp (CBool F))
        [VarInp (NetVar 0) NONE; VarInp (NetVar 1) NONE; VarInp (NetVar 2) NONE; VarInp (NetVar 3) NONE]
        [VarInp (RegVar "r" 3) NONE; VarInp (RegVar "r" 2) NONE; VarInp (RegVar "r" 1) NONE; VarInp (RegVar "r" 0) NONE]]``;

val lutnl = ``[
 CellLUT 0 [VarInp (RegVar "a" 0) NONE; VarInp (RegVar "b" 0) NONE] [[T; T]];
 CellLUT 3 [VarInp (RegVar "c" 0) NONE; VarInp (RegVar "d" 0) NONE; VarInp (NetVar 0) NONE] [[T; T; T]]]``;

val nlsmall = ``[
 Cell2 CAnd 0 (VarInp (RegVar "a")) (VarInp (RegVar "b"));
 Cell2 COr 1 (VarInp (NetVar 0)) (VarInp (RegVar "c"))]``;

val lutnl = ``[
 CellLUT 0 [VarInp (RegVar "a"); VarInp (RegVar "b"); VarInp (RegVar "c")] [[F; F; T]; [F; T; T]; [T; F; T]; [T; T; F]; [T; T; T]]]``;

(* Experiment with same netlist *)
val th = MATCH_MP same_output_in_same_netlist
                  (CONJ (Redblackmap.find (!cache, (3, NONE))) (Redblackmap.find (!cache, (2, NONE))));
val precond = th |> concl |> lhand |> minisatProve.SAT_PROVE;
val th = MP th precond
val th = th |> CONV_RULE (LAND_CONV (LHS_CONV (RAND_CONV EVAL)));

(*val cleanup_boolify_thm = CONV_RULE (LAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV EVAL))));*)

(* Experiment with different netlists *)
reset_boolify_state ()
boolify_netlist nl
val nl_output_cell = Redblackmap.find (!cache, (4, NONE))

reset_boolify_state ()
boolify_netlist newnl
val lutnl_output_cell = Redblackmap.find (!cache, (4, NONE))

minisatProve.SAT_PROVE (mk_eq (nl_output_cell |> concl |> rand,
                               lutnl_output_cell |> concl |> rand))

val th = MATCH_MP same_output_in_diff_netlist (CONJ nl_output_cell lutnl_output_cell)
val precond = th |> concl |> lhand |> minisatProve.SAT_PROVE;
val th = MP th precond;
val th = REWRITE_RULE [SNOC] th;
*)

(* Experiment with long AND chain *)
(*
fun add_pointless_base_and_cell nl = let
 val inp1 = "a" |> stringSyntax.fromMLstring |> mk_RegVar |> mk_VarInp
 val inp2 = "b" |> stringSyntax.fromMLstring |> mk_RegVar |> mk_VarInp
 val new_cell = mk_Cell2 (``CAnd``, zero_tm, inp1, inp2)
in
 mk_cons (new_cell, nl)
end;

fun add_pointless_and_cell out nl = let
 val inp = mk_VarInp (mk_NetVar (term_of_int (out - 1)))
 val new_cell = mk_Cell2 (``CAnd``, term_of_int out, inp, inp)
in
 mk_cons (new_cell, nl)
end;

fun build_pointless_and_chain depth = let
 fun build_pointless_and_chain' depth nl =
  if depth > 0 then
   build_pointless_and_chain' (depth - 1) (add_pointless_and_cell depth nl)
  else
   add_pointless_base_and_cell nl
in
 build_pointless_and_chain' depth (mk_nil cell_ty)
end

val nl = build_pointless_and_chain 3;
val lutnl = ``[CellLUT 20 [VarInp (RegVar "b"); VarInp (RegVar "a")] [[T; T]]]``;

val th = MATCH_MP same_output_in_diff_netlist (CONJ nl_output_cell lutnl_output_cell)
val precond = th |> concl |> lhand |> minisatProve.SAT_PROVE;
val th = MP th precond;
val th = REWRITE_RULE [SNOC] th;
*)

end
