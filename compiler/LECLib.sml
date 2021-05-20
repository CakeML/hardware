structure LECLib =
struct

open hardwarePreamble;

open LECTheory;

open SMLRTLLib;

open listSyntax optionSyntax RTLSyntax;

(* Syntax *)

fun is_Eval tm =
 (tm |> strip_comb |> fst |> dest_const |> fst) = "Eval";

fun is_fext_bool tm =
 (tm |> strip_comb |> fst |> dest_const |> fst) = "fext_bool";

fun is_fext_array tm =
 (tm |> strip_comb |> fst |> dest_const |> fst) = "fext_array";

(* LEC boolification infrastructure *)

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

(* Cache for eq infrastructure *)
val eq_cache = ref (Redblackmap.mkDict cache_cmp : (int * int option, thm) Redblackmap.dict);

val Cell2_thms = Redblackmap.fromList Term.compare [(“CAnd”, Eval_CAnd),
                                                    (“COr”, Eval_COr),
                                                    (“CEqual”, Eval_CEqual)];

fun Redblackmap_member (m, k) =
 case Redblackmap.peek (m, k) of
   NONE => false
 | _ => true;

(* Assumes everything has been blasted to bools already *)
(* Trivial limitation for now: Might produce incorrect results for reg names that end with digits *)
fun boolify_inp nl cache inp =
 if is_ConstInp inp then let
  val b = inp |> dest_ConstInp |> dest_CBool
 in
  SPECL [b, nl] Eval_ConstInp
 end else if is_ExtInp inp then let
  val (var, idx) = dest_ExtInp inp
  val var' = var |> stringLib.fromHOLstring
 in
  if is_NoIndexing idx then
   Eval_ExtInp_NoIndexing |> SPECL [var, mk_var ("fext_" ^ var', bool), nl] |> UNDISCH_ALL
  else let
   val idx = dest_Indexing idx
   val idx' = idx |> dest_numeral |> Arbnumcore.toString
  in
   Eval_ExtInp_Indexing |> SPECL [var, idx, mk_var ("fext_" ^ var' ^ "_" ^ idx', bool), nl] |> UNDISCH_ALL
 end end else if is_VarInp inp then let
  val (var, idx) = dest_VarInp inp
  val idx = if is_NoIndexing idx then NONE else SOME (idx |> dest_Indexing |> int_of_term)
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
   val idx_prefix = case idx of NONE => "" | SOME idx => "_" ^ Int.toString idx
   val varname = mk_var ("net" ^ Int.toString n ^ idx_prefix, bool)
  in
   if Redblackmap_member (!eq_cache, (n, idx)) then
    Eval_refl_thm_for_NetVar |> SPECL [inp, varname, nl] |> UNDISCH
   else
    Redblackmap.find (cache, (n, idx))
  end else
   failwith "Unknown VarInp"
 end else
  failwith "Unknown cell input";

fun boolify_cell nl nl_distinct cache cellmem =
let
 val cell = cellmem |> concl |> dest_mem |> fst
 (*val () = print (term_to_string cell ^ "\n")*)
in
 if is_Cell1 cell then let
  val (t, out, in1) = dest_Cell1 cell
  val () = if t ~~ ``CNot`` then () else failwith "Non-neg 1-input cell?"
  val thm = MATCH_MP Eval_CNot nl_distinct(* |> UNDISCH*)
  val in1_thm = boolify_inp nl cache in1
  val thm = MATCH_MP thm (CONJ cellmem in1_thm)
  val cache = Redblackmap.insert (cache, (out |> int_of_term, NONE), thm)
 in
  cache
 end else if is_Cell2 cell then let
  val (t, out, in1, in2) = dest_Cell2 cell
  val t_thm = Redblackmap.find (Cell2_thms, t)
  val t_thm = MATCH_MP t_thm nl_distinct(* |> UNDISCH*)
  val in1_thm = boolify_inp nl cache in1
  val in2_thm = boolify_inp nl cache in2
  val thm = MATCH_MP t_thm (LIST_CONJ [cellmem, in1_thm, in2_thm])
  val cache = Redblackmap.insert (cache, (out |> int_of_term, NONE), thm)
 in
  cache
 end else if is_CellMux cell then let
  val (out, in1, in2, in3) = dest_CellMux cell
  val thm = MATCH_MP Eval_mux nl_distinct(* |> UNDISCH*)
  val ins = map (boolify_inp nl cache) [in1, in2, in3]
  val thm = MATCH_MP thm (LIST_CONJ (cellmem::ins))
  val cache = Redblackmap.insert (cache, (out |> int_of_term, NONE), thm)
 in
  cache
 end else if is_CellLUT cell then let
  val (out, ins, tb) = dest_CellLUT cell
  val thm = lookup (ins |> listSyntax.dest_list |> fst |> length) [(2, Eval_LUT2), (3, Eval_LUT3), (4, Eval_LUT4), (5, Eval_LUT5), (6, Eval_LUT6)]
  val thm = MATCH_MP thm nl_distinct(* |> UNDISCH*)
  val precond = ins |> dest_list |> fst |> map (boolify_inp nl cache) |> cons cellmem |> LIST_CONJ
  val thm = MATCH_MP thm precond
  val thm = CONV_RULE (RAND_CONV (REWRITE_CONV [gen_lut_cond_def, LIST_REL_def])) thm
  val cache = Redblackmap.insert (cache, (out |> int_of_term, NONE), thm)
 in
  cache
 end else if is_Carry4 cell then let
   val (out, cout, cin, lin, rin) = dest_Carry4 cell
   val thm = MATCH_MP Eval_Carry4 nl_distinct(* |> UNDISCH*)
   val precond = cellmem ::
                 (boolify_inp nl cache cin) ::
                 (lin |> dest_list |> fst |> map (boolify_inp nl cache)) @
                 (rin |> dest_list |> fst |> map (boolify_inp nl cache)) @
                 [mk_eq (out, cout) |> mk_neg |> EVAL_PROVE] |> LIST_CONJ
   val thm = MATCH_MP thm precond
   val [out0, out1, out2, out3, cout0, cout1, cout2, cout3] = CONJUNCTS thm

   val out = int_of_term out
   val cout = int_of_term cout
   val cache = Redblackmap.insert (cache, (out, SOME 0), out0)
   val cache = Redblackmap.insert (cache, (out, SOME 1), out1)
   val cache = Redblackmap.insert (cache, (out, SOME 2), out2)
   val cache = Redblackmap.insert (cache, (out, SOME 3), out3)
   val cache = Redblackmap.insert (cache, (cout, SOME 0), cout0)
   val cache = Redblackmap.insert (cache, (cout, SOME 1), cout1)
   val cache = Redblackmap.insert (cache, (cout, SOME 2), cout2)
   val cache = Redblackmap.insert (cache, (cout, SOME 3), cout3)
 in
  cache
 end else
  failwith "unknown cell"
end;

(* LEC eq infrastructure *)

fun cell_outputs cell =
 if is_Cell1 cell then let
  val (_, out, _) = dest_Cell1 cell
 in
  [out]
 end else if is_Cell2 cell then let
  val (_, out, _, _) = dest_Cell2 cell
 in
  [out]
 end else if is_CellMux cell then let
  val (out, _, _, _) = dest_CellMux cell
 in
  [out]
 end else if is_CellLUT cell then let
  val (out, _, _) = dest_CellLUT cell
 in
  [out]
 end else if is_Carry4 cell then let
   val (out, cout, _, _, _) = dest_Carry4 cell
 in
   [out, cout]
 end else
  failwith "Unknown cell?";

fun list_aconv [] [] = true
  | list_aconv [] (y::ys) = false
  | list_aconv (x::xs) [] = false
  | list_aconv (x::xs) (y::ys) = x ~~ y andalso list_aconv xs ys;

fun cell_input_eq_thm regs fextty nl nlnew inp =
 if is_ConstInp inp then let
  val b = inp |> dest_ConstInp |> dest_CBool
 in
  SPECL [regs, fextty, nl, nlnew, b] cell_inp_rel_ConstInp
 end else if is_ExtInp inp then let
  val (var, idx) = dest_ExtInp inp
  val var' = var |> stringLib.fromHOLstring
 in
  cell_inp_rel_ExtInp |> SPECL [regs, fextty, nl, nlnew, var, idx] |> EVAL_MP
 end else if is_VarInp inp then let
  val (var, idx) = dest_VarInp inp
  val idx = if is_NoIndexing idx then NONE else SOME (idx |> dest_Indexing |> int_of_term)
 in
  if is_RegVar var andalso (* should never have idx: *) not (isSome idx) then let
   val (reg, i) = var |> dest_RegVar
  in
   cell_inp_rel_VarInp_RegVar |> SPECL [regs, fextty, nl, nlnew, reg, i] |> EVAL_MP
  end else if is_NetVar var then let
   val n = var |> dest_NetVar |> int_of_term
  in
   Redblackmap.find (!eq_cache, (n, idx))
  end else
   failwith "Unknown VarInp"
 end else
  failwith "Unknown cell input";

val precond_ = ref (REFL arb);

(* val cellmem = c; val cellnewmem = cnew; *)
fun consume_unchanged_cell regs fextty nl nlnew nl_distinct nlnew_distinct cellmem cellnewmem = let
 val cell = cellmem |> concl |> dest_mem |> fst
in
 if is_CellLUT cell then let
  val (out, ins, tb) = dest_CellLUT cell
  val thm = lookup (ins |> listSyntax.dest_list |> fst |> length) [(2, cell_inp_rel_LUT2), (3, cell_inp_rel_LUT3), (4, cell_inp_rel_LUT4), (5, cell_inp_rel_LUT5), (6, cell_inp_rel_LUT6)]
  val ins_precond = ins |> dest_list |> fst |> map (cell_input_eq_thm regs fextty nl nlnew)
  val thm = MATCH_MP thm (LIST_CONJ ([nl_distinct, nlnew_distinct, cellmem, cellnewmem] @ ins_precond))
  val () = eq_cache := Redblackmap.insert (!eq_cache, (out |> int_of_term, NONE), thm)
 in
  ()
 end else if is_Carry4 cell then let
  val (out, cout, cin, lin, rin) = dest_Carry4 cell
  val precond = nl_distinct :: nlnew_distinct :: cellmem :: cellnewmem ::
                (cell_input_eq_thm regs fextty nl nlnew cin) ::
                (lin |> dest_list |> fst |> map (cell_input_eq_thm regs fextty nl nlnew)) @
                (rin |> dest_list |> fst |> map (cell_input_eq_thm regs fextty nl nlnew))
                |> LIST_CONJ
  val () = precond_ := precond
   val thm = MATCH_MP cell_inp_rel_Carry4 precond
   val [out0, out1, out2, out3, cout0, cout1, cout2, cout3] = CONJUNCTS thm

   val out = int_of_term out
   val cout = int_of_term cout
   val () = eq_cache := Redblackmap.insert (!eq_cache, (out, SOME 0), out0)
   val () = eq_cache := Redblackmap.insert (!eq_cache, (out, SOME 1), out1)
   val () = eq_cache := Redblackmap.insert (!eq_cache, (out, SOME 2), out2)
   val () = eq_cache := Redblackmap.insert (!eq_cache, (out, SOME 3), out3)
   val () = eq_cache := Redblackmap.insert (!eq_cache, (cout, SOME 0), cout0)
   val () = eq_cache := Redblackmap.insert (!eq_cache, (cout, SOME 1), cout1)
   val () = eq_cache := Redblackmap.insert (!eq_cache, (cout, SOME 2), cout2)
   val () = eq_cache := Redblackmap.insert (!eq_cache, (cout, SOME 3), cout3)
 in
  ()
 end else
  failwith "Unknown cell?"
end;

fun cleanup_cell_inp_rel nl nlnew th = let
 val hyps = hyp th
in
 if null hyps then
  th
 else let val h = hd hyps in
  if is_eq h (*is_cget_var h*) then
   cleanup_cell_inp_rel nl nlnew (th |> DISCH h |> GEN (h |> rhs |> rand |> rand)
                                     |> MATCH_MP cell_inp_rel_remove_tmp_RegVar
                                     |> EVAL_MP)
  else if is_fext_array h then
   cleanup_cell_inp_rel nl nlnew (th |> DISCH h |> GEN (h |> rand)
                                     |> MATCH_MP cell_inp_rel_remove_tmp_fext_array
                                     |> EVAL_MP)
  else if is_fext_bool h then
   cleanup_cell_inp_rel nl nlnew (th |> DISCH h |> GEN (h |> rand)
                                     |> MATCH_MP cell_inp_rel_remove_tmp_fext_bool
                                     |> EVAL_MP)
  else if is_Eval h then let
   val (h', arg0) = dest_comb h
   val (h', arg1) = dest_comb h'
   val (h', nlh) = dest_comb h'
   val nlh' = if nlh ~~ nl then nlnew else nl
   val h' = mk_comb(h', nlh')
   val h' = mk_comb(h', arg1)
   val h' = mk_comb(h', arg0)

   (* Copied code: *)
   val (var, idx) = dest_VarInp arg1
   val idx = if is_NoIndexing idx then NONE else SOME (idx |> dest_Indexing |> int_of_term)
   val n = var |> dest_NetVar |> int_of_term

   val thm = Redblackmap.find (!eq_cache, (n, idx))
  in
   cleanup_cell_inp_rel nl nlnew (th |> DISCH h' |> DISCH h |> GEN arg0
                                     |> MATCH_MP (MATCH_MP cell_inp_rel_remove_tmp_NetVar thm))
  end else
   failwith "Unknown assumption"
 end
end;

fun consume_changed_cell regs fextty nl nlnew cache cachenew cell = let
 val (out, _, _) = dest_CellLUT cell
 val out = out |> int_of_term

 val nl_thm = Redblackmap.find (cache, (out, NONE))
 val nlnew_thm = Redblackmap.find (cachenew, (out, NONE))
 val th = MATCH_MP (SPECL [regs, fextty] Eval_Eval_cell_inp_rel) (CONJ nl_thm nlnew_thm)

 val precond = th |> concl |> lhand |> minisatProve.SAT_PROVE;
 val th = MP th precond;

 val th = cleanup_cell_inp_rel nl nlnew th

 val () = eq_cache := Redblackmap.insert (!eq_cache, (out, NONE), th)
in
 ()
end;

fun consume_cells regs fextty nl nlnew nl_distinct nlnew_distinct cache cachenew
                  (c::cells) (cnew::cellsnew) = let
     val c_cell = c |> concl |> dest_mem |> fst
     val cnew_cell = cnew |> concl |> dest_mem |> fst
     (*val () = print ("---\n" ^ term_to_string c_cell ^ "\nvs.\n" ^ term_to_string cnew_cell ^ "\n");*)
    in
     if list_aconv (cell_outputs cnew_cell) (cell_outputs c_cell) then
      if cnew_cell ~~ c_cell then
       (* unchanged by tech mapping *)
       (consume_unchanged_cell regs fextty nl nlnew nl_distinct nlnew_distinct c cnew;
        consume_cells regs fextty nl nlnew nl_distinct nlnew_distinct cache cachenew cells cellsnew)
      else let
       (* boolify both cells *)
       val cache = boolify_cell nl nl_distinct cache c
       val cachenew = boolify_cell nlnew nlnew_distinct cachenew cnew
      in
       (* sat prove them equal *)
       (consume_changed_cell regs fextty nl nlnew cache cachenew cnew_cell;
        consume_cells regs fextty nl nlnew nl_distinct nlnew_distinct cache cachenew cells cellsnew)
     end else let
       (* boolify old cell only to sync *)
       val cache = boolify_cell nl nl_distinct cache c
     in
       consume_cells regs fextty nl nlnew nl_distinct nlnew_distinct cache cachenew cells (cnew::cellsnew)
     end
    end
  | consume_cells _ _ _ _ _ _ _ _ [] (cnews::cellsnew) = failwith "Old netlist ended too early?"
  | consume_cells _ _ _ _ _ _ _ _ _ [] = ();

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

fun lec extenv_def outs_def regs_def nl_def nlnew_def = let
 val extenv = extenv_def |> concl |> lhs;
 val outs = outs_def |> concl |> lhs;
 val regs = regs_def |> concl |> lhs;
 val nl = nl_def |> concl |> lhs;
 val nlnew = nlnew_def |> concl |> lhs;

 val nl_distinct = prove_ALL_DISTINCT_FLAT_MAP_cell_output nl_def;
 val nlnew_distinct = prove_ALL_DISTINCT_FLAT_MAP_cell_output nlnew_def;

 val cells = MATCH_MP all_mems nl_def
             |> PURE_REWRITE_RULE [EVERY_MEM_compute]
             |> CONJUNCTS |> butlast; (* last element is always T *)
 val cellsnew = MATCH_MP all_mems nlnew_def
              |> PURE_REWRITE_RULE [EVERY_MEM_compute]
              |> CONJUNCTS |> butlast; (* last element is always T *)

 val () = eq_cache := Redblackmap.mkDict cache_cmp;
 val cache = (Redblackmap.mkDict cache_cmp : (int * int option, thm) Redblackmap.dict);
 val cachenew = cache;

 (* Build corrs *)

 val () = consume_cells regs extenv nl nlnew nl_distinct nlnew_distinct cache cachenew cells cellsnew;

 (* Glue corrs together *) 
 
 val th = SPECL [extenv, outs, regs, nl, nlnew] circuit_run_cong
 val th = EVAL_MP th

 fun inp_to_cache_key (VarInp (NetVar n, idx)) = (n, idx)
 (* set_goal ([], th |> concl |> lhand) *)

 fun cell_inp_run_eq_tac (asm, g) = let
  val inp_key = g |> strip_forall |> snd |> rand |> extract_cell_input |> inp_to_cache_key
  (*val inp_key_str = (inp_key |> fst |> Int.toString) ^ (case inp_key |> snd of
                                                          NONE => ""
                                                        | SOME idx => "[" ^ Int.toString idx ^ "]")
  val () = print ("Proving input " ^ inp_key_str ^ " eqv.\n")*)
 in
  MATCH_ACCEPT_TAC (Redblackmap.find (!eq_cache, inp_key))
 end (asm, g)
 val precond = prove(th |> concl |> lhand,
                     CONV_TAC (RAND_CONV (REWRITE_CONV [regs_def])) \\
                     rewrite_tac [EVERY_DEF, reg_inp_rel_trivial] \\ rpt conj_tac \\
                     match_mp_tac cell_inp_rel_reg_inp_rel \\ simp [] \\ cell_inp_run_eq_tac)
 val th = MP th precond

 val precond = prove(th |> concl |> lhand,
                     CONV_TAC (RAND_CONV (REWRITE_CONV [outs_def])) \\
                     rewrite_tac [EVERY_DEF] \\ rpt conj_tac \\
                     match_mp_tac cell_inp_rel_out_inp_rel \\ simp [] \\ rpt conj_tac \\ cell_inp_run_eq_tac)
 val th = MP th precond

 val () = print "Validating tech. mapped netlist...\n"
 val th = EVAL_MP th
in
 th
end;

end
