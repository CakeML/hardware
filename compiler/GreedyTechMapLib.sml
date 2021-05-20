structure GreedyTechMapLib =
struct

open hardwarePreamble;
open sumExtraTheory RTLTheory;

open SMLRTLLib;

open RTLSyntax;

(* Width of LUTs to map to, 7 series FPGAs has k = 6 *)
val k = 6;

datatype cover = Cover of cell list
               | CoverAlreadyMappedCell of cell (* cell is always AlreadyMappedCell here *);

fun is_cover (Cover _) = true
  | is_cover (CoverAlreadyMappedCell _) = false;

fun cover_size (Cover nl) = length nl
  | cover_size (CoverAlreadyMappedCell _) = 1;

fun cover_snoc cell (Cover nl) = Cover (nl @ [cell])
  | cover_snoc cell1 (CoverAlreadyMappedCell cell2) = CoverAlreadyMappedCell cell2;

fun cover_output (Cover nl) = flatten (map cell_output nl)
  | cover_output (CoverAlreadyMappedCell cell) = cell_output cell;

fun get_covers inp covers =
 case inp of
   VarInp (NetVar n, _) => lookup n covers
 | _ => [];

(* Only non-internal inputs *)
fun get_inputs nl = let
 fun is_netvar_in outs (VarInp (NetVar n, _)) = mem n outs
   | is_netvar_in _ _ = false
 val outputs = map cell_output nl |> flatten
in
 nl |> map cell_inputs |> flatten |> filter (not o is_netvar_in outputs)
end;

(* Only non-internal inputs *)
fun cover_inputs (Cover nl) = get_inputs nl
  | cover_inputs (CoverAlreadyMappedCell cell) = cell_inputs cell;

fun filter_larger_than_k_covers covers = filter (fn cov => length (cover_inputs cov) <= k) covers;

fun prod_of_covers covs1 covs2 = let
 fun prod_of_cover (Cover nl1) (Cover nl2) = Cover (nl1 @ nl2)
 fun prod_of_covers' [] _ = []
   | prod_of_covers' (cov1::covs1) covs2 =
     filter_larger_than_k_covers (map (fn cov => prod_of_cover cov1 cov) covs2) @ prod_of_covers' covs1 covs2
in
 prod_of_covers' (Cover [] :: covs1) (Cover [] :: covs2)
end;

fun largest_cover covers = let
 fun largest_cover' [] best = best
   | largest_cover' (cov::covs) best =
      if cover_size cov > cover_size best then
       largest_cover' covs cov
      else
       largest_cover' covs best
in
 case covers of
   [] => failwith "no covers?" (* should never happen *)
 | (cov::covs) => largest_cover' covs cov
end;

(* Will just die with an exception if we do not visit cells in order... *)
fun gen_cover c covers =
 case c of
   Cell1 (out, inp1) => (case filter is_cover (get_covers inp1 covers) of
                           [] => [Cover [c]]
                           (* we know that we will never want to select only a 1-input cell if there are cells
                              before this cell, as the number of inputs is not be increased by the 1-input
                              cell *)
                         | covs => map (cover_snoc c) covs)
 | Cell2 (_, out, inp1, inp2) => let
  val covs1 = filter is_cover (get_covers inp1 covers)
  val covs2 = filter is_cover (get_covers inp2 covers)
  val covs = prod_of_covers covs1 covs2
  val covs = map (cover_snoc c) covs
  val covs = filter_larger_than_k_covers covs
  (* be greedy for now: *) val covs = [largest_cover covs]
 in
  covs
 end
 | CellMux (out, inp1, inp2, inp3) => let
  val covs1 = filter is_cover (get_covers inp1 covers)
  val covs2 = filter is_cover (get_covers inp2 covers)
  val covs3 = filter is_cover (get_covers inp3 covers)
  val covs = prod_of_covers covs1 (prod_of_covers covs2 covs3)
  val covs = map (cover_snoc c) covs
  val covs = filter_larger_than_k_covers covs
  (* be greedy for now: *) val covs = [largest_cover covs]
 in
  covs
 end
 | AlreadyMappedCell (outs, ins, tm) => AlreadyMappedCell (outs, ins, tm) |> CoverAlreadyMappedCell |> sing;

fun gen_covers nl = let
 fun gen_covers' [] nlnum nlorder covers = (nlorder, covers)
   | gen_covers' (c :: cs) nlnum nlorder covers = let
     val cover = gen_cover c covers
    in
     gen_covers' cs (nlnum + 1)
                 (map (fn out => (out, nlnum)) (cell_output c) @ nlorder)
                 (map (fn out => (out, cover)) (cell_output c) @ covers)
    end
in
 gen_covers' nl 0 [] []
end;

(* Cover selection *)

fun sort_in_rev_nlorder nlorder l =
 l |> map (fn n => (n, lookup n nlorder)) |> sort (fn (_, o1) => fn (_, o2) => o1 > o2) |> map fst;

fun rem x l = filter (fn e => e <> x) l;

(* required_pos = note that these must be in reverse netlist order *)
(* selected_covers = assoc list from outputs to covers (int -> option cover) *)
fun select_covers nlorder required_pos all_covers selected_covers =
 case required_pos of
   [] => selected_covers
 | (po::pos) =>
   case lookup_opt po selected_covers of
     NONE => (* new cover needed *) let
      val cov = all_covers |> lookup po |> largest_cover
      val new_pos = cov |> cover_inputs |> flatMap get_cell_input_num
      val new_pos = sort_in_rev_nlorder nlorder (new_pos @ pos)
      val outs = cover_output cov
      val selected_covers = (po, SOME cov) :: map (fn out => (out, NONE)) (rem po outs) @ selected_covers
     in
      select_covers nlorder new_pos all_covers selected_covers
     end
   | SOME _ => (* already covered *)
      select_covers nlorder pos all_covers selected_covers;

(** Derive LUT from small netlist **)

fun bool_compare (false, false) = EQUAL
  | bool_compare (false, true) = LESS
  | bool_compare (true, false) = GREATER
  | bool_compare (true, true) = EQUAL;

fun lex_compare cmp1 cmp2 ((e11, e12), (e21, e22)) =
 let val r = cmp1 (e11, e21) in if r = EQUAL then cmp2 (e12, e22) else r end;

fun var_compare (RegVar r1, RegVar r2) = lex_compare String.compare Int.compare (r1, r2)
  | var_compare (RegVar _, NetVar _) = LESS
  | var_compare (NetVar _, RegVar _) = GREATER
  | var_compare (NetVar in1, NetVar in2) = Int.compare (in1, in2);

fun option_compare cmp (NONE, NONE) = EQUAL
  | option_compare cmp (NONE, SOME x) = LESS
  | option_compare cmp (SOME x, NONE) = GREATER
  | option_compare cmp (SOME x, SOME y) = cmp (x, y);

fun cell_input_compare (ConstInp b1, ConstInp b2) = bool_compare (b1, b2)
  | cell_input_compare (ConstInp _, _) = LESS

  | cell_input_compare (ExtInp _, ConstInp _) = GREATER
  | cell_input_compare (ExtInp e1, ExtInp e2) = lex_compare String.compare (option_compare Int.compare) (e1, e2)
  | cell_input_compare (ExtInp _, _) = LESS
                                          
  | cell_input_compare (VarInp _, ConstInp _) = GREATER
  | cell_input_compare (VarInp _, ExtInp _) = GREATER
  | cell_input_compare (VarInp i1, VarInp i2) = lex_compare var_compare (option_compare Int.compare) (i1, i2);

fun build_env [] [] = Redblackmap.mkDict cell_input_compare
  | build_env [] vals = failwith "uneven build_env lists"
  | build_env ins [] = failwith "uneven build_env lists"
  | build_env (i::is) (v::vs) = Redblackmap.insert (build_env is vs, i, v);
(*| build_env (i::is) (v::vs) = (case i of
      ConstInp _ => build_env is vs
    | VarInp i => Redblackmap.insert (build_env is vs, i, v));*)

fun simulate_with_input ins ins_v nl out = let 
 val env = build_env ins ins_v
in
 Redblackmap.find (rtl_sem env nl, VarInp (NetVar out, NONE))
end;

(* hide ugly lift_bool in boolSyntax *)
fun lift_bool true = T
  | lift_bool false = F

fun build_var (RegVar (reg, i)) = mk_RegVar (stringSyntax.fromMLstring reg, term_of_int i)
  | build_var (NetVar n) = n |> term_of_int |> mk_NetVar;

val none_tm_int = optionSyntax.none_tm |> inst [ alpha |-> numSyntax.num ];

fun build_idx NONE = NoIndexing_tm
  | build_idx (SOME idx) = idx |> term_of_int |> mk_Indexing;

fun build_cell_input (ConstInp b) = b |> lift_bool |> mk_CBool |> mk_ConstInp
  | build_cell_input (ExtInp (var, idx)) = mk_ExtInp (stringSyntax.fromMLstring var, build_idx idx)
  | build_cell_input (VarInp (var, idx)) = mk_VarInp (build_var var, build_idx idx);

fun build_lut_table nl out = let
 val ins = nl |> get_inputs
 val ins_vs = ins |> length |> all_binary_numbers
 val table = flatMap (fn ins_v => if simulate_with_input ins ins_v nl out then SOME ins_v else NONE) ins_vs
 val table = map (fn vs => listSyntax.mk_list (map lift_bool vs, bool)) table
 val table = listSyntax.mk_list (table, listSyntax.mk_list_type bool)
in
 mk_CellLUT (numSyntax.term_of_int out, listSyntax.mk_list (map build_cell_input ins, cell_input_ty), table)
end;

fun selected_covers_build_luts [] = []
  | selected_covers_build_luts ((out, NONE) :: cs) = selected_covers_build_luts cs
  | selected_covers_build_luts ((out, SOME (Cover nl)) :: cs) = build_lut_table nl out :: selected_covers_build_luts cs
  | selected_covers_build_luts ((out, SOME (CoverAlreadyMappedCell c)) :: cs) = AlreadyMappedCell_term c :: selected_covers_build_luts cs;

fun build_lut_nl selected_covers = let
 val cells = selected_covers_build_luts selected_covers
in
 listSyntax.mk_list (cells, cell_ty)
end;

(* Top-level entry point: Expects a (blasted) circuit term as input *)
fun greedy_tech_map circuit = let
 val (_, outs, regs, nl, _) = dest_Circuit circuit
 val nl = extract_netlist nl
 val (nlorder, covers) = gen_covers nl
 val pos = extract_required_pos outs regs
 val pos = sort_in_rev_nlorder nlorder pos
 val selected_covers = select_covers nlorder pos covers []
in
 build_lut_nl selected_covers
end;

(*
(* Test 1 *)
val testcovers1 =
 gen_covers [Cell2 (CAnd, 0, VarInp (RegVar "a"), VarInp (RegVar "b")),
             Cell2 (CAnd, 1, VarInp (RegVar "c"), VarInp (RegVar "d")),
             Cell2 (CAnd, 2, VarInp (NetVar 0), VarInp (NetVar 1)),
             Cell2 (COr, 3, VarInp (NetVar 2), VarInp (NetVar 2))] [];
(*             Cell1 (3, VarInp (NetVar 2))] [];*)

val best_covers = select_covers [3, 0] testcovers1 [];
val best_covers = map (fn covs => (fst covs, sort (fn cov1 => fn cov2 => cell_output cov1 <= cell_output cov2) (snd covs))) best_covers;

(* Test 2 *)
val testcovers2 =
 gen_covers [Cell2 (0, VarInp (RegVar "A"), VarInp (RegVar "B")),
             Cell2 (1, VarInp (RegVar "C"), VarInp (RegVar "D")),
             Cell2 (2, VarInp (RegVar "D"), VarInp (RegVar "E")),

             Cell2 (3, VarInp (NetVar 0), VarInp (NetVar 1)),
             Cell2 (4, VarInp (NetVar 2), VarInp (NetVar 2)),

             Cell2 (5, VarInp (NetVar 3), VarInp (NetVar 4)),

             Cell1 (6, VarInp (NetVar 5))] [];

select_covers [6, 4, 3] testcovers2 [];

(* Test 3 *)
val nl_sml = extract_netlist nl;
val testcovers3 = gen_covers nl_sml [];

val best_covers = select_covers [100] testcovers3 [];
val best_covers = map (fn covs => (fst covs, sort (fn cov1 => fn cov2 => cell_output cov1 <= cell_output cov2) (snd covs))) best_covers;

(* Test with compiler output *)

val nl = ``[Cell2 CAnd 0 (VarInp (RegVar "in1")) (VarInp (RegVar "in2"));
            Cell2 COr 1 (VarInp (RegVar "in1")) (VarInp (RegVar "in2"));
            Cell1 CNot 2 (VarInp (NetVar 0));
            Cell1 CNot 3 (VarInp (NetVar 1));
            CellMux 4 (VarInp (RegVar "inv")) (VarInp (NetVar 3)) (VarInp (NetVar 1));
            CellMux 5 (VarInp (RegVar "inv")) (VarInp (NetVar 2)) (VarInp (NetVar 0))]``;

val nl_sml = extract_netlist nl;

val testcovers = gen_covers nl_sml [];
val best_covers = select_covers [5, 4] testcovers [];
val best_covers = map (fn covs => (fst covs, sort (fn cov1 => fn cov2 => cell_output cov1 <= cell_output cov2) (snd covs))) best_covers;

val regs = ``[("a", VarInp (NetVar 5)); ("b", VarInp (NetVar 4))]``;
*)

end
