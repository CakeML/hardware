structure SMLRTLLib =
struct

open hardwarePreamble;

open listSyntax RTLSyntax;

datatype var = RegVar of string * int
             | NetVar of int;

datatype cell_input = ConstInp of bool (* <-- we know that we only have bool inputs when doing tech map level things *)
                    | ExtInp of string * (int option)
                    | VarInp of var * (int option);

datatype cell2 = CAnd | COr | CEqual;

datatype cell = CellNot of (int * cell_input)
              | Cell2 of (cell2 * int * cell_input * cell_input)
              | CellDuplicate_Left2DownAndRight
              | CellRotate_Down2Right;

(*datatype cell2 = CAnd | COr | CEqual;

datatype cell = Cell1 of (int * cell_input) (* <-- no "cell1" type currently, only have inv currently *)
              | Cell2 of (cell2 * int * cell_input * cell_input)
              | CellMux of (int * cell_input * cell_input * cell_input)
              | AlreadyMappedCell of (int list) * (cell_input list) * term; (* <-- for cells mapped previously *)*)

fun cell_output (CellNot (out, _)) = out
  | cell_output (Cell2 (_, out, _, _)) = out;

fun cell_inputs (CellNot (_, inp1)) = [inp1]
  | cell_inputs (Cell2 (_, _, inp1, inp2)) = [inp1, inp2];

fun get_cell_input_num (VarInp (NetVar n, _)) = SOME n
  | get_cell_input_num _ = NONE;

(*fun AlreadyMappedCell_term (AlreadyMappedCell (outs, ins, tm)) = tm;*)

(* Simple RLT bool-only semantics on SML level -- could also use (existing) in-logic sem, but that would probably be too slow... *)
fun rtl_cell_input_sem env (ConstInp b) = b
  | rtl_cell_input_sem env (ExtInp e) = Redblackmap.find (env, ExtInp e)
  | rtl_cell_input_sem env (VarInp i) = Redblackmap.find (env, VarInp i);

fun rtl_cell_sem env (CellNot (out, inp1)) = let
     val inp1 = rtl_cell_input_sem env inp1
     val v = not inp1
    in
     Redblackmap.insert (env, VarInp (NetVar out, NONE), v)
    end
  | rtl_cell_sem env (Cell2 (ct, out, inp1, inp2)) = let
     val inp1 = rtl_cell_input_sem env inp1
     val inp2 = rtl_cell_input_sem env inp2
     val v = case ct of
               CAnd => inp1 andalso inp2
             | COr => inp1 orelse inp2
             | CEqual => (inp1 = inp2)
    in
     Redblackmap.insert (env, VarInp (NetVar out, NONE), v)
    end;

fun rtl_sem env [] = env
  | rtl_sem env (c::cs) = rtl_sem (rtl_cell_sem env c) cs;

(** Convenience **)

fun flatMap f [] = []
  | flatMap f (x::xs) = 
     case f x of
       NONE => flatMap f xs
     | SOME x' => x' :: flatMap f xs;

(** Extract (non-tech.-mapped) HOL netlist to SML netlist **)

fun extract_var t =
 if is_RegVar t then let
  val (reg, i) = dest_RegVar t
  val reg = stringSyntax.fromHOLstring reg
  val i = int_of_term i in
   RegVar (reg, i)
 end else if is_NetVar t then
  t |> dest_NetVar |> int_of_term |> NetVar
 else
  failwith "not a var";

fun extract_input_idx t =
 if is_NoIndexing t then
  NONE
 else if is_Indexing t then
  t |> dest_Indexing |> int_of_term |> SOME
 else
  failwith "unknown/unexpected cell input index";

fun extract_cell_input t =
 if is_ConstInp t then
  ConstInp ((t |> dest_ConstInp |> dest_CBool) ~~ T)
 else if is_ExtInp t then let
  val (var, idx) = dest_ExtInp t
  val var = stringSyntax.fromHOLstring var
  val idx = extract_input_idx idx in
   ExtInp (var, idx)
 end else if is_VarInp t then let
  val (var, idx) = dest_VarInp t
  val var = extract_var var
  val idx = extract_input_idx idx in
   VarInp (var, idx)
 end else
  failwith "not implemented: extract_cell_input";

(* TODO: NOT COMPLETE/CORRECT *)
fun extract_cell2 tm =
 if tm ~~ CAnd_tm then
  CAnd
 else if tm ~~ COr_tm then
  COr
 else if tm ~~ CEqual_tm then
  CEqual
 else
  failwith "Not a cell2?";

fun extract_cell cell =
 if is_Cell1 cell then let
  val (_, out, inp) = dest_Cell1 cell
  val out = int_of_term out
  val inp = extract_cell_input inp
 in
  CellNot (out, inp)
 end else if is_Cell2 cell then let
  val (cellt, out, lhs, rhs) = dest_Cell2 cell
  val cellt = extract_cell2 cellt
  val out = int_of_term out
  val lhs = extract_cell_input lhs
  val rhs = extract_cell_input rhs
 in
  Cell2 (cellt, out, lhs, rhs)
 end else
  failwith ("Illegal cell: " ^ term_to_string cell);

fun extract_netlist nl = let
 val nl = fst (dest_list nl)
in
 map extract_cell nl
end;

fun extract_required_out_po out = let
 val out_inp = out |> pairSyntax.dest_pair |> snd
 val out_inps = if is_OutInp out_inp then
                 [out_inp |> dest_OutInp]
                else
                  out_inp |> dest_OutInps |> dest_list |> fst
in
 out_inps |> flatMap (fn inp => case extract_cell_input inp of
                                    VarInp (NetVar n, _) => SOME n
                                  | _ => NONE)
end;

fun extract_required_reg_po reg = let
 val rdata = reg |> pairSyntax.dest_pair |> snd |> TypeBase.dest_record |> snd
 val inp = lookup "inp" rdata
in
 if optionSyntax.is_some inp then
  case (inp |> optionSyntax.dest_some |> extract_cell_input) of
    VarInp (NetVar n, _) => SOME n
  | _ => NONE
 else
  NONE
end;

fun dedup [] = []
  | dedup (x::xs) = x :: dedup (filter (curry (op <>) x) xs);

fun extract_required_pos outs regs = let
 val out_pos = dest_list outs |> fst |> map extract_required_out_po |> flatten
 val reg_pos = dest_list regs |> fst |> flatMap extract_required_reg_po
in
 dedup (out_pos @ reg_pos)
end;

(** Other convenient functions **)

fun all_binary_numbers len = 
 if len = 0 then
  [[]]
 else let
  val nums = all_binary_numbers (len - 1)
 in
  map (cons false) nums @ map (cons true) nums
 end;

end
