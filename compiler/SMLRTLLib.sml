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

datatype cell = Cell1 of (int * cell_input) (* <-- no "cell1" type currently, only have inv currently *)
              | Cell2 of (cell2 * int * cell_input * cell_input)
              | CellMux of (int * cell_input * cell_input * cell_input)
              | AlreadyMappedCell of (int list) * (cell_input list) * term; (* <-- for cells mapped previously *)

fun cell_output (Cell1 (out, _)) = [out]
  | cell_output (Cell2 (_, out, _, _)) = [out]
  | cell_output (CellMux (out, _, _, _)) = [out]
  | cell_output (AlreadyMappedCell (outs, _, _)) = outs;

fun cell_inputs (Cell1 (_, inp1)) = [inp1]
  | cell_inputs (Cell2 (_, _, inp1, inp2)) = [inp1, inp2]
  | cell_inputs (CellMux (_, inp1, inp2, inp3)) = [inp1, inp2, inp3]
  | cell_inputs (AlreadyMappedCell (_, ins, _)) = ins;

fun get_cell_input_num (VarInp (NetVar n, _)) = SOME n
  | get_cell_input_num _ = NONE;

fun AlreadyMappedCell_term (AlreadyMappedCell (outs, ins, tm)) = tm;

(* Simple RLT bool-only semantics on SML level -- could also use (existing) in-logic sem, but that would probably be too slow... *)
fun rtl_cell_input_sem env (ConstInp b) = b
  | rtl_cell_input_sem env (ExtInp e) = Redblackmap.find (env, ExtInp e)
  | rtl_cell_input_sem env (VarInp i) = Redblackmap.find (env, VarInp i);

fun rtl_cell_sem env (Cell1 (out, inp1)) = let
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
    end
  | rtl_cell_sem env (CellMux (out, inp1, inp2, inp3)) = let
     val inp1 = rtl_cell_input_sem env inp1
     val inp2 = rtl_cell_input_sem env inp2
     val inp3 = rtl_cell_input_sem env inp3
     val v = if inp1 then inp2 else inp3
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
 if optionSyntax.is_some t then
  t |> optionSyntax.dest_some |> int_of_term |> SOME
 else
  NONE;

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
fun extract_cell2 t =
 if t ~~ ``CAnd`` then
  CAnd
 else if t ~~ ``COr`` then
  COr
 else if t ~~ ``CEqual`` then
  CEqual
 else
  failwith "not implemented: cell2";

fun extract_cell cell =
 if is_Cell1 cell then let
  val (t, out, in1) = dest_Cell1 cell
 in
   Cell1 (int_of_term out, extract_cell_input in1)
 end else if is_Cell2 cell then let
  val (t, out, in1, in2) = dest_Cell2 cell
 in
  Cell2 (extract_cell2 t, int_of_term out, extract_cell_input in1, extract_cell_input in2)
 end else if is_CellMux cell then let
  val (out, in1, in2, in3) = dest_CellMux cell
 in
  CellMux (int_of_term out, extract_cell_input in1, extract_cell_input in2, extract_cell_input in3)
 end else if is_CellLUT cell then let
  val (out, ins, tb) = dest_CellLUT cell
  val out = int_of_term out
  val ins = ins |> dest_list |> fst
  val ins = map extract_cell_input ins
 in
  AlreadyMappedCell ([out], ins, cell)
 end else if is_Carry4 cell then let
  val (out, cout, cin, lhs, rhs) = dest_Carry4 cell
  val out = int_of_term out
  val cout = int_of_term cout
  val cin = extract_cell_input cin
  val lhs = lhs |> dest_list |> fst |> map extract_cell_input
  val rhs = rhs |> dest_list |> fst |> map extract_cell_input
 in
  AlreadyMappedCell ([out, cout], cin::lhs@rhs, cell)
 end else
  failwith "not implemented: cell";

fun extract_netlist nl = let
 val nl = fst (dest_list nl)
in
 map extract_cell nl
end;

fun extract_required_po reg = let
 val inp = reg |> pairSyntax.spine_pair |> last
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

fun extract_required_pos regs = dest_list regs |> fst |> flatMap extract_required_po |> dedup;

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
