structure RTLPrintLib =
struct

open hardwarePreamble;

open RTLSyntax;

open SMLRTLLib;

datatype cell2 = CAnd | COr | CEqual;

datatype cell = CellNot of (int * cell_input)
              | Cell2 of (cell2 * int * cell_input * cell_input);

fun extract_bool tm =
 if tm ~~ T then
  true
 else if tm ~~ F then
  false
 else
  failwith "Not a constant bool?";

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

fun print_type tm =
 if is_CBool_t tm then
  "logic"
 else if is_CArray_t tm then let
  val dim = tm |> dest_CArray_t |> dest_numeral |> Arbnumcore.less1
 in
  "logic[" ^ (Arbnumcore.toString dim) ^ ":0]"
 end else
  failwith "Unknown type: " ^ (term_to_string tm);

fun print_bool b = if b then "1'b1" else "1'b0";

val print_CBool = print_bool o extract_bool o rand;

fun print_var (RegVar (reg, i)) = reg ^ Int.toString i
  | print_var (NetVar n) = "w" ^ Int.toString n;

fun print_idx (SOME idx) = "[" ^ Int.toString idx ^ "]"
  | print_idx NONE = "";

fun print_cell_input (ConstInp b) = print_bool b
  | print_cell_input (ExtInp (var, idx)) = var ^ (print_idx idx)
  | print_cell_input (VarInp (var, idx)) = (print_var var) ^ (print_idx idx);

fun print_extenv extenv = let
 fun print_extenv' entry = let
  val (var, ty) = entry |> pairSyntax.dest_pair
 in
  " input " ^ print_type ty ^ " " ^ stringSyntax.fromHOLstring var ^ ",\n"
 end
 val extenv = extenv |> dest_list |> fst
in
 map print_extenv' extenv |> concat
end;

fun print_outs outs = let
 fun print_out (var, inp) =
  if is_OutInp inp then
   " output logic " ^ (stringSyntax.fromHOLstring var)
  else let
   val len = inp |> dest_OutInps |> dest_list |> fst |> length
  in
   " output logic[" ^ Int.toString (len - 1) ^ ":0] " ^ (stringSyntax.fromHOLstring var)
  end
 val outs = outs |> dest_list |> fst |> map pairSyntax.dest_pair
in
 map print_out outs |> String.concatWith ",\n"
end;

fun print_outs_assign outs = let
 fun print_out (var, inp) =
  if is_OutInp inp then let
   val inp = inp |> dest_OutInp |> extract_cell_input |> print_cell_input
  in
   "assign " ^ (stringSyntax.fromHOLstring var) ^ " = " ^ inp ^ ";\n"
  end else let
   val inp = inp |> dest_OutInps |> dest_list |> fst
                 |> map (print_cell_input o extract_cell_input) |> String.concatWith ", "
  in
   "assign " ^ (stringSyntax.fromHOLstring var) ^ " = {" ^ inp ^ "};\n"
  end

  val outs = outs |> dest_list |> fst |> map pairSyntax.dest_pair
in
 map print_out outs |> concat
end;

fun print_wires nl = let
 fun print_wires' (CellNot (out, _)) = "logic w" ^ Int.toString out ^ ";\n"
   | print_wires' (Cell2 (_, out, _, _)) = "logic w" ^ Int.toString out ^ ";\n"
in
 map print_wires' nl |> concat
end;

fun print_regs regs = let
 fun print_reg (regi, rdata) = let
  val (reg, i) = pairSyntax.dest_pair regi
  (* Could sanity-check ty here... *)
  val reg = stringSyntax.fromHOLstring reg ^ term_to_string i
  val rdata = rdata |> TypeBase.dest_record |> snd
  val v = lookup "init" rdata |> optionSyntax.dest_some |> print_CBool
  val inp = lookup "inp" rdata;
 in
  "logic " ^ reg ^ " = " ^ v ^ ";\n" ^
  "always_ff @(posedge clk) " ^ reg ^ " <= " ^
  (if optionSyntax.is_some inp then
   inp |> optionSyntax.dest_some |> extract_cell_input |> print_cell_input
  else
   "1'b0") ^ ";\n\n"
 end
 val regs = regs |> dest_list |> fst |> map pairSyntax.dest_pair
in
 map print_reg regs |> concat
end;

fun pow n m =
 if m <= 0 then
  1
 else
  n * pow n (m - 1);

fun print_cell2 cell2 =
 case cell2 of
   CAnd => "and"
 | COr => "or"
 | CEqual => "xnor" (* note! called xnor! *)

fun print_cell (CellNot (out, inp)) = let
  val wire = "w" ^ Int.toString out
  val inp = print_cell_input inp
 in
  "not not_" ^ wire ^ "(" ^ wire ^ ", "  ^ inp ^ ");\n"
 end

| print_cell (Cell2 (cell2, out, lhs, rhs)) = let
   val cell2 = print_cell2 cell2
   val wire = "w" ^ Int.toString out
   val lhs = print_cell_input lhs
   val rhs = print_cell_input rhs
  in
   cell2 ^ " " ^ cell2 ^ "_" ^ Int.toString out ^ "(" ^ wire ^ ", " ^ lhs ^ ", " ^ rhs ^ ");\n"
  end;

val print_nl = concat o map print_cell;

(* TODO: Need to check that wire names do not collide with reg names *)
fun print_Circuit tm = let
 val (extenv, outs, regs, nl_combs, nl_ffs) = dest_Circuit tm
 val nl_combs = extract_netlist nl_combs
 val nl_ffs = extract_netlist nl_ffs
 val has_regs = listSyntax.is_cons regs
in
 "module Circuit(\n" ^
 (if has_regs then " input clk,\n" else "") ^
 print_extenv extenv ^
 (* todo: print correctly if outs empty... but on the other hand, do we ever have no outputs? *)
 print_outs outs ^
 ");\n\n" ^
 
 print_wires nl_combs ^
 print_wires nl_ffs ^
 "\n" ^

 print_regs regs ^

 print_outs_assign outs ^
 "\n" ^

 print_nl nl_combs ^
 print_nl nl_ffs ^
 "endmodule\n"
end;

end
