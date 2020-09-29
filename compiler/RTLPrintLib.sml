structure RTLPrintLib =
struct

open hardwarePreamble;

open RTLSyntax;

open SMLRTLLib;

datatype cell = CellLUT of (int * cell_input list * bool list list)
              | Carry4 of (int * int * cell_input * cell_input list * cell_input list);

fun extract_bool tm =
 if tm ~~ T then
  true
 else if tm ~~ F then
  false
 else
  failwith "Not a constant bool?";

fun extract_cell cell =
 if is_CellLUT cell then let
  val (out, ins, tb) = dest_CellLUT cell
  val out = int_of_term out
  val ins = ins |> dest_list |> fst
  val ins = map extract_cell_input ins
  val extract_tb_entry = (map extract_bool) o fst o dest_list
  val tb = tb |> dest_list |> fst |> map extract_tb_entry
 in
  CellLUT (out, ins, tb)
 end else if is_Carry4 cell then let
  val (out, cout, cin, lhs, rhs) = dest_Carry4 cell
  val out = int_of_term out
  val cout = int_of_term cout
  val cin = extract_cell_input cin
  val lhs = lhs |> dest_list |> fst |> map extract_cell_input
  val rhs = rhs |> dest_list |> fst |> map extract_cell_input
 in
  Carry4 (out, cout, cin, lhs, rhs)
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
  " " ^ print_type ty ^ " " ^ stringSyntax.fromHOLstring var ^ ",\n"
 end
 val extenv = extenv |> dest_list |> fst
in
 map print_extenv' extenv |> concat
end;

fun print_wires nl = let
 fun print_wires' (CellLUT (out, _, _)) = "logic w" ^ Int.toString out ^ ";\n"
   | print_wires' (Carry4 (out, cout, _, _, _)) = "logic[3:0] w" ^ Int.toString out ^ ";\nlogic[3:0] w" ^ Int.toString cout ^ ";\n"
in
 map print_wires' nl |> concat
end;

(*
FDCE #(.INIT(INIT)) FDCE_inst (
 .Q(Q),     // 1-bit Data output
 .C(C),     // 1-bit Clock input
 .CE(CE),   // 1-bit Clock enable input
 .CLR(CLR), // 1-bit Asynchronous clear input
 .D(D)      // 1-bit Data input
);
*)
fun print_regs regs = let
 fun print_reg reg = let
  val [ty, name, i, v, inp] = pairSyntax.spine_pair reg
  (* Could sanity-check ty here... *)
  val reg = stringSyntax.fromHOLstring name ^ term_to_string i
  val v = v |> optionSyntax.dest_some |> print_CBool
 in
  "logic " ^ reg ^ ";\n" ^
  "FDCE #(.INIT(" ^ v ^ ")) FDCE_" ^ reg ^ " (\n" ^
  " .Q(" ^ reg ^ ")," ^
  " .C(clk)," ^
  " .CLR(1'b0)," ^
  (if optionSyntax.is_some inp then
   " .CE(1'b1), .D(" ^ (inp |> optionSyntax.dest_some |> extract_cell_input |> print_cell_input) ^ "));\n\n"
  else
   " .CE(1'b0), .D(1'b0));\n\n")
 end
 val regs = regs |> dest_list |> fst
in
 map print_reg regs |> concat
end;

fun pow n m =
 if m <= 0 then
  1
 else
  n * pow n (m - 1);

(*
LUT2 #(.INIT(4'h0) // Specify LUT Contents
) LUT2_inst (
 .O(O),   // LUT general output
 .I0(I0), // LUT input
 .I1(I1)  // LUT input
);
*)
fun print_cell (CellLUT (out, ins, tb)) = let
     val wire = "w" ^ Int.toString out
     val len = length ins
     val ins = ins |> rev
                   |> mapi (fn i => fn inp => ".I" ^ Int.toString i ^ "(" ^ print_cell_input inp ^ ")")
                   |> String.concatWith ", "
     val tb' = all_binary_numbers len
               |> rev
               |> map (fn e => if mem e tb then "1" else "0")
               |> concat
               |> (fn tb' => Int.toString (pow 2 len) ^ "'b" ^ tb')
    in
     "LUT" ^ Int.toString len ^ " #(.INIT(" ^ tb' ^ ")) LUT_" ^ wire ^ " (\n" ^
     " .O(" ^ wire ^ "), "  ^ ins ^ ");\n\n"
    end
(*
CARRY4 CARRY4_inst (
 .CO(CO),         // 4-bit carry out
 .O(O),           // 4-bit carry chain XOR data out
 .CI(CI),         // 1-bit carry cascade input
 .CYINIT(CYINIT), // 1-bit carry initialization
 .DI(DI),         // 4-bit carry-MUX data in
 .S(S)            // 4-bit carry-MUX select input
);
*)
  | print_cell (Carry4 (out, cout, cin, di, s)) = let
    val ci_cyinit = case cin of
                      ConstInp b => ".CI(1'b0), .CYINIT(" ^ print_bool b ^ "),"
                    | cin => ".CI(" ^ print_cell_input cin ^ "), .CYINIT(1'b0),"
    in
     "CARRY4 CARRY4_" ^ Int.toString out ^ " (\n" ^
     " .CO(w" ^ Int.toString cout ^ "), .O(w" ^ Int.toString out ^ "), " ^
     ci_cyinit ^
     " .DI({" ^ (di |> map print_cell_input |> String.concatWith ", ")^ "})," ^
     " .S({" ^ (s |> map print_cell_input |> String.concatWith ", ")^ "}));\n\n"
  end;

val print_nl = concat o map print_cell;

fun print_Circuit tm = let
 val (extenv, regs, nl) = dest_Circuit tm
 val nl = extract_netlist nl
in
 "module Circuit(\n" ^
 " input clk,\n" ^
 print_extenv extenv ^
 " // add other inputs and outputs\n" ^
 ");\n" ^

 "\n" ^
 print_wires nl ^
 "\n" ^
 print_regs regs ^
 print_nl nl ^
 "endmodule\n"
end;

(* For concatenating blasted regs *)
fun unblast_regs reg len = let
 val regs = String.concatWith ", " (List.tabulate (len, (fn i => reg ^ Int.toString i)))
in
 ("output logic[" ^ Int.toString (len - 1) ^ ":0] " ^ reg,
 "assign " ^ reg ^ " = {" ^ regs ^ "}")
end;

end
