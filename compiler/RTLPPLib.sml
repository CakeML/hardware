structure RTLPPLib =
struct

open hardwarePreamble;

open SMLRTLLib;

open listSyntax RTLSyntax;

(* Currently old prints LUTs because that's what we are interested in currently *)

(* wire w20 = LUT ... *)

fun print_var (RegVar reg) = reg
  | print_var (NetVar n) = "w" ^ Int.toString n;

(* TODO: Incomplete! *)
fun print_cell_input (ConstInp b) = if b then "1'b1" else "1'b0"
  | print_cell_input (VarInp var) = print_var var;

fun print_lut_input i inp =
 ".I" ^ Int.toString i ^ "(" ^ print_cell_input inp ^ ")";

fun dest_bool t =
 if t ~~ T then
  true 
 else if t ~~ F then
  false
 else
  failwith "bool not T or F";

fun pow2 n = if n = 0 then 1 else 2 * pow2 (n - 1);

(* Print things in "opposite" order to have a more direct corr between formal syntax and pp syntax *)
fun maprevi f l = let
 fun maprevi' _ [] = []
   | maprevi' i (x::xs) = f i x :: maprevi' (i - 1) xs
in
 maprevi' (length l - 1) l
end;

fun print_cell cell =
 if is_CellLUT cell then let
  val (out, ins, tb) = dest_CellLUT cell

  val out = out |> int_of_term |> Int.toString

  val ins = ins |> dest_list |> fst |> map extract_cell_input |> maprevi print_lut_input;
  val len = length ins
  val ins = ins |> String.concatWith ", "

  (* Inefficient but simple, could sort instead... *)
  (* note: tb entries of incorrect length will be ignored, exactly as in HOL semantics *)
  val tb = tb |> dest_list |> fst |> map (map dest_bool o fst o dest_list)
  val tb_binary = len |> all_binary_numbers |> rev |> map (fn e => if mem e tb then "1" else "0") |> String.concat
  val tb_binary_len = pow2 len |> Int.toString
 in
  "wire w" ^ out ^ ";\n" ^
  "LUT" ^ Int.toString len ^ " #(.INIT(" ^ tb_binary_len ^ "'b" ^ tb_binary ^ ")) LUT_inst" ^ out ^
  " (.O(w" ^ out ^ "), " ^ ins ^ ");\n\n"
 end else
  failwith "not implemented: cannot print cell";

fun print_luts nl = let
 val nl = nl |> dest_list |> fst
 val nl = nl |> map print_cell |> String.concat
in
 nl
end;

val regs = ``[("a", VarInp (NetVar 5)); ("b", VarInp (NetVar 4))]``;

fun extract_reg (reg, inp) = (stringSyntax.fromHOLstring reg, extract_cell_input inp);

(* TODO: Check so regs are not named the same as wires ... i.e w<num> *)
(* TODO: Check so no strange chars are in name, such as "(" or similar -- can cause syntax errors *)
(* TODO: Use delcs in the future... need to declare regs above netlist. *)
fun print_reg (reg, inp) = let
 val inp = print_cell_input inp
in
 "wire " ^ reg ^ ";\n" ^
 "FDRE FDRE_inst_" ^ reg ^ " (.Q(" ^ reg ^ "), .C(clk), .CE(1), .R(0), .D(" ^ inp ^ "));\n\n"
end;

fun print_regs regs = regs |> dest_list |> fst |> map (print_reg o extract_reg o pairSyntax.dest_pair) |> concat;

(* print (print_luts lutnl); print (print_regs regs) *)

end
