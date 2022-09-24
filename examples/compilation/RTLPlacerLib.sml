structure RTLPlacerLib =
struct

open hardwarePreamble;

open SMLRTLLib;

(** todo: move all extract stuff to the right file... **)
datatype vertype = VBool_t | VArray_t of int;

fun extract_type tm =
 if is_CBool_t tm then
  VBool_t
 else if is_CArray_t tm then let
  val dim = tm |> dest_CArray_t |> int_of_term
 in
  VArray_t dim
 end else
  failwith ("Unknown type: " ^ term_to_string tm);

fun extract_extenv tm = let
 fun extract_extenv_entry (var, ty) = (fromHOLstring var, extract_type ty)
in
 tm |> dest_list |> fst |> map (extract_extenv_entry o pairSyntax.dest_pair)
end;

fun extract_reg tm = let
 val (regi, metadata) = pairSyntax.dest_pair tm

 val (reg, i) = pairSyntax.dest_pair regi
 val reg = stringSyntax.fromHOLstring reg
 val i = int_of_term i

 val (_, metadata) = TypeBase.dest_record metadata
 val init = lookup "init" metadata |> optionSyntax.dest_some |> dest_CBool |> extract_bool
 (* todo: make sure all regs have an input... i.e. optimise away all other regs... *)
 val inp = lookup "inp" metadata |> optionSyntax.dest_some |> extract_cell_input
in
 (if init then "Reg1" else "Reg0", (reg, i), inp)
end;

fun extract_regs tm = tm |> dest_list |> fst |> map extract_reg;
(** end todo **)

(* regs *)
val reg_locs = ref([]:(string * (int * int)) list);
(* row for external input -- should be a map in the future *)
val exts_locs = ref([]:(cell_input * int) list);
(* location of cells (cell output, (x, y)) -- should be a map in the future *)
val cell_locs = ref([]:(int * (cell * int * int)) list);
(* no need for inputs here since they are use-once: *)
val route_locs = ref([]:(string * (int * int)) list);

val vlines = ref([]:((int * int) * (int * int)) list);
val hlines = ref([]:((int * int) * (int * int)) list);

(** print to js **)
fun cell22js cell2 =
 case cell2 of
   CAnd => "And"
 | COr => "Or"
 | CEqual => "XNor";

fun cell2js (_, (cell, x, y)) =
 case cell of
   CellNot _ => "[\"CellNot\", " ^ Int.toString x ^ ", " ^ Int.toString y ^ "]"
 | Cell2 (cell2, _, _, _) => "[\"" ^ cell22js cell2 ^ "\", " ^ Int.toString x ^ ", " ^ Int.toString y ^ "]";

fun cells2js () = List.map cell2js (!cell_locs);

fun route2js (cell, (x, y)) = "[\"" ^ cell ^ "\", " ^ Int.toString x ^ ", " ^ Int.toString y ^ "]";

fun routes2js () = List.map route2js (!route_locs);

fun regs2js () = List.map route2js (!reg_locs);

fun everything2js () =
 "[" ^ ((regs2js () @ cells2js () @ routes2js ()) |> String.concatWith ",") ^ "]\n";

fun line2js ((x1, y1), (x2, y2)) = "[[" ^ Int.toString x1 ^ ", " ^ Int.toString y1 ^ "], [" ^ Int.toString x2 ^ ", " ^ Int.toString y2 ^ "]]";

fun lines2js lines = "[" ^ (map line2js lines |> String.concatWith ",") ^ "]\n";

(** P&R **)

fun add_cell cell (x, y) = cell_locs := (cell_output cell, (cell, x, y)) :: !cell_locs;
fun add_route cell (x, y) = route_locs := (cell, (x, y)) :: !route_locs;
fun add_vline loc1 loc2 = vlines := (loc1, loc2) :: !vlines;
fun add_hline loc1 loc2 = hlines := (loc1, loc2) :: !hlines;

fun place_extenv offset i (signal, ty) = let
 val offset = offset + i
 val xoffset = !xoffset
in
 case ty of
   VBool_t => let
    val _ = exts_locs := (ExtInp (signal, NONE), offset) :: !exts_locs
    val _ = add_hline (xoffset, offset) (3000, offset)
   in () end
 | VArray_t len => let
    val _ = exts_locs := List.tabulate (len, fn i => (ExtInp (signal, SOME i), offset + i)) @ !exts_locs
    val _ = app (fn offset => add_hline (xoffset, offset) (3000, offset)) (List.tabulate (len, fn i => offset + i))
   in () end
end;

fun place_exts extenv = let
 val (_, y) = hd (!exts_locs)
 (* todo: these should be removed *)
 val _ = exts_locs := [(ConstInp false, y + 1), (ConstInp true, y + 2)] @ !exts_locs;
 val _ = add_hline (!xoffset, y + 1) (3000, y + 1)
 val _ = add_hline (!xoffset, y + 2) (3000, y + 2)

 (* externals *)
 val _ = appi (place_extenv (y+3)) extenv
in () end;

val xoffset = ref(0);
val yoffset = ref(0);

fun route_lhs_ext inp = let
 val xrotate = !xoffset
 val yrotate = lookup inp (!exts_locs)
 val _ = add_route "Dup-w2en" (xrotate, yrotate)

 val _ = add_vline (xrotate, yrotate) (xrotate, !yoffset)

 val yrotate = !yoffset
 val _ = add_route "Rot-s2e" (xrotate, yrotate)
in () end;

fun route_lhs_net n = let
 val xrotate = !xoffset
 val (_, _, yrotate) = lookup n (!cell_locs)
 val _ = add_route "Dup-w2en" (xrotate, yrotate)

 val _ = add_vline (xrotate, yrotate) (xrotate, !yoffset)

 val yrotate = !yoffset
 val _ = add_route "Rot-s2e" (xrotate, yrotate)
in () end;

fun route_lhs inp =
 case inp of
   VarInp (NetVar n, _) => route_lhs_net n
 | _ => route_lhs_ext inp;

fun route_rhs_ext inp = let
 val xrotate = !xoffset + 1
 val yrotate = lookup inp (!exts_locs)
 val _ = add_route "Dup-w2en" (xrotate, yrotate)

 val _ = add_vline (xrotate, yrotate) (xrotate, !yoffset)

in () end;

fun route_rhs_net n = let
 val xrotate = !xoffset + 1
 val (_, _, yrotate) = lookup n (!cell_locs)
 val _ = add_route "Dup-w2en" (xrotate, yrotate)

 val _ = add_vline (xrotate, yrotate) (xrotate, !yoffset)

in () end;

fun route_rhs inp =
 case inp of
  VarInp (NetVar n, _) => route_rhs_net n
 | _ => route_rhs_ext inp;

fun place_cell cell =
 case cell of
   CellNot (out, inp) => let
    val _ = route_lhs inp

    val xcell = !xoffset + 1
    val ycell = !yoffset
    val _ = add_cell cell (xcell, ycell)

    val _ = xoffset := !xoffset + 2
    val _ = yoffset := !yoffset - 1 in () end

 | Cell2 (cell2, out, lhs, rhs) => let
    val _ = route_lhs lhs
    val _ = route_rhs rhs

    val xcell = !xoffset + 1
    val ycell = !yoffset
    val _ = add_cell cell (xcell, ycell)

    val _ = xoffset := !xoffset + 2
    val _ = yoffset := !yoffset - 1 in () end;

fun place_reg nllen reglen i (regty, regi, _) = let
 val y = !yoffset + i*(2 + 1)
 val _ = add_route "Dup-n2se" (0, y)
 val delays = List.tabulate (reglen - i, fn i => ("Delay", (1 + i, y)))
 val _ = List.app (uncurry add_route) delays
 val x = 1 + reglen
 val _ = reg_locs := (regty, (x, y)) :: !reg_locs;

 (* todo, the direction here depends on if regs or cells are "taller", assume cells taller for now *)
 val oldx = x
 val x = x + 2 + reglen + i
 val _ = add_route "Rot-w2s" (x, y)

 val _ = add_hline (oldx, y) (x, y)

 val oldy = y
 val y = !yoffset + nllen + i
 val _ = add_route "Rot-n2e" (x, y)

 val _ = add_vline (x, oldy) (x, y)

 val _ = add_hline (x, y) (3000, y)

 val _ = exts_locs := (VarInp (RegVar regi, NONE), y) :: !exts_locs
in () end;

fun place_regs nllen regs = appi (place_reg nllen (length regs)) regs;

fun get_inp_y inp =
 case inp of
   VarInp (NetVar n, _) => let val (_, _, y) = lookup n (!cell_locs) in y end
 | _ => lookup inp (!exts_locs);

fun place_reg_inps i (regty, regi, inp) = let
 val y = get_inp_y inp;
 val _ = add_route "Rot-w2n" (!xoffset + i, y)
 val _ = add_route "Rot-s2w" (!xoffset + i, i)

 val _ = add_vline (!xoffset + i, y) (!xoffset + i, i);

 val x = 1 + length regs + 2 + i
 val _ = add_route "Rot-e2s" (x, i)

 val _ = add_hline (!xoffset + i, i) (x, i);

 val y = length regs + i*(2+1) + 2;
 val _ = add_route "Rot-n2w" (x, y)

 val _ = add_vline (x, i) (x, y);
 val _ = add_hline (x, y) (1 + length regs + 2, y);
in () end;

fun place_regs_inps regs = appi place_reg_inps regs;

fun place_circuit tm = let
 val (extenv, outs, regs, nl, _) = dest_Circuit tm
 val extenv = extract_extenv extenv
 val regs = extract_regs regs
 val nl = extract_netlist nl

 val _ = reg_locs := []
 val _ = exts_locs := []
 val _ = cell_locs := []
 val _ = route_locs := []
 val _ = vlines := []
 val _ = hlines := []

 val _ = yoffset := length regs
 val _ = add_route "clk" (0, !yoffset);
 val _ = yoffset := !yoffset + 1

 val _ = place_regs (length nl) regs
 val _ = xoffset := 3*(length regs) + 2

 val _ = place_exts extenv

 val _ = yoffset := !yoffset - 1 + length nl
 val _ = List.app place_cell nl

 val _ = yoffset := length regs
 val _ = place_regs_inps regs
in () end;

(*

val tm = circuit |> concl |> rhs;

"const everything = " ^ everything2js () ^ ";\n\n" ^
"const vlines = " ^ lines2js (!vlines)  ^ ";\n\n" ^
"const hlines = " ^ lines2js (!hlines)  ^ ";\n\n" |> writeFile "data.js";

*)

end
