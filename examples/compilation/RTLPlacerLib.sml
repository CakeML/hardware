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
 val (regi, _) = pairSyntax.dest_pair tm
 val (reg, i) = pairSyntax.dest_pair regi
 val reg = stringSyntax.fromHOLstring reg
 val i = int_of_term i
in
 (reg, i)
end;

fun extract_regs tm = regs |> dest_list |> fst |> map extract_reg;
(** end todo **)

(* row for external input -- should be a map in the future *)
val exts_locs = ref([]:(cell_input * int) list);

(* location of cells (cell output, (x, y)) -- should be a map in the future *)
val cell_locs = ref([]:(int * (cell * int * int)) list);
(* no need for inputs here since they are use-once: *)
val rotation_locs = ref([]:(cell * (int * int)) list);

fun add_cell cell (x, y) = cell_locs := (cell_output cell, (cell, x, y)) :: !cell_locs;
fun add_rotation cell (x, y) = rotation_locs := (cell, (x, y)) :: !rotation_locs;

fun place_extenv (signal, ty) = let
 val offset = List.length (!exts_locs)
in
 case ty of
   VBool_t => exts_locs := (ExtInp (signal, NONE), offset) :: !exts_locs
 | VArray_t len => exts_locs := List.tabulate (len, fn i => (ExtInp (signal, SOME i), offset + i)) @ !exts_locs
end;

fun place_reg regi = let
 val offset = List.length (!exts_locs)
in
 exts_locs := (VarInp (RegVar regi, NONE), offset) :: !exts_locs
end;

fun place_exts extenv regs = let
 (* todo: these should be removed *)
 val _ = exts_locs := [(ConstInp false, 0), (ConstInp true, 1)]
 (* regs *)
 val _ = List.app place_reg regs
 (* externals *)
 val _ = List.app place_extenv extenv in () end;

val xoffset = ref(0);
val yoffset = ref(0);

fun route_lhs_ext inp = let
 val xrotate = !xoffset
 val yrotate = lookup inp (!exts_locs)
 val _ = add_rotation CellDuplicate_Left2DownAndRight (xrotate, yrotate)

 val yrotate = !yoffset
 val _ = add_rotation CellRotate_Down2Right (xrotate, yrotate) in () end;

fun route_lhs_net n = let
 val xrotate = !xoffset
 val (_, _, yrotate) = lookup n (!cell_locs)
 val _ = add_rotation CellDuplicate_Left2DownAndRight (xrotate, yrotate)

 val yrotate = !yoffset
 val _ = add_rotation CellRotate_Down2Right (xrotate, yrotate) in () end;

fun route_lhs inp =
 case inp of
   VarInp (RegVar _, _) => (* TODO: dummy implementation until there's support for state... *) route_lhs_ext inp
 | VarInp (NetVar n, _) => route_lhs_net n
 | _ => route_lhs_ext inp;

fun route_rhs_ext inp = let
 val xrotate = !xoffset + 1
 val yrotate = lookup inp (!exts_locs)
 val _ = add_rotation CellDuplicate_Left2DownAndRight (xrotate, yrotate) in () end;

fun route_rhs_net n = let
 val xrotate = !xoffset + 1
 val (_, _, yrotate) = lookup n (!cell_locs)
 val _ = add_rotation CellDuplicate_Left2DownAndRight (xrotate, yrotate) in () end;

fun route_rhs inp =
 case inp of
   VarInp (RegVar _, _) => (* TODO: dummy implementation until there's support for state... *) route_rhs_ext inp
 | VarInp (NetVar n, _) => route_rhs_net n
 | _ => route_rhs_ext inp;

fun place_cell cell =
 case cell of
   CellNot (out, inp) => let
    val _ = route_lhs inp

    val xcell = !xoffset + 1
    val ycell = !yoffset
    val _ = add_cell cell (xcell, ycell)

    val _ = xoffset := !xoffset + 2
    val _ = yoffset := !yoffset + 1 in () end
                     
 | Cell2 (cell2, out, lhs, rhs) => let
    val _ = route_lhs lhs
    val _ = route_rhs rhs

    val xcell = !xoffset + 1
    val ycell = !yoffset
    val _ = add_cell cell (xcell, ycell)

    val _ = xoffset := !xoffset + 2
    val _ = yoffset := !yoffset + 1 in () end

 | _ => failwith "unexpected cell";

(*
val tm = circuit |> concl |> rhs;
*)

val (extenv, outs, regs, nl, _) = dest_Circuit tm

val extenv = extract_extenv extenv
val regs = extract_regs regs;
val _ = place_exts extenv regs;

val nl = extract_netlist nl
val _ = xoffset := 1;
val _ = yoffset := List.length (!exts_locs);
val _ = rotation_locs := [];
val _ = cell_locs := [];
val _ = List.app place_cell nl;

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

fun rot2js (cell, (x, y)) =
 case cell of
   CellDuplicate_Left2DownAndRight => "[\"Dup\", " ^ Int.toString x ^ ", " ^ Int.toString y ^ "]"
 | CellRotate_Down2Right => "[\"Rot\", " ^ Int.toString x ^ ", " ^ Int.toString y ^ "]";

fun rots2js () = List.map rot2js (!rotation_locs);

fun everything2js () =
 "[" ^ ((cells2js () @ rots2js ()) |> String.concatWith ",") ^ "]\n";

everything2js () |> print

end
