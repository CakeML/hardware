structure RTLPlacerLib =
struct

open hardwarePreamble;

open SMLRTLLib;

(* Instead of a functor for now: *)
(*open PlacementBackendJS;*)
open PlacementBackendGoL;

(** extraction functions that are not fully general **)

fun extract_extenv tm = let
 fun extract_extenv_entry (var, ty) = (stringSyntax.fromHOLstring var, extract_type ty)
in
 tm |> dest_list |> fst |> map (extract_extenv_entry o pairSyntax.dest_pair)
end;

fun extract_out tm = let
 val (name, tm) = pairSyntax.dest_pair tm
in
 if is_OutInp tm then
  tm |> dest_OutInp |> extract_cell_input |> OutInp
 else
  tm |> dest_OutInps |> dest_list |> fst |> map extract_cell_input |> OutInps
end;

fun extract_outs tm = tm |> dest_list |> fst |> map extract_out;

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

(** P&R **)

val xoffset = ref(0);
val yoffset = ref(0);

fun place_extenv offset i (signal, ty) = let
 val offset = offset + i
 val xoffset = !xoffset
in
 case ty of
   VBool_t => let
    val _ = add_ext (ExtInp (signal, NONE)) offset
    val _ = add_hline (xoffset, offset) (3000, offset)
   in () end
 | VArray_t len => let
    val _ = add_exts (List.tabulate (len, fn i => (ExtInp (signal, SOME i), offset + i)))
    val _ = app (fn offset => add_hline (xoffset, offset) (3000, offset)) (List.tabulate (len, fn i => offset + i))
   in () end
end;

fun place_exts extenv = let
 val y = lookup_exts_last_y ()
 (* todo: these should be removed *)
 (*val _ = add_exts [(ConstInp false, y + 1), (ConstInp true, y + 2)]*)
 val _ = add_hline (!xoffset, y + 1) (3000, y + 1)
 val _ = add_hline (!xoffset, y + 2) (3000, y + 2)

 (* externals *)
 val _ = appi (place_extenv (y+3)) extenv
in () end;

fun route_lhs_ext inp = let
 val xrotate = !xoffset
 val yrotate = lookup_ext_inp inp
 val _ = add_dup DEast DNorth (xrotate, yrotate)

 val _ = add_vline (xrotate, yrotate) (xrotate, !yoffset)

 val yrotate = !yoffset
 val _ = add_rot DNorth DEast (xrotate, yrotate)
in () end;

fun route_lhs_net n = let
 val xrotate = !xoffset
 val (_, yrotate) = lookup_cell_inp n
 val _ = add_dup DEast DNorth (xrotate, yrotate)

 val _ = add_vline (xrotate, yrotate) (xrotate, !yoffset)

 val yrotate = !yoffset
 val _ = add_rot DNorth DEast (xrotate, yrotate)
in () end;

fun route_lhs inp =
 case inp of
   ConstInp _ => failwith "constant inputs not allowed"
 | VarInp (NetVar n, _) => route_lhs_net n
 | _ => route_lhs_ext inp;

fun route_rhs_ext inp = let
 val xrotate = !xoffset + 1
 val yrotate = lookup_ext_inp inp
 val _ = add_dup DEast DNorth (xrotate, yrotate)

 val _ = add_vline (xrotate, yrotate) (xrotate, !yoffset)

in () end;

fun route_rhs_net n = let
 val xrotate = !xoffset + 1
 val (_, yrotate) = lookup_cell_inp n
 val _ = add_dup DEast DNorth (xrotate, yrotate)

 val _ = add_vline (xrotate, yrotate) (xrotate, !yoffset)

in () end;

fun route_rhs inp =
 case inp of
   ConstInp _ => failwith "constant inputs not allowed"
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
 val _ = add_dup DSouth DEast (0, y)
 val delays = List.tabulate (reglen - i, fn i => ("Delay", (1 + i, y)))
 val _ = List.app (uncurry add_route) delays
 val x = 1 + reglen
 val _ = add_reg 1 (x, y);

 (* todo, the direction here depends on if regs or cells are "taller", assume cells taller for now *)
 val oldx = x
 val x = x + 2 + reglen + i
 val _ = add_rot DEast DSouth (x, y)

 val _ = add_hline (oldx, y) (x, y)

 val oldy = y
 val y = !yoffset + nllen + i
 val _ = add_rot DSouth DEast (x, y)

 val _ = add_vline (x, oldy) (x, y)

 val _ = add_hline (x, y) (3000, y)

 val _ = add_ext (VarInp (RegVar regi, NONE)) y
in () end;

fun place_regs nllen regs = appi (place_reg nllen (length regs)) regs;

fun get_inp_y inp =
 case inp of
   VarInp (NetVar n, _) => let val (_, y) = lookup_cell_inp n in y end
 | _ => lookup_ext_inp inp;

fun out_get_inps (_, out) =
 case out of
   OutInp inp => [inp]
 | OutInps inps => inps;

fun is_false_inp inp =
 case inp of
   ConstInp false => true
 | _ => false;

fun place_out_dup inp = let
 val _ = (if is_false_inp inp then
           ()
          else let
           val y = get_inp_y inp
           val _ = add_dup DEast DSouth (!xoffset, y)
          in () end)
 val _ = add_stop DSouth (!xoffset, !yoffset)
 val _ = xoffset := !xoffset + 1
in () end;

fun place_reg_inps regslen i (regty, regi, inp) = let
 val y = get_inp_y inp
 val _ = add_rot DEast DNorth (!xoffset + i, y)
 val _ = add_rot DNorth DWest (!xoffset + i, i)

 val _ = add_vline (!xoffset + i, y) (!xoffset + i, i)

 val x = 1 + regslen + 2 + i
 val _ = add_rot DWest DSouth (x, i)

 val _ = add_hline (!xoffset + i, i) (x, i)

 val y = regslen + i*(2+1) + 2
 val _ = add_rot DSouth DWest (x, y)

 val _ = add_vline (x, i) (x, y)
 val _ = add_hline (x, y) (1 + regslen + 2, y)
in () end;

fun place_regs_inps regs = appi (place_reg_inps (length regs)) regs;

fun place_right_stoppers yoffset_cell_start nllen reglen = let
 val _ = iterate (fn y => add_stop DEast (!xoffset + reglen, yoffset_cell_start - y)) nllen
 val _ = iterate (fn y => add_stop DEast (!xoffset + reglen, yoffset_cell_start + y + 1)) reglen
in () end;

fun place_circuit tm = let
 val (extenv, outs, regs, nl, _) = dest_Circuit tm
 val extenv = extract_extenv extenv
 val outs = extract_outs outs
 val regs = extract_regs regs
 val nl = extract_netlist nl

 val _ = placement_init ()

 val _ = yoffset := length regs
 val _ = add_route "clk" (0, !yoffset)
 val _ = yoffset := !yoffset + 1

 val _ = place_regs (length nl) regs
 val _ = xoffset := 3*(length regs) + 3

 val _ = place_exts extenv

 val _ = yoffset := !yoffset - 1 + length nl
 val yoffset_cell_start = !yoffset
 val _ = List.app place_cell nl

 val _ = yoffset := lookup_exts_last_y () + 1
 val _ = outs |> map out_get_inps |> flatten |> app place_out_dup
                  
 val _ = yoffset := length regs
 val _ = place_regs_inps regs

 (* stoppers to the right *)
 val _ = place_right_stoppers yoffset_cell_start (length nl) (length regs);
in () end;

end
