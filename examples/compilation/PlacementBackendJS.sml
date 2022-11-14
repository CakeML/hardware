use "PlacementBackend.sml";

(* TODO:
add_rot, previously called add_route "Rot-w2n" etc.
add_dup, previously just called add_route "Dup-w2en"
*)

structure PlacementBackendJS :> PlacementBackend = struct

open hardwarePreamble;

open SMLRTLLib;

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

fun placement_init () = let
 val _ = reg_locs := []
 val _ = exts_locs := []
 val _ = cell_locs := []
 val _ = route_locs := []
 val _ = vlines := []
 val _ = hlines := []
in () end;

fun add_cell cell (x, y) = cell_locs := (cell_output cell, (cell, x, y)) :: !cell_locs;
fun add_ext inp y = exts_locs := (inp, y) :: !exts_locs;
fun add_exts inps_y = exts_locs := inps_y @ !exts_locs;
fun add_route cell (x, y) = route_locs := (cell, (x, y)) :: !route_locs;
fun add_vline loc1 loc2 = vlines := (loc1, loc2) :: !vlines;
fun add_hline loc1 loc2 = hlines := (loc1, loc2) :: !hlines;
fun add_reg regty (x, y) = reg_locs := (regty, (x, y)) :: !reg_locs;

fun lookup_exts_last_y () = let
 val (_, y) =  hd (!exts_locs)
in
 y
end;

fun lookup_ext_inp inp = lookup inp (!exts_locs);
fun lookup_cell_inp n = lookup n (!cell_locs);

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

fun export (filename) =
 "const everything = " ^ everything2js () ^ ";\n\n" ^
 "const vlines = " ^ lines2js (!vlines)  ^ ";\n\n" ^
 "const hlines = " ^ lines2js (!hlines)  ^ ";\n\n" |> writeFile filename;

end
