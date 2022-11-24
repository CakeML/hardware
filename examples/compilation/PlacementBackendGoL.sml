use "PlacementBackend.sml";

structure PlacementBackendGoL (*:> PlacementBackend*) = struct

open hardwarePreamble;

open SMLRTLLib GoLLib;

datatype dir = DWest | DNorth | DEast | DSouth;

fun abbrev_dir dir =
 case dir of
   DWest => "w"
 | DNorth => "n"
 | DEast => "e"
 | DSouth => "s"

(* "placed cell" *)
datatype pcell = PCell of cell
               | PReg of int
               | PRot of (dir * dir) (* input, output *)
               | PDup of (dir* dir) (* input, duplicate output *)
               | PStop of dir (* stops streams in given direction*);

fun pcell_width pcell =
 case pcell of
   PCell _ => 1
 | PReg _ => 1 (* TODO: 6 *)
 | PRot _ => 1
 | PDup _ => 1
 | PStop _ => 1;

val world = ref([]:((int * int) * pcell) list);
(* map: cell output -> (x, y) *)
val cells = ref([]:(int * (int * int)) list);

fun placement_init () = let
 val _ = world := [];
 val _ = cells := [];
in () end;

fun add_cell cell (x, y) = let
 val () = cells := (cell_output cell, (x, y)) :: !cells
 val () = world := ((x, y), PCell cell) :: !world
in () end;

fun add_rot indir outdir (x, y) = let
 val () = world := ((x, y), PRot (indir, outdir)) :: !world
in () end;

fun add_dup indir outdir (x, y) = let
 val () = world := ((x, y), PDup (indir, outdir)) :: !world
in () end;

fun add_stop dir (x, y) = let
 val () = world := ((x, y), PStop dir) :: !world
in () end;

fun lookup_cell_inp n = lookup n (!cells);

fun cells_y () = !cells |> map (snd o snd);

(* "Fake" constant 1 reg for now, until we have actual regs *)
fun add_reg n (x, y) =
 (*world := [((x, y), PReg 0), ((x, y+1), PReg 1), ((x, y+2), PReg 2)] @ !world;*)
 world := [((x, y), PReg n), ((x, y + 1), PStop DWest)] @ !world;

(* fake for now *)
val exts_locs = ref([]:(cell_input * int) list);
fun add_ext inp y = exts_locs := (inp, y) :: !exts_locs;
fun add_exts inps_y = exts_locs := inps_y @ !exts_locs;
fun lookup_ext_inp inp = lookup inp (!exts_locs);

fun exts_max [] = 0
  | exts_max ((_, y)::ys) = let val max = exts_max ys in if y > max then y else max end;

fun lookup_exts_last_y () = exts_max (!exts_locs);

val cell_dir = "/Users/aloow/dev/game-of-life/java/v2/";

local
 val cell_not = gol_import (cell_dir ^ "lwss-not-ready.rle") (1, 1)
 val cell_and = gol_import (cell_dir ^ "lwss-and-ready.rle") (1, 1)
 val cell_or = gol_import (cell_dir ^ "lwss-or-ready.rle") (1, 1)
 (*val cell_xor = gol_import (cell_dir ^ "lwss-xor-ready.rle") (1, 1)*)
in
fun get_cell_gcell cell =
 case cell of
   CellNot _ => cell_not
 | Cell2 (t, _, _, _) =>
   case t of
     CAnd => cell_and
   | COr => cell_or
   | CXOr => failwith "xor not implemented yet" (*cell_xor*)
end;

local
 val preg_gcell = gol_import (cell_dir ^ "lwss-gun--e.rle") (1, 1)
 val empty = empty_cell ()
in
fun get_preg_gcell n =
 if n = 0 then
  empty
 else
  preg_gcell
end;

fun dir_toString dir =
 case dir of
   DWest => "west"
 | DNorth => "north"
 | DEast => "east"
 | DSouth => "south";

local
 fun abbrev_rot_dir indir outdir =
  abbrev_dir indir ^ abbrev_dir outdir;

 val rots = [(DEast, DNorth), (DEast, DSouth),
             (DNorth, DEast), (DNorth, DWest),
             (DSouth, DEast), (DSouth, DWest),
             (DWest, DNorth), (DWest, DSouth)]
         |> map (fn (indir, outdir) => let
                 val k = abbrev_rot_dir indir outdir
                 in
                  (k, gol_import (cell_dir ^ "lwss-rotate-" ^ k ^ ".rle") (1, 1))
                 end)
         |> Redblackmap.fromList String.compare
in
fun get_rot_gcell indir outdir = let
 val k = abbrev_rot_dir indir outdir
in
 case Redblackmap.peek (rots, k) of
   NONE => failwith ("missing rot cell: " ^ dir_toString indir ^ " -> " ^ dir_toString outdir)
 | SOME cell_impl => cell_impl
end
end;

local
 fun abbrev_dup_dir indir outdir =
  abbrev_dir indir ^ "-" ^ abbrev_dir indir ^ abbrev_dir outdir;

 val dups = [(DEast, DNorth), (DEast, DSouth),
             (DNorth, DEast), (DNorth, DWest),
             (DSouth, DEast), (DSouth, DWest),
             (DWest, DNorth), (DWest, DSouth)]
         |> map (fn (indir, outdir) => let
                 val k = abbrev_dup_dir indir outdir
                 in
                  (k, gol_import (cell_dir ^ "lwss-dup-" ^ k ^ ".rle") (1, 1))
                 end)
         |> Redblackmap.fromList String.compare
in
fun get_dup_gcell indir outdir = let
 val k = abbrev_dup_dir indir outdir
in
 case Redblackmap.peek (dups, k) of
   NONE => failwith ("missing dup cell: " ^ dir_toString indir ^ " -> " ^ dir_toString outdir)
 | SOME cell_impl => cell_impl
end
end;

local
 val west_north_gcell = gol_import (cell_dir ^ "lwss-and-wn-w.rle") (1, 1)
 val east_south_gcell = gol_import (cell_dir ^ "lwss-and-es-e.rle") (1, 1)
in
fun get_stop_gcell dir =
 case dir of
   DWest => west_north_gcell
 | DNorth => west_north_gcell
 | DEast => east_south_gcell
 | DSouth => east_south_gcell
end;

fun max_x_cell world = let
 fun max_x_cell_row g_max_x = foldl (fn ((x, cell), g_max_x) => Int.max (x + pcell_width cell - 1, g_max_x)) g_max_x
in
 foldl (fn ((y, xs), g_max_x) => max_x_cell_row g_max_x xs) 0 world
end;

datatype 'a map_entry = ME_first of int * 'a
                      | ME_item of (int * 'a) * (int * 'a)
                      | ME_last of int * 'a;

(* f : outer coords -> inner y -> cell *)
fun approws (f: int -> int -> 'a map_entry -> unit) rows = let
 fun appcols' cols y y_inner =
  case cols of
    [] => failwith "impossible" (* <-- just to silence warning *)
  | [xc] => f y y_inner (ME_last xc)
  | (xc1::xc2::cols) => (f y y_inner (ME_item (xc1, xc2)); appcols' (xc2::cols) y y_inner)

 fun appcols cols y y_inner =
  case cols of
    [] => failwith "impossible: empty row?"
  | (xc::cols) => (f y y_inner (ME_first xc); appcols' (xc::cols) y y_inner)
in
 app (fn (y, cols) => iterate (appcols cols y) cellsize) rows
end;

fun export_gcell out y gcell =
 iterate (fn x => out (if Array2.sub (gcell, y, x) then "o" else "b")) cellsize;

fun get_gcell pcell =
 case pcell of
   PCell cell => get_cell_gcell cell
 | PReg n => get_preg_gcell n (*failwith "not implemented yet"*)
 | PRot (indir, outdir) => get_rot_gcell indir outdir
 | PDup (indir, outdir) => get_dup_gcell indir outdir
 | PStop dir => get_stop_gcell dir;

fun export_pcell out y_inner pcell = let
 val gcell = get_gcell pcell
in
 export_gcell out y_inner gcell
end;

fun export_pcells out max_x y y_inner e =
 case e of
   ME_first (x, pcell) => let
    val () = if x <> 0 then out (Int.toString (cellsize*x) ^ "b") else ()
   in
    export_pcell out y_inner pcell
   end
 | ME_item ((xprev, pcellprev), (x, pcell)) => let
    val w = x - (xprev + pcell_width pcellprev)
    val () = if w <> 0 then out (Int.toString (cellsize*w) ^ "b") else ()
   in
    export_pcell out y_inner pcell
   end
 | ME_last (x, pcell) =>
   let
    val w = max_x - (x + pcell_width pcell - 1)
    val () = if w <> 0 then out (Int.toString (cellsize*w) ^ "b$\n") else out "$\n"
   in () end;

fun rowify_world world = let
 fun update_entry ycell prev =
  case prev of
    NONE => [ycell]
  | SOME prev => ycell :: prev
in
 world
 |> foldl (fn (((x, y), cell), acc) => Redblackmap.update (acc, y, update_entry (x, cell)))
          (Redblackmap.mkDict Int.compare)
 |> Redblackmap.transform (sort (fn (y1, _) => fn (y2, _) => y1 <= y2))
 |> Redblackmap.listItems
end;

(* val filename = "world.rle" *)

fun export filename = let
 val rows = rowify_world (!world)
 val max_x = max_x_cell rows
 val f = TextIO.openOut filename
 val out = fn s => TextIO.output (f, s)
 val () = out "x = 0, y = 0, rule = B3/S23\n"
 val () = approws (export_pcells out max_x) rows
 val () = TextIO.closeOut f
in () end;

(* for visualisation, does nothing in the GoL backend *)
fun add_route (_ : string) (_ : int * int) = ();
fun add_vline (_ : int * int) (_ : int * int) = ();
fun add_hline (_ : int * int) (_ : int * int) = ();

(*

add_cell (CellNot (0, ConstInp true)) (0, 0)

gol_print (!world)

val arr = Array2.array (5, 4, false)

Array2.nCols arr;
Array2.nRows arr;

Array2.appi Array2.RowMajor
 (fn (row, col, c) => (print (Int.toString row ^ ", " ^ Int.toString col ^ "\n"); if col = Array2.nCols arr - 1 then print "\n" else ()))
 {base = arr, col = 0, row = 0, nrows = NONE, ncols = NONE};

gol_export (!world) (cell_dir ^ "world.rle")


*)

end
