use "PlacementBackend.sml";

structure PlacementBackendGoL :> PlacementBackend = struct

open hardwarePreamble;

open SMLRTLLib GoLLib;

datatype dir = DWest | DNorth | DEast | DSouth;

fun abbrev_dir dir =
 case dir of
   DWest => "w"
 | DNorth => "n"
 | DEast => "e"
 | DSouth => "s"

val world = ref(Array2.array (1, 1, false));
(* map: cell output -> (x, y) *)
val cells = ref([]:(int * (int * int)) list);

val width = 300;
val height = 300;
val cellsize = 150;

val cell_dir = "/Users/aloow/dev/game-of-life/java/v2/";

fun placement_init () = let
 val _ = world := Array2.array (cellsize*width, cellsize*height, false)
 val _ = cells := [];
in () end;

local
 val cell_not = gol_import (cell_dir ^ "lwss-not-ready.rle")
 val cell_and = gol_import (cell_dir ^ "lwss-and-ready.rle")
 val cell_or = gol_import (cell_dir ^ "lwss-or-ready.rle")
in
fun get_cell_impl cell =
 case cell of
   CellNot _ => cell_not
 | Cell2 (t, _, _, _) =>
   case t of
     CAnd => cell_and
   | COr => cell_or
   | CEqual => cell_or (* TODO: we don't have any eq cell yet *)
end;

fun add_cell cell (x, y) = let
 val () = cells := (cell_output cell, (x, y)) :: !cells;
 val cell_impl = get_cell_impl cell
 val () = gol_place (!world) cell_impl (x*cellsize, y*cellsize)
in () end;

fun lookup_cell_inp n = lookup n (!cells);

local
 fun abbrev_rot_dir indir outdir =
  abbrev_dir indir ^ abbrev_dir outdir;
    
 val rots = [(DEast, DNorth), (DEast, DSouth),
             (DNorth, DEast), (* (DNorth, DWest), *)
             (DSouth, DEast), (DSouth, DWest),
             (DWest, DNorth), (DWest, DSouth)]
         |> map (fn (indir, outdir) => let
                 val k = abbrev_rot_dir indir outdir
                 in
                  (k, gol_import (cell_dir ^ "lwss-rotate-" ^ k ^ ".rle"))
                 end)
         |> Redblackmap.fromList String.compare
in
fun add_rot indir outdir (x, y) = let
 val k = abbrev_rot_dir indir outdir
 val cell_impl = Redblackmap.find (rots, k)
in
 gol_place (!world) cell_impl (x*cellsize, y*cellsize)
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
                  (k, gol_import (cell_dir ^ "lwss-dup-" ^ k ^ ".rle"))
                 end)
         |> Redblackmap.fromList String.compare
in
fun add_dup indir outdir (x, y) = let
 val k = abbrev_dup_dir indir outdir
 val cell_impl = Redblackmap.find (dups, k)
in
 gol_place (!world) cell_impl (x*cellsize, y*cellsize)
end
end;

(* TODO *)
fun add_reg regty (x, y) = ();

(* fake for now *)
val exts_locs = ref([]:(cell_input * int) list);
fun add_ext inp y = exts_locs := (inp, y) :: !exts_locs;
fun add_exts inps_y = exts_locs := inps_y @ !exts_locs;
fun lookup_ext_inp inp = lookup inp (!exts_locs);
fun lookup_exts_last_y () = let val (_, y) =  hd (!exts_locs) in y end;

fun export filename = gol_export (!world) filename;

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
