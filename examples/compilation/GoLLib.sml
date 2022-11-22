structure GoLLib =
struct

open hardwarePreamble;

fun span p xs =
 case xs of
   [] => ([], [])
 | (x::xs') => if p x then let val (ys, zs) = span p xs' in (x::ys, zs) end else ([], xs);

fun array2_set_true arr i j len =
 Array2.modifyi Array2.RowMajor (fn _ => true) {base = arr, col = i, row = j, nrows = SOME 1, ncols = SOME len}
 handle Subscript => failwith ("Cell outside bounding box: (x, y) = (" ^ Int.toString i ^ ", " ^ Int.toString j ^ ")");

fun consume_line arr i j line = let
 val (ds, line) = span Char.isDigit line
 val d = if null ds then 1 else (ds |> String.implode |> Int.fromString |> Option.valOf)
 val cell = hd line
 val line = tl line
 (*val () = print (Int.toString i ^ ", " ^ Int.toString j ^ ": " ^ Int.toString d ^ " with " ^ Char.toString cell ^ "\n")*)
in
 case cell of
   #"o" => (array2_set_true arr i j d; consume_line arr (i + d) j line)
 | #"b" => consume_line arr (i + d) j line
 | #"$" => consume_line arr 0 (j + d) line
 | #"!" => (i, j)
 | #"\n" => (i, j)
 | _ => failwith ("Unexpected cell " ^ Char.toString(cell))
end;
                   
fun consume_lines f arr i j =
 case TextIO.inputLine f of
   NONE => arr
 | SOME line => let val (i, j) = consume_line arr i j (String.explode line) in consume_lines f arr i j end;

val cellsize = 150;

fun gol_import filename (width, height) = let
 val f = TextIO.openIn filename
 (* consume header/comment *)
 val l = TextIO.inputLine f
 (* consume another line (i.e., header) if first line was comment *)
 val _ = if String.sub (Option.valOf l, 0) = #"#" then TextIO.inputLine f else NONE
 val arr = Array2.array (width*cellsize, height*cellsize, false)
 val _ = consume_lines f arr 0 0
in
 arr
end

fun gol_export arr filename = let
 val f = TextIO.openOut filename
 val out = fn s => TextIO.output (f, s)
 val () = out "x = 0, y = 0, rule = B3/S23\n"
 val last_col = Array2.nCols arr - 1
 val last_row = Array2.nRows arr - 1
 val () = Array2.appi Array2.RowMajor
           (fn (row, col, c) => (
             out (if c then "o" else "b");
             if col = last_col then
              out (if row = last_row then "!\n" else "$\n")
             else
              ()))
           {base = arr, col = 0, row = 0, nrows = NONE, ncols = NONE};
in () end;

fun gol_print arr = let
 val last_col = Array2.nCols arr - 1
 val () = print "\n"
in
 Array2.appi Array2.RowMajor
             (fn (row, col, c) => (print (if c then "o" else ".");
                                   if col = last_col then print "\n" else ()))
             {base = arr, col = 0, row = 0, nrows = NONE, ncols = NONE}
end;

fun gol_place arr component (x, y) =
 Array2.copy {
  src = {base = component, row = 0, col = 0, nrows = NONE, ncols = NONE},
  dst = arr,
  dst_row = y,
  dst_col = x };

(* x = 134, y = 106, rule = B3/S23b *)

end
