open SMLRTLLib;

signature PlacementBackend = sig  

(* direction of stream *)
datatype dir = DWest | DNorth | DEast | DSouth;

val placement_init : unit -> unit;

val add_cell : cell -> int * int -> unit;
val add_rot : dir -> dir -> int * int -> unit;
val add_dup : dir -> dir -> int * int -> unit;

val add_reg : string -> int * int -> unit;

val add_ext : cell_input -> int -> unit;
val add_exts : (cell_input * int) list -> unit;

(* for visualisation *)
val add_route : string -> int * int -> unit;
val add_vline : int * int -> int * int -> unit;
val add_hline : int * int -> int * int -> unit;

val lookup_ext_inp : cell_input -> int;
val lookup_cell_inp : int -> int * int;
val lookup_exts_last_y : unit -> int;

val export : string -> unit;

end
