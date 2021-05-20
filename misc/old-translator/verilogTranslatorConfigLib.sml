structure verilogTranslatorConfigLib =
struct

open hardwarePreamble;

open verilogTranslatorCoreLib;

(** Config **)

(*
open ag32MachineTheory;
val state_ty = ``:state_circuit``;
val fext_ty = ``:ext``;
*)

(*
open circuitExampleTheory;
val state_ty = ``:state``;
val fext_ty = ``:ext_state``;
*)

open avgExampleTheory;
val state_ty = ``:state``;
val fext_ty = ``:ext_state``;

(*
open regexpExampleTheory;
val state_ty = ``:rc``;
val fext_ty = ``:rc_ext``;
*)

(** State record info **)

val fields = map fst (TypeBase.fields_of state_ty);

val accessors = TypeBase.accessors_of state_ty
                |> map (rator o lhs o snd o strip_forall o concl)
                |> zip fields;

val updates = TypeBase.updates_of state_ty
              |> map (rator o rator o lhs o snd o strip_forall o concl)
              |> zip fields;

(** Fext info **)

(* Variables only used for modeling, never read directly *)
val model_fext_vars = ["mem", "io_events", "interrupt_state"];

local
  val raw = zip (TypeBase.fields_of fext_ty) (TypeBase.accessors_of fext_ty)
            |> filter (not o flip mem model_fext_vars o fst o fst)
in
val fext_fields = map (fst o fst) raw;

val fext_accessors = map (fn ((name, _), acc) => (name, acc)) raw
                     |> snd_map (rator o lhs o snd o strip_forall o concl);
end

fun predicate_for_var var = let
 val acc = lookup var accessors
in
 acc |> type_of |> dom_rng |> snd |> predicate_for_type_ty
end;

end
