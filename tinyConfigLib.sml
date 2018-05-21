structure tinyConfigLib =
struct

open preamble;

open tinyImplTheory;

val state_ty = mk_type ("tinyImpl_state", []);

(** Various auto-generated structures for translating state operations **)

(* States that are not actual variables, only used in verification: *)
(* OLD:
val nonfields = []; (*["mem_fun"];*)
val relevant_fields = map (fn x => not (mem x nonfields)) fields;
val fields = filter_by_list fields relevant_fields;
*)
val fields = map fst (TypeBase.fields_of state_ty);

(* Variables used in communication: *)
(*val comm_fields = filter (String.isPrefix "acc_") fields;*)

val accessors = TypeBase.accessors_of state_ty
                |> map (rator o lhs o snd o strip_forall o concl)
(*              |> (flip filter_by_list) relevant_fields *)
                |> zip fields;

val updates = TypeBase.updates_of state_ty
              |> map (rator o rator o lhs o snd o strip_forall o concl)
(*            |> (flip filter_by_list) relevant_fields *)
              |> zip fields;

end
