open hardwarePreamble;

open translatorTheory translatorCoreLib;

val _ = new_theory "mixedCircuit";

(* Just a very minimal example showing that you can mix
   blocking and non-blocking assignments in one always_ff block. *)

val _ = prefer_num ();

Datatype:
 mixed_state = <| var1 : word8; var2 : word8; var3 : word8; var_comb : word8 |>
End

Datatype:
 mixed_ext_state = <| signal : word8 |>
End

Definition mixed_comb_def:
 mixed_comb (fext:mixed_ext_state) (s:mixed_state) (s':mixed_state) =
  s' with var_comb := fext.signal
End

Definition mixed_ff_def:
 mixed_ff (fext:mixed_ext_state) (s:mixed_state) (s':mixed_state) = let
  s' = s' with var1 := fext.signal;
  s' = s' with var2 := fext.signal in
  s' with var3 := s.var1 + s'.var2
End

val init_tm = add_x_inits “<| var1 := 0w; var2 := 0w; var3 := 0w |>”;

Definition mixed_init_def:
 mixed_init fbits = ^init_tm
End

Definition mixed_def:
 mixed = mk_module (procs [mixed_ff]) (procs [mixed_comb]) mixed_init
End

val _ = export_theory ();
