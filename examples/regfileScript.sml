open hardwarePreamble;

open translatorTheory translatorCoreLib;

open blastLib;

val _ = new_theory "regfile";

val _ = prefer_num ();

(* clk is implicitly assumed to exist *)
Datatype:
  ext_state =
  <| rst : bool
   ; we3 : bool
   ; a1  : word6
   ; a2  : word6
   ; a3  : word6
   ; wd3 : word32
  |>
End

Datatype:
  state =
  <| rf : word6 -> word32
   ; rd1 : word32
   ; rd2 : word32
  |>
End

Definition rf_ff_def:
  rf_ff (fext : ext_state) (s : state) (s' : state) =
   if fext.we3 then
    (s' with rf := (fext.a3 =+ fext.wd3) s'.rf)
   else
    s'
End

Definition rd1_comb_def:
  rd1_comb (fext : ext_state) (s : state) (s' : state) =
    s' with rd1 := if fext.a1 <> 0w then s.rf fext.a1 else 0w
End

Definition rd2_comb_def:
  rd2_comb (fext : ext_state) (s : state) (s' : state) =
    s' with rd2 := if fext.a2 <> 0w then s.rf fext.a2 else 0w
End

val init_tm = add_x_inits “<|
     rf := K 0w
   ; rd1 := 0w
   ; rd2 := 0w
 |>”

Definition regfile_init_def:
  regfile_init (fbits : num -> bool) = ^init_tm
End

Definition udma_def:
  udma = mk_module
          (procs [ rf_ff ])
          (procs [ rd1_comb ; rd2_comb ])
          regfile_init
End

val _ = export_theory ();
