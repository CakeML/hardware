open hardwarePreamble;

open ag32Theory;

val _ = new_theory "ag32Paper";

val LoadConstant_clean = Q.store_thm("LoadConstant_clean",
 `!reg negate imm s.
   dfn'LoadConstant (reg, negate, imm) s =
    let v = w2w imm in
     s with <| R := (reg =+ if negate then -v else v) s.R; PC := s.PC + 4w |>`,
 rw [dfn'LoadConstant_def, incPC_def]);

val _ = export_theory ();
