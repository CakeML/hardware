open preamble;

open wordsTheory;

open listSyntax stringSyntax;

open tinyTheory;

(* For EVAL *)
open bitstringTheory wordsLib;

val _ = new_theory "tinyTestPrograms";

val add_two_numbers_def = Define `
 add_two_numbers = [
  Out (fAdd, 0w, Imm 1w, Imm 1w);

  LoadConstant (0w, F, 20w);
  LoadConstant (1w, F, 30w);
  Normal (fAdd, 2w, Reg 1w, Reg 0w);
  StoreMEM (fAdd, 3w, Imm 7w, Reg 2w);
  LoadMEM (4w, Reg 2w);

  Out (fAdd, 4w, Reg 4w, Imm 0w);
  Jump (fAdd, 5w, Imm 0w)
 ]`;

val plus_by_acc_def = Define `
 plus_by_acc = [
  LoadConstant (0w, F, 255w);   (* 0000_0000_1111_1111 mask *)
  LoadConstant (1w, F, 65280w); (* 1111_1111_0000_0000 mask *)
  LoadConstant (2w, F, 256w);   (* Shift constant *)

  In (3w);

  Normal (fAnd, 4w, Reg 0w, Reg 3w); (* low mask *)

  Normal (fAnd, 5w, Reg 1w, Reg 3w); (* high mask *)
  Normal (fMul, 5w, Reg 2w, Reg 5w); (* shift *)

  Normal (fOr, 4w, Reg 4w, Reg 5w);

  Accelerator (5w, Reg 4w);
  Out (fSnd, 6w, Imm 0w, Reg 5w);
  Jump (fSnd, 6w, Imm 12w)
 ]`;

(** High-tech assembler **)

(*

computeLib.add_funs [Encode_def, enc_def, ri2bits_def];

fun build_dump prg = let
  val prg = prg |> concl |> lhs
  val dump = EVAL ``MAP (word_to_bin_string o Encode) ^prg``
             |> concl |> rhs
             |> dest_list |> fst |> map (fn tm => fromHOLstring tm ^ "\n")
             |> concat
in
  writeFile "prg.data" dump
end;

val () = build_dump plus_by_acc_def;

*)

val _ = export_theory ();
