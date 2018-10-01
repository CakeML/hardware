open hardwarePreamble;

open wordsTheory;

open listSyntax stringSyntax;

open ag32Theory;

(* For EVAL *)
open bitstringTheory wordsLib;

val _ = new_theory "ag32Programs";

val minimal_prg_def = Define `
 minimal_prg = [
  Out (fAdd, 0w, Imm 0w, Imm 0w);
  In 1w;
  Out (fAdd, 0w, Reg 0w, Reg 1w);
  Jump (fSub, 2w, Imm 8w)
 ]`;

val minimal_prg_slow_def = Define `
 minimal_prg_slow = [
  (* 0: ... *)       LoadConstant (3w, F, 20w);
  (* 4: 810006 *)    Out (fAdd, 0w, Imm 0w, Imm 0w);
  (* 8: 2810007 *)   In 1w;
  (* 12: 406 *)      Out (fAdd, 0w, Reg 0w, Reg 1w);

  (* 16: 85000014 *) LoadConstant (2w, F, 30000w);
  (* 20: 4050480 *)  Normal (fSub, 2w, Reg 2w, Imm 1w);
  (* 24: F805030A *) JumpIfZero (fEqual, Imm (-4w), Reg 2w, Imm 0w);

  (* 28: 4D10089 *)  Jump (fSub, 2w, Reg 3w)
 ]`;

val store_test_def = Define `
 store_test = [
  (* 64 *) StoreMEM (Imm 0w, Imm 0w);
  (* 68 *) StoreMEMByte (Imm 4w, Imm 1w);
  (* 72 *) StoreMEMByte (Imm 1w, Imm 2w);
  (* 76 *) Interrupt;

  (* 80 *) Normal (fAdd, 0w, Reg 0w, Reg 0w);
  (* 84 *) Jump (fSub, 0w, Imm 4w)
 ]`;

val store_test_real_def = Define `
 store_test_real = [
  StoreMEM (Imm 0w, Reg 0w); (* <-- redundant *)

  LoadConstant (1w, F, 72w); (* H *)
  StoreMEMByte (Reg 1w, Reg 0w);

  Normal (fAdd, 0w, Imm 1w, Reg 0w);
  LoadConstant (1w, F, 69w); (* E *)
  StoreMEMByte (Reg 1w, Reg 0w);

  Normal (fAdd, 0w, Imm 1w, Reg 0w);
  LoadConstant (1w, F, 76w); (* L *)
  StoreMEMByte (Reg 1w, Reg 0w);

  Normal (fAdd, 0w, Imm 1w, Reg 0w);
  StoreMEMByte (Reg 1w, Reg 0w);

  Normal (fAdd, 0w, Imm 1w, Reg 0w);
  LoadConstant (1w, F, 79w); (* O *)
  StoreMEMByte (Reg 1w, Reg 0w);

  Normal (fAdd, 0w, Imm 1w, Reg 0w);
  LoadConstant (1w, F, 32w); (* " " (space) *)
  StoreMEMByte (Reg 1w, Reg 0w);

  (* NULL *)
  Normal (fAdd, 0w, Imm 2w, Reg 0w);
  StoreMEMByte (Imm 0w, Reg 0w);
  Normal (fSub, 0w, Reg 0w, Imm 1w);

  LoadConstant (3w, F, 48w);
  LoadConstant (4w, F, 57w);

  StoreMEMByte (Reg 3w, Reg 0w);
  Interrupt;

  Normal (fAdd, 3w, Imm 1w, Reg 3w);
  JumpIfZero (fEqual, Imm (-12w), Reg 3w, Reg 4w);

  ReservedInstr

(*  Normal (fAdd, 0w, Reg 0w, Reg 0w);
  Jump (fSub, 0w, Imm 4w) *)
 ]`;

val add_two_numbers_def = Define `
 add_two_numbers = [
  Out (fAdd, 0w, Imm 1w, Imm 1w);

  LoadConstant (0w, F, 20w);
  LoadConstant (1w, F, 30w);
  Normal (fAdd, 2w, Reg 1w, Reg 0w);
  StoreMEM (Imm 7w, Reg 2w);
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

computeLib.add_funs [Encode_def, enc_def, ri2bits_def];

(* To binary *)
fun build_dump prg = let
  val prg = prg |> concl |> lhs
  val dump = EVAL ``MAP (word_to_bin_string o Encode) ^prg``
             |> concl |> rhs
             |> dest_list |> fst |> map (fn tm => fromHOLstring tm ^ "\n")
             |> concat
in
  writeFile "prg.data" dump
end;

(* To hex ... *)
fun build_dump prg = let
  val prg = prg |> concl |> lhs
  val dump = EVAL ``(GENLIST (K "0") (64 DIV 4)) ++
                    MAP (word_to_hex_string o Encode) ^prg``
             |> concl |> rhs
             |> dest_list |> fst |> map (fn tm => fromHOLstring tm ^ "\n")
             |> concat
in
  writeFile "prg.data" dump
end;

(* TODO: To hex bytes ... *)

(* Tmp: *)
val word32_to_4bytes_def = Define `
 word32_to_4bytes (w:word32) = [(w2w w):word8; w2w (w >>> 8); w2w (w >>> 16); w2w (w >>> 24)]`;

fun build_dump prg = let
  val prg = prg |> concl |> lhs
  val dump = EVAL ``(GENLIST (K "0") 64) ++
                    (FLAT (MAP (MAP word_to_hex_string o word32_to_4bytes o Encode) ^prg))``
             |> concl |> rhs
             |> dest_list |> fst |> map (fn tm => fromHOLstring tm ^ "\n")
             |> concat
in
  writeFile "prg.data" dump
end;

(*

val () = build_dump store_test_real_def;

*)

val _ = export_theory ();
