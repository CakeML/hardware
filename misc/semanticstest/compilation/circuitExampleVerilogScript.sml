open hardwarePreamble;

open verilogTranslatorLib verilogLiftLib verilogPrintLib;
open circuitExampleTheory;

val _ = new_theory "circuitExampleVerilog";

val _ = prefer_num ();

fun get_inputs prg =
 ``vreads ^prg``
 |> EVAL |> concl |> rhs |> dest_list |> fst
 |> map fromHOLstring;

fun get_output prg =
 ``vwrites ^prg``
 |> EVAL |> concl |> rhs |> dest_list |> fst
 |> hd |> fromHOLstring;

local
 val tys = TypeBase.fields_of state_ty
in
val add_types =
 map (fn var => (var, lookup var tys))
end;

val VBoolver2str_def = Define `
 (VBoolver2str (VArray _) = INL TypeError) /\
 (VBoolver2str (VBool b) = INR (if b then #"1" else #"0"))`;

val ver2str_def = Define `
 (ver2str (VArray vs) = sum_mapM VBoolver2str vs) /\
 (ver2str (VBool F) = INR "0") /\
 (ver2str (VBool T) = INR "1")`;

val get_result = Define `
 (get_result name (INR s) = sum_bind (mget_var s.vars name) ver2str) /\
 (get_result name (INL err) = INL err)`;

(*
``get_result
   "r3"
   (prun ARB <| vars := [("a3", w2ver (5w:word3));
                         ("b3", w2ver (4w:word3));
                         ("r3", w2ver (0w:word3))] |> ^ex1v)``
|> EVAL |> concl |> rhs |> dest_inr |> fst |> fromHOLstring
*)

fun all_cases xs =
 case xs of
  [] => [[]]
 | (x::xs) => map (cons x) (all_cases xs) @
              (if x = Arbnumcore.zero then [] else all_cases (Arbnumcore.less1 x :: xs));

(*
val all_cases_def = Define `
 (all_cases []  = [[]]) /\
 (all_cases (x::xs) = (MAP (CONS x) (all_cases xs) ++
                      (if x = 0 then [] else all_cases (x - 1 :: xs))))`;
*)

fun build_test_cases circuit_def = let

val ex1_trans = hol2hardware_step_function circuit_def
val ex1v = ex1_trans |> concl |> EvalS_get_prog

val ins = ex1v |> get_inputs |> add_types

val outs_var = ex1v |> get_output
val outs = outs_var |> Portable.single |> add_types |> hd
val outs_var = outs_var |> fromMLstring

val ins_cases = 
 ins
 |> map (Arbnumcore.less1 o curry Arbnumcore.pow Arbnumcore.two o
         dest_numeric_type o dest_word_type o snd)
 |> all_cases;

val vars_cases =
 ins_cases |> map (cons Arbnumcore.zero);

fun ty_size ty =
 if is_word_type ty then
  ty |> dest_word_type |> dest_numeric_type
 else if ty = bool then
  Arbnumcore.zero (* special handling of bool, only allowed to occur on lhs ... *)
 else
  failwith "Cannot calculate size of type"

val sign = (outs |> (fn (var, s) => (fromMLstring var, ty_size s))) ::
           (ins |> map (fn (var, s) => (fromMLstring var, s |> dest_word_type |> dest_numeric_type)))
fun to_hol_input_bool var = mk_pair (var, mk_VBool F)
fun to_hol_input_word d var size = mk_pair (var, mk_w2ver (mk_word (d, size)))
fun to_hol_input (d, (var, size)) =
 if size = Arbnumcore.zero then
  to_hol_input_bool var
 else
  to_hol_input_word d var size

fun to_hol_inputs ds = map to_hol_input (zip ds sign)
val envTty = ``:envT`` |> dest_list_type

val hol_ins_cases =
 vars_cases
 |> map ((fn ds => mk_list (ds, envTty)) o to_hol_inputs)
 |> map (fn x => TypeBase.mk_record (``:pstate``, [("vars", x)]))

val outs_cases =
 hol_ins_cases
(* |> flip (curry List.take) 5*)
 |> map (fn s => ``get_result ^outs_var (prun ARB ^s ^ex1v)``)
 |> map EVAL
 |> map (fromHOLstring o fst o dest_inr o rhs o concl)

val expected =
 zip ins_cases outs_cases

val code = vprog_print ex1v

in
 (code, ins, outs, expected)
end;

(* iverilog test *)

val dest_word_type_num = dest_numeric_type o dest_word_type;

fun format_num v ty = let
 val prefix = if is_word_type ty then
                (ty |> dest_word_type_num |> Arbnumcore.toString) ^ "'d"
              else
                "1'd"
in
 prefix ^ (Arbnumcore.toString v)
end;

fun format_bin v ty = let
 val prefix = if is_word_type ty then
                (ty |> dest_word_type_num |> Arbnumcore.toString) ^ "'b"
              else
                "1'b"
in
 prefix ^ v
end;

fun format_test_case code ins outs (datain, dataout) = let
 val vars = zip ins datain
 val vars = map (fn ((var, ty), v) => var ^ " = " ^ format_num v ty ^ ";\n") vars
 val vars = concat vars
 val cond = (fst outs) ^ " != " ^ format_bin dataout (snd outs)
in
 vars ^
 code ^
 "\n" ^
 "if (" ^ cond ^ ") begin\n" ^
 " $display(\"ERROR: code = " ^ (substring (code, 0, size code - 1)) ^ ", cond = " ^ cond ^ "\");\n" ^
 " $display(\"" ^ (fst outs) ^ " = %b\", " ^ (fst outs) ^ ");\n" ^
 " $finish();\n" ^
 "end\n\n"
end;

fun gen_exes n =
 List.tabulate (n, (fn i => "ex" ^ Int.toString (1 + i) ^ "_def"))
 |> String.concatWith ", ";

(* gen_exes 22 *)
val exes = [ex1_def, ex2_def, ex3_def, ex4_def, ex5_def, ex6_def, ex7_def, ex8_def, ex9_def, ex10_def, ex11_def, ex12_def, ex13_def, ex14_def, ex15_def, ex16_def, ex17_def, ex18_def, ex19_def, ex20_def, ex21_def, ex22_def];

val tests = map build_test_cases exes;

(*
val (code, ins, outs, expected) = build_test_cases ex1_def;
(map (format_test_case code ins outs) expected |> concat)
*)

val ss =
 "`timescale 1ns / 1ps\n" ^
 "\n" ^
 "module Main();\n" ^

 (TypeBase.fields_of state_ty
  |> map (fn (var, ty) => print_var var (predicate_for_type_ty ty) ^ ";\n")
  |> String.concat) ^

 "\n" ^
 "initial begin\n" ^

 (map
 (fn (code, ins, outs, expected) => 
  map (format_test_case code ins outs) expected |> concat)
 (*(List.take (tests, 5))*)
 tests
 |> concat) ^

 "$finish();\n" ^
 "end\n" ^
 "\n" ^
 "endmodule";

(* writeFile "Main.sv" ss; *)

val _ = export_theory ();
