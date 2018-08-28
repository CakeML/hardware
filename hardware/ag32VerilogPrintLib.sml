open ag32VerilogTheory ag32EqTheory;

open verilogTranslatorConfigLib verilogTranslatorCoreLib verilogTranslatorLib verilogPrintLib;

open verilogSyntax;

val input_vars = ["data_in"];
val output_vars = ["data_out", "command", "data_addr", "PC" (* for inst_addr *), "data_wdata", "data_wstrb", "interrupt_req"];
val external_vars = input_vars @ output_vars;

(* Fext vars *)

fun print_fext_var (var, ty) = let
  val var_type = predicate_for_type_ty ty
in
  print_var var var_type
end;

(* For filtering out modeling variables *)
fun is_fext_var (var, _) = not (mem var model_fext_vars);

(* Internal vars *)

local
  val s = mk_var ("t", state_ty)
  val data = INIT_def |> SPEC_ALL |> concl |> rhs |> strip_conj
in
val init_assoc =
 foldr (fn (spec, l) => if is_neg spec then let
                          val var = hol2hardware_exp s (dest_neg spec) |> concl |> Eval_get_prog |> dest_Var |> fromHOLstring
                          val v = exp_print ``Const (VBool F)``
                        in
                          (var, v) :: l
                        end else if is_eq spec andalso is_word_literal (rhs spec) then let
                          val (var, _, const) = hol2hardware_exp s spec |> concl |> Eval_get_prog |> dest_Cmp
                          val var = dest_Var var |> fromHOLstring
                        in
                          (var, exp_print const) :: l
                        end else
                          l) [] data
end;

fun print_interface_var (var, ty) = let
  val var_type = ty |> predicate_for_type_ty
  val init_val = assoc1 var init_assoc
  val var = print_var var var_type
in
  case init_val of
      SOME (_, v) => var ^ " = " ^ v
    | NONE => var
end;

fun is_internal_var (var, _) =
 not (exists (equal var) external_vars);

(* Internal let-induced vars *)

val internal_let_vars =
 ag32types_def
 |> concl |> rhs |> dest_list |> fst
 |> map (fn p =>
            let
              val (var, ty) = dest_pair p
              val var = fromHOLstring var
              val ty = newtype2vertype ty
            in
              "automatic " ^ ty ^ " " ^ var ^ ";\n"
            end)
 |> concat;

let
  val ss =
   "`timescale 1ns / 1ps\n" ^
   "\n" ^
   "module processor(\n" ^
   "  input clk,\n" ^
   (TypeBase.fields_of state_ty
    |> filter (fn (var, _) => mem var input_vars)
    |> map (fn p => "  input " ^ print_interface_var p ^ ",\n")
    |> String.concat) ^

   (TypeBase.fields_of state_ty
    |> filter (fn (var, _) => mem var output_vars)
    |> map (fn p => "  output " ^ print_interface_var p ^ ",\n")
    |> String.concat) ^

   (TypeBase.fields_of fext_ty
    |> filter is_fext_var
    |> map (fn var => "  input " ^ print_fext_var var)
    |> String.concatWith ",\n") ^
   ");\n\n" ^

   (TypeBase.fields_of state_ty
    |> filter is_internal_var
    |> map (fn p => print_interface_var p ^ ";\n")
    |> concat) ^

   "\nalways_ff @ (posedge clk) begin\n" ^
   (* All let variables are from processor currently, so can do this in a simple way currently *)
   internal_let_vars ^ "\n" ^
   vprog_print prog_comm ^
   "end\n" ^

   "\nalways_ff @ (posedge clk) begin\n" ^
   vprog_print prog_acc_comm ^
   "end\n" ^

   "\n" ^ "endmodule\n"
in
  writeFile "processor.sv" ss
end;
