open ag32VerilogTheory;

open verilogTranslatorConfigLib verilogTranslatorCoreLib verilogTranslatorLib verilogPrintLib;

open verilogSyntax;

val ERR = Feedback.mk_HOL_ERR "ag32VerilogPrintLib";

val input_vars = ["data_in"];
val output_vars = ["data_out", "command", "data_addr", "PC" (* for inst_addr *),
                   "data_wdata", "data_wstrb", "interrupt_req"];
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
  val get_var = fromHOLstring o rand o rand
  val s = mk_var ("t", state_ty)
  fun to_ver_constant tm = hol2hardware_exp s tm |> concl |> Eval_get_prog
  fun spec_to_init spec =
      if is_BOOL spec then let
        val (v, var) = dest_BOOL spec
        val v = to_ver_constant v
        val var = get_var var
      in
        (var, exp_print v)
      end else if is_WORD spec then let
        val (v, var) = dest_WORD spec
        val v = to_ver_constant v
        val var = get_var var
      in
        (var, exp_print v)
      end else if is_WORD_ARRAY spec then let
        val (v, var) = dest_WORD_ARRAY spec
        val v = v |> dest_abs |> snd
        val var = get_var var
      in
        (* TODO: Special handling for this for now *)
        if v = ``0w:word32`` then
          (var, "0")
        else
          raise UnableToTranslate (spec, "Too general WORD_ARRAY expression for current implementation")
      end else
      raise UnableToTranslate (spec, "Unknown case")
in
val init_assoc = map spec_to_init (INIT_verilog_def |> SPEC_ALL |> concl |> rhs |> strip_conj)
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

(*val [prog_comm, prog_acc_comm] = computer_def |> concl |> rhs |> EVAL |> concl |> rhs |> dest_list |> fst;*)

(* Sanity check output_vars *)

val cvars = cvars_def |> concl |> rhs |> dest_list |> fst |> map fromHOLstring;

val () = if (not (all (fn v => mem v cvars) output_vars)) then
         raise ERR "cvars check" "Some external variable not in cvars!"
        else
         ();

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
   vprog_print (prog_comm_def |> concl |> rhs) ^
   "end\n" ^

   "\nalways_ff @ (posedge clk) begin\n" ^
   vprog_print (prog_acc_comm_def |> concl |> rhs) ^
   "end\n" ^

   "\n" ^ "endmodule\n"
in
  writeFile "processor.sv" ss
end;
