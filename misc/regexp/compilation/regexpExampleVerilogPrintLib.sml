open regexpExampleVerilogTheory;

open verilogTranslatorConfigLib verilogTranslatorCoreLib verilogTranslatorLib verilogPrintLib;

open verilogSyntax;

val ERR = Feedback.mk_HOL_ERR "regexpExampleVerilogPrintLib";

(* test: circuit_correct_regexp_verilog *)

(* verilog code: *)
regexpv_def |> concl |> rhs |> vprog_print |> print

(* variables: *)
``var_type_print relMtypes`` |> EVAL

(*

We do not treat initialization formally,
but given how this code looks like we probably should:

fun vectorToList vec = Vector.foldr (op ::) [] vec;
fun toVerilogList l =
 l
 |> rev
 |> String.concatWith ", "
 |> (fn l => "'{" ^ l ^ "}");

fun toVerilogListInit name l =
 l
 |> mapi (fn i => fn e => name ^ "[" ^ (Int.toString i) ^ "] = " ^ e);

regexp_res here is from regexpExampleScript.sml:

 regexp_res
 |> #final
 |> vectorToList
 |> rev
 |> map (fn b => if b then "1" else "0")
 |> String.concatWith ", "
 |> (fn bs => "'{" ^ bs ^ "}")

 regexp_res
 |> #table
 |> vectorToList
 |> map vectorToList
 |> map (map Int.toString)
 |> map toVerilogList
 |> toVerilogListInit "next_state_info"
 |> String.concatWith ";\n"
 |> print
 
 regexp_res
 |> #table
 |> vectorToList
 |> tl
 |> tl
 |> hd
 |> vectorToList
 |> el 112

state_size
hfinal
htable

*)
