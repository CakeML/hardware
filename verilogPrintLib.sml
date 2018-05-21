structure verilogPrintLib =
struct

open preamble;

open wordsSyntax stringSyntax listSyntax numSyntax pairSyntax optionSyntax;

open verilogTheory verilogSyntax;
open translatorCoreLib;

open verilogPrintTheory;

val buop_print_tm = ``buop_print``;
val bbop_print_tm = ``bbop_print``;
val abop_print_tm = ``abop_print``;
val arith_print_tm = ``arith_print``;

(* From some random web site: Decimal numbers without the base format and size specified are treated as signed integers, but decimal numbers with base format are treated as unsigned integers (see Arithmetic expressions with registers and integers for more details). *)
fun w2ver_print tm = let
  val (n, size) = tm |> dest_w2ver |> dest_mod_word_literal
in
  Arbnumcore.toString size ^ "'d" ^ Arbnumcore.toString n
end;

val dest_numeral_to_string = Arbnumcore.toString o dest_numeral;
fun op_to_string print_tm op_tm = mk_comb (print_tm, op_tm) |> EVAL |> concl |> rhs |> fromHOLstring;

fun exp_print tm =
  if is_Const tm then let
    val tm = dest_Const tm
  in
    if is_w2ver tm then
      w2ver_print tm
    else if is_VBool tm then let
      val tm = dest_VBool tm
    in
      if same_const T tm then
        "1"
      else if same_const F tm then
        "0"
      else
        failwith "Not a constant bool"
    end else if is_n2ver tm then
      tm |> dest_n2ver |> dest_numeral |> Arbnumcore.toString (* TODO: Width here? *)
    else
      failwith ("Unknown constant type: " ^ term_to_string tm)
  end

  else if is_Var tm then
    tm |> dest_Var |> fromHOLstring

  else if is_ArrayIndex tm then let
    val (var, is) = dest_ArrayIndex tm
  in
    (fromHOLstring var) ^ (exp_print_list is)
  end

  else if is_ArraySlice tm then let
    val (var, is, high_bound, low_bound) = dest_ArraySlice tm
  in
    (fromHOLstring var) ^ (exp_print_list is) ^ "[" ^ (dest_numeral_to_string high_bound) ^ ":" ^ (dest_numeral_to_string low_bound) ^ "]"
  end

  else if is_InlineIf tm then let
    val (ctm, ltm, rtm) = dest_InlineIf tm
  in
    "(" ^ (exp_print ctm) ^ ") ? (" ^ (exp_print ltm) ^ ") : (" ^(exp_print rtm) ^ ")"
  end

  else if is_BUOp tm then let
    val (uop, exp) = dest_BUOp tm
    val uop = op_to_string buop_print_tm uop
  in
    uop ^ "(" ^ exp_print exp ^ ")"
  end

  else if is_BBOp tm then let
    val (exp1, bop, exp2) = dest_BBOp tm
    val bop = op_to_string bbop_print_tm bop
  in
    "((" ^ exp_print exp1 ^ ") " ^ bop ^ " (" ^ exp_print exp2 ^ "))"
  end

  else if is_ABOp tm then let
    val (exp1, bop, exp2) = dest_ABOp tm
    val bop = op_to_string abop_print_tm bop
  in
    "(" ^ exp_print exp1 ^ ") " ^ bop ^ " (" ^ exp_print exp2 ^ ")"
  end

  (* LIMITATION: *)
  else if is_Shift tm then let
    val (exp1, shift, exp2) = dest_Shift tm
    val exp1 = exp_print exp1
    val exp2 = exp_print exp2
  in
    if is_ShiftArithR shift then
      "(" ^ exp1 ^ ") >> (" ^ exp2 ^ ")"
    else if is_ShiftLogicalL shift then
      "(" ^ exp1 ^ ") << (" ^ exp2 ^ ")"
    else if is_ShiftLogicalR shift then
      "$unsigned($signed(" ^ exp1 ^ ") >>> (" ^ exp2 ^ "))"
    else
      failwith "Unknown shift operator"
  end

  else if is_Arith tm then let
    val (exp1, bop, exp2) = dest_Arith tm
    val bop = op_to_string arith_print_tm bop
  in
    "(" ^ exp_print exp1 ^ ") " ^ bop ^ " (" ^ exp_print exp2 ^ ")"
  end

  (* LIMITATION: *)
  else if is_Cmp tm then let
    val (exp1, cmp, exp2) = dest_Cmp tm
    val exp1 = exp_print exp1
    val exp2 = exp_print exp2
  in
    if is_ArrayEqual cmp then
      "(" ^ exp1 ^ ") == (" ^ exp2 ^ ")"
    else if is_ArrayNotEqual cmp then
      "(" ^ exp1 ^ ") != (" ^ exp2 ^ ")"
    else if is_LessThan cmp then
      "$signed(" ^ exp1 ^ ") < $signed(" ^ exp2 ^ ")"
    else if is_LowerThan cmp then
      "(" ^ exp1 ^ ") < (" ^ exp2 ^ ")"
    else if is_LessThanOrEqual cmp then
      "$signed(" ^ exp1 ^ ") <= $signed(" ^ exp2 ^ ")"
    else if is_LowerThanOrEqual cmp then
      "(" ^ exp1 ^ ") <= (" ^ exp2 ^ ")"
    else
      failwith "Unknown shift operator"
  end

  (* LIMITATION: *)
  else if is_Resize tm then let
    val (exp, resize, _) = dest_Resize tm
    val exp = exp_print exp
  in
    if is_SignExtend resize then
      "$signed(" ^ exp ^ ")"
    else
      exp
  end

  else
    failwith ("Unknown exp ctor.: " ^ term_to_string tm)

and exp_print_list tm =
    tm |> dest_list |> fst |> map (fn tm => "[" ^ exp_print tm ^ "]") |> String.concat;

fun vprog_print tm =
  if is_Skip tm then (* TODO: This must be removed *)
    (*failwith "Cannot translate Skip"*)
    (*"SKIP;\n"*)
    "nothing = 0;\n"

  else if is_Seq tm then let
    val (tm1, tm2) = dest_Seq tm
  in
    (vprog_print tm1) ^ (vprog_print tm2)
  end

  else if is_IfElse tm then let
    val (ctm, ltm, rtm) = dest_IfElse tm
    val ctm = exp_print ctm
    val ltm = vprog_print ltm
    val rtm = vprog_print rtm
  in
    "if (" ^ ctm ^ ") begin\n" ^ ltm ^ "end else begin\n" ^ rtm ^ "end\n"
  end

  else if is_Case tm then let
    val (ctm, cases, def) = dest_Case tm
    val ctm = exp_print ctm
    val cases = cases |> dest_list |> fst |> map vprog_cases_print |> String.concat
    val def = if is_some def then let
                val def = dest_some def
              in
                "default : begin\n" ^ vprog_print def ^ "end\n"
              end else if is_none def then
                ""
              else
                failwith "Unknown default case"
  in
    "case (" ^ ctm ^ ")\n" ^ cases ^ def ^ "endcase\n"
  end

  else if is_BlockingAssign tm then let
    val (lhs, rhs) = dest_BlockingAssign tm
    val lhs = exp_print lhs
    val rhs = exp_print rhs
  in
    lhs ^ " = " ^ rhs ^ ";\n"
  end

  else if is_NonBlockingAssign tm then let
    val (lhs, rhs) = dest_NonBlockingAssign tm
    val lhs = exp_print lhs
    val rhs = exp_print rhs
  in
    lhs ^ " <= " ^ rhs ^ ";\n"
  end

  else
    failwith ("Unknown ctor: " ^ (term_to_string tm))

(* NOTE: Here we assume that the "lhs" will just be constants, as is the case for Tiny, so we do not add parens for lhs *)
and vprog_cases_print tm = let
  val (exp, prg) = dest_pair tm
  val exp = exp_print exp
  val prg = vprog_print prg
in
  exp ^ " : begin\n" ^ prg ^ "end\n"
end;

fun type2vertype tm =
  if same_const BOOL_tm tm then
    "logic"
  else if same_const WORD_tm tm then let
    val size = tm |> type_of |> dom_rng |> fst |> dest_word_type
                  |> fcpSyntax.dest_numeric_type |> Arbnumcore.less1 |> Arbnumcore.toString
  in
    "logic[" ^ size ^ ":0]"
  end else if same_const WORD_ARRAY_tm tm then let
    val (size1, size2) = tm |> type_of |> dom_rng |> fst |> dom_rng |> list_of_pair
                            |> map (fcpSyntax.dest_numeric_type o
                                    dest_word_type)
                            |> pair_of_list
    val size1 = Arbnumcore.toString (Arbnumcore.less1 (Arbnumcore.pow (Arbnumcore.two, size1)))
    val size2 = Arbnumcore.toString (Arbnumcore.less1 size2)
  in
    "logic[" ^ size1 ^ ":0][" ^ size2 ^ ":0]"
  end else
    failwith "Unknown type";

fun print_var var ty = let
  val var = fromHOLstring var
  val ty = type2vertype ty
in
  ty ^ " " ^ var ^ ";\n"
end;

end
