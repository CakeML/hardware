structure verilogPrintLib =
struct

open hardwarePreamble;

open wordsSyntax stringSyntax listSyntax numSyntax pairSyntax optionSyntax;

open verilogTheory verilogSyntax;

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
fun op_to_string_space print_tm op_tm = " " ^ (op_to_string print_tm op_tm) ^ " ";

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

  else if is_InputVar tm then
    tm |> dest_InputVar |> fromHOLstring

  else if is_ArrayIndex tm then let
    val (var, is) = dest_ArrayIndex tm
    val var = dest_Var_generic var
  in
    (fromHOLstring var) ^ (exp_print_list is)
  end

  else if is_ArraySlice tm then let
    val (var, is, high_bound, low_bound) = dest_ArraySlice tm
    val var = dest_Var_generic var
  in
    (fromHOLstring var) ^ (exp_print_list is) ^ "[" ^ (dest_numeral_to_string high_bound) ^ ":" ^ (dest_numeral_to_string low_bound) ^ "]"
  end

  else if is_ArrayConcat tm then let
    val (ltm, rtm) = dest_ArrayConcat tm
  in
    "{" ^ (exp_print ltm) ^ ", " ^ (exp_print rtm) ^ "}"
  end

  else if is_InlineIf tm then let
    val (ctm, ltm, rtm) = dest_InlineIf tm
  in
    (exp_print_paren ctm) ^ " ? " ^ (exp_print_paren ltm) ^ " : " ^ (exp_print_paren rtm)
  end

  else if is_BUOp tm then let
    val (uop, exp) = dest_BUOp tm
    val uop = op_to_string buop_print_tm uop
  in
    uop ^ (exp_print_paren exp)
  end

  else if is_BBOp tm then let
    val (exp1, bop, exp2) = dest_BBOp tm
    val bop = op_to_string_space bbop_print_tm bop
  in
    (exp_print_paren exp1) ^ bop ^ (exp_print_paren exp2)
  end

  else if is_ABOp tm then let
    val (exp1, bop, exp2) = dest_ABOp tm
    val bop = op_to_string_space abop_print_tm bop
  in
    (exp_print_paren exp1) ^ bop ^ (exp_print_paren exp2)
  end

  else if is_Shift tm then let
    val (exp1, shift, exp2) = dest_Shift tm
  in
    if is_ShiftArithR shift then
      "{$signed(" ^ (exp_print exp1) ^ ") >>> (" ^ (exp_print exp2) ^ ")}"
    else if is_ShiftLogicalL shift then
      (exp_print_paren exp1) ^ " << " ^ (exp_print_paren exp2)
    else if is_ShiftLogicalR shift then
      (exp_print_paren exp1) ^ " >> " ^ (exp_print_paren exp2)
    else
      failwith "Unknown shift operator"
  end

  else if is_Arith tm then let
    val (exp1, bop, exp2) = dest_Arith tm
    val bop = op_to_string_space arith_print_tm bop
  in
    (exp_print_paren exp1) ^ bop ^ (exp_print_paren exp2)
  end

  else if is_Cmp tm then let
    val (exp1, cmp, exp2) = dest_Cmp tm
    val exp1' = exp_print_paren exp1
    val exp2' = exp_print_paren exp2
  in
    if is_ArrayEqual cmp then
      exp1' ^ " == " ^ exp2'
    else if is_ArrayNotEqual cmp then
      exp1' ^ " != " ^ exp2'
    else if is_LessThan cmp then
      "{$signed(" ^ (exp_print exp1) ^ ") < $signed(" ^ (exp_print exp2) ^ ")}"
    else if is_LowerThan cmp then
      exp1' ^ " < " ^ exp2'
    else if is_LessThanOrEqual cmp then
      "{$signed(" ^ (exp_print exp1) ^ ") <= $signed(" ^ (exp_print exp2) ^ ")}"
    else if is_LowerThanOrEqual cmp then
      exp1' ^ " <= " ^ exp2'
    else
      failwith "Unknown shift operator"
  end

  else if is_Resize tm then let
    val (exp, resize, width) = dest_Resize tm
    val exp = exp_print exp
    val width = width |> dest_numeral |> Arbnumcore.toString
  in
    if is_SignExtend resize then
      (* It's not entirely clear if additional {} are around exp here, but I don't think so... *)
      "{" ^ width ^ "'($signed(" ^ exp ^ "))}"
    else
      width ^ "'({" ^ exp ^ "})"
  end

  else
    failwith ("Unknown exp ctor.: " ^ term_to_string tm)

(* Just a hack currently *)
and exp_print_paren tm = let
  fun is_tm_skip_paren tm =
      (is_Const tm orelse is_Var tm orelse is_InputVar tm orelse is_ArrayIndex tm orelse
       is_ArraySlice tm orelse is_ArrayConcat tm)
  val skip_paren =
      if is_Resize tm then let
        val (tm, resize, _) = dest_Resize tm
      in
        is_SignExtend resize orelse is_tm_skip_paren tm
      end else
        is_tm_skip_paren tm
in
  if skip_paren then
    exp_print tm
  else
    "(" ^ (exp_print tm) ^ ")"
end

and exp_print_list tm =
    tm |> dest_list |> fst |> map (fn tm => "[" ^ exp_print tm ^ "]") |> String.concat;

fun vprog_print tm =
  if is_Skip tm then
    failwith "Cannot translate Skip"

  else if is_Seq tm then let
    val (tm1, tm2) = dest_Seq tm
  in
    (vprog_print tm1) ^ (vprog_print tm2)
  end

  (* NOTE: If false-branch is Skip, then we do not output anything for that branch *)
  else if is_IfElse tm then let
    val (ctm, ltm, rtm) = dest_IfElse tm
    val ctm = exp_print ctm
    val ltm = vprog_print ltm
  in
    if is_Skip rtm then
      "if (" ^ ctm ^ ") begin\n" ^ ltm ^ "end\n"
    else let
      val rtm = vprog_print rtm
    in
      "if (" ^ ctm ^ ") begin\n" ^ ltm ^ "end else begin\n" ^ rtm ^ "end\n"
    end
  end

  else if is_Case tm then let
    val (ctm, cases, def) = dest_Case tm
    val ctm = exp_print ctm
    val cases = cases |> dest_list |> fst |> map vprog_cases_print |> String.concat
    val def = if is_some def then let
                val def = dest_some def
              in
                "default : " ^ (vprog_print_paren def)
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

and vprog_print_paren tm =
 if is_Seq tm then
   "begin\n" ^ (vprog_print tm) ^ "end\n"
 else
   vprog_print tm

(* NOTE: Here we assume that the "lhs" will just be constants, so we do not add parens for lhs *)
and vprog_cases_print tm = let
  val (exp, prg) = dest_pair tm
  val exp = exp_print exp
  val prg = vprog_print_paren prg
in
  exp ^ " : " ^ prg
end;

fun type2vertype tm =
  if same_const BOOL_tm tm then
    "logic"
  else if same_const WORD_tm tm then let
    val size = tm |> type_of |> dom_rng |> fst |> dest_word_type
                  |> fcpSyntax.dest_numeric_type |> Arbnumcore.less1 |> Arbnumcore.toString
  in
    "logic[" ^ size ^ ":0]"
  end else if is_comb tm andalso same_const (rator tm) WORD_ARRAY_tm then let
    (* Sanity check for now: *)
    val () = if same_const WORD_tm (rand tm) then () else failwith "expected WORD"
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

fun newtype2vertype tm =
  if is_VBool_t tm then
    "logic"
  else if is_VArray_t tm then let
    val dims = dest_VArray_t tm |> map (Arbnumcore.less1 o dest_numeral)
  in
    (* TODO: Check printing order... *)
    "logic" ^ ((map (fn n => "[" ^ (Arbnumcore.toString n) ^ ":0]") dims) |> concat)
  end else
    failwith "Unknown type: " ^ (term_to_string tm);

fun print_var var ty = let
  val ty = type2vertype ty
in
  ty ^ " " ^ var
end;

end
