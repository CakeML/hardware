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

fun dest_bool tm =
 if same_const tm T then
  true
 else if same_const tm F then
  false
 else
  failwith $ "Unknown bool: " ^ (term_to_string tm);

fun const_print tm =
 if is_w2ver tm then
  w2ver_print tm
 (* Note: maybe we should be more precise in what we print here? *)
 else if is_build_zero tm then
  "'0"
 else if is_VBool tm then
  if (tm |> dest_VBool |> dest_bool) then "1" else "0"
 else if is_n2ver tm then
  tm |> dest_n2ver |> dest_numeral |> Arbnumcore.toString (* TODO: Width here? *)
 else
  failwith ("Unknown constant type: " ^ term_to_string tm);

fun exp_print tm =
  if is_Const tm then
   tm |> dest_Const |> const_print

  else if is_Var tm then
    tm |> dest_Var |> fromHOLstring

  else if is_InputVar tm then
    tm |> dest_InputVar |> fromHOLstring

  else if is_ArrayIndex tm then let
    val (var, _, is) = dest_ArrayIndex tm
    val var = dest_Var_generic var
  in
    (fromHOLstring var) ^ "[" ^ (exp_print is) ^ "]"
  end

  else if is_ArraySlice tm then let
    val (var, (*is,*) high_bound, low_bound) = dest_ArraySlice tm
    val var = dest_Var_generic var
  in
    (fromHOLstring var) (*^ (exp_print_list is)*) ^ "[" ^ (dest_numeral_to_string high_bound) ^ ":" ^ (dest_numeral_to_string low_bound) ^ "]"
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

fun write_spec_print tm =
 if is_NoIndexing tm then
  tm |> dest_NoIndexing |> fromHOLstring
 else if is_Indexing tm then let
  val (var, _, index) = dest_Indexing tm
  val var = fromHOLstring var
 in
  var ^ "[" ^ (exp_print index) ^ "]"
 end else if is_SliceIndexing tm then let
  val (var, is, n1, n2) = dest_SliceIndexing tm
  val var = fromHOLstring var
 in
  var ^ (exp_print_list is) ^ "[" ^ (dest_numeral_to_string n1) ^ ":" ^ (dest_numeral_to_string n2) ^ "]"
 end else
  failwith ("Unknown write_spec ctor.: " ^ term_to_string tm);

fun X_print print_fun tm =
 if optionSyntax.is_none tm then
  "'x"
 else
  tm |> optionSyntax.dest_some |> print_fun;

fun vprog_print tm =
  if is_Skip tm then
    failwith "Cannot translate Skip"

  else if is_Seq tm then let
    val (tm1, tm2) = dest_Seq tm
  in
    (vprog_print tm1) ^ (if is_Skip tm2 then "" else vprog_print tm2)
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
    val (_, ctm, cases, def) = dest_Case tm
    val ctm = exp_print ctm
    val cases = cases |> dest_list |> fst |> map vprog_cases_print |> String.concat
    val def = if is_some def then let
                val def = dest_some def
              in
                if is_Skip def then
                  ""
                else
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
    val lhs = write_spec_print lhs
    val rhs = X_print exp_print rhs
  in
    lhs ^ " = " ^ rhs ^ ";\n"
  end

  else if is_NonBlockingAssign tm then let
    val (lhs, rhs) = dest_NonBlockingAssign tm
    val lhs = write_spec_print lhs
    val rhs = X_print exp_print rhs
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

fun var_print name ttm =
 if is_VBool_t ttm then
  "logic " ^ name 
 else if is_VArray_t ttm then let
  val dim = dest_VArray_t ttm |> dest_numeral |> Arbnumcore.less1
 in
  "logic[" ^ (Arbnumcore.toString dim) ^ ":0] " ^ name
 end else if is_VArray2_t ttm then let
  val (dim1, dim2) = dest_VArray2_t ttm
  val dim1 = dim1 |> dest_numeral |> Arbnumcore.less1
  val dim2 = dim2 |> dest_numeral |> Arbnumcore.less1
 in
  (* Should really have a choice here, but right not we print to unpacked arrays unconditionally *)
  (* unpacked: "logic[" ^ (Arbnumcore.toString dim2) ^ ":0] " ^ name ^ "[" ^ (Arbnumcore.toString dim1) ^ ":0]" *)
  (* packed: *) "logic[" ^ (Arbnumcore.toString dim1) ^ ":0][" ^ (Arbnumcore.toString dim2) ^ ":0]" ^ name
 end else
  failwith $ "Unknown type: " ^ (term_to_string ttm);

fun fext_print var ty =
 "input " ^ (var_print (fromHOLstring var) ty);

fun decl_print var data = let
 val ty = lookup "type" data |> var_print var
 val init = lookup "init" data |> X_print const_print
in
 ty ^ " = " ^ init
end;

fun verilog_print modulename tm = let
 val (ty, fields) = TypeBase.dest_record tm
 val _ = assert (fn _ => (ty |> dest_type |> fst) = "module") ty
 val (exts, ints) =
  lookup "decls" fields
  |> dest_list |> fst
  |> map dest_pair
  |> map (fn (f, d) => (f |> fromHOLstring, d |> TypeBase.dest_record |> snd))
  |> partition (fn (f, d) => lookup "output" d |> dest_bool)
in
  "`timescale 1ns / 1ps\n" ^
  "\n" ^
  "module " ^ modulename ^ "(\n" ^
  "  input clk,\n" ^

  (lookup "fextty" fields
   |> dest_list |> fst
   |> map dest_pair
   |> map (fn (f, d) => "  " ^ fext_print f d ^ ",\n")
   |> String.concat) ^

  (exts
   |> map (fn (f, d) => "  output " ^ decl_print f d)
   |> String.concatWith ",\n") ^
  "\n);\n\n" ^

  (ints
   |> map (fn (f, d) => decl_print f d ^ ";\n")
   |> String.concat) ^

  (lookup "combs" fields
   |> listSyntax.dest_list |> fst
   |> map (fn tm => "\nalways_comb begin\n" ^
                    vprog_print tm ^
                    "end\n")
   |> String.concat) ^

   (lookup "ffs" fields
   |> listSyntax.dest_list |> fst
   |> map (fn tm => "\nalways_ff @ (posedge clk) begin\n" ^
                    vprog_print tm ^
                    "end\n")
   |> String.concat) ^

  "\n" ^ "endmodule\n"
end;

end
