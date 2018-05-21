structure verilogSyntax :> verilogSyntax =
struct

open HolKernel Abbrev;
open stringSyntax;
open verilogTheory;

(* Internal helpers *)
val op1 = HolKernel.syntax_fns1 "verilog";
val op2 = HolKernel.syntax_fns2 "verilog";
val op3 = HolKernel.syntax_fns3 "verilog";
val op4 = HolKernel.syntax_fns4 "verilog";

(** Syntax for verilogTheory **)

val value_ty = ``:value``;

(** Values **)

(* TODO: Needed? *)
val (VBool_tm, mk_VBool, dest_VBool, is_VBool) = op1 "VBool"
val (VArray_tm, mk_VArray, dest_VArray, is_VArray) = op1 "VArray"

(** Expressions **)

(* Need there because need to hack when printing, other can be handled by HOL's EVAL *)

val ShiftArithR_tm = ``ShiftArithR``;
val is_ShiftArithR = same_const ShiftArithR_tm;

val ShiftLogicalL_tm = ``ShiftLogicalL``;
val is_ShiftLogicalL = same_const ShiftLogicalL_tm;

val ShiftLogicalR_tm = ``ShiftLogicalR``;
val is_ShiftLogicalR = same_const ShiftLogicalR_tm;


val ArrayEqual_tm = ``ArrayEqual``;
val is_ArrayEqual = same_const ArrayEqual_tm;

val ArrayNotEqual_tm = ``ArrayNotEqual``;
val is_ArrayNotEqual = same_const ArrayNotEqual_tm;

val LessThan_tm = ``LessThan``;
val is_LessThan = same_const LessThan_tm;

val LowerThan_tm = ``LowerThan``;
val is_LowerThan = same_const LowerThan_tm;

val LessThanOrEqual_tm = ``LessThanOrEqual``;
val is_LessThanOrEqual = same_const LessThanOrEqual_tm;

val LowerThanOrEqual_tm = ``LowerThanOrEqual``;
val is_LowerThanOrEqual = same_const LowerThanOrEqual_tm;


val SignExtend_tm = ``SignExtend``;
val is_SignExtend = same_const SignExtend_tm;


val (Const_tm, mk_Const, dest_Const, is_Const) = op1 "Const"
val (Var_tm, mk_Var, dest_Var, is_Var) = op1 "Var"
val (ArrayIndex_tm, mk_ArrayIndex, dest_ArrayIndex, is_ArrayIndex) = op2 "ArrayIndex"
val (ArraySlice_tm, mk_ArraySlice, dest_ArraySlice, is_ArraySlice) = op4 "ArraySlice"
val (InlineIf_tm, mk_InlineIf, dest_InlineIf, is_InlineIf) = op3 "InlineIf"
val (BUOp_tm, mk_BUOp, dest_BUOp, is_BUOp) = op2 "BUOp"
val (BBOp_tm, mk_BBOp, dest_BBOp, is_BBOp) = op3 "BBOp"
val (ABOp_tm, mk_ABOp, dest_ABOp, is_ABOp) = op3 "ABOp"
val (Shift_tm, mk_Shift, dest_Shift, is_Shift) = op3 "Shift"
val (Arith_tm, mk_Arith, dest_Arith, is_Arith) = op3 "Arith"
val (Cmp_tm, mk_Cmp, dest_Cmp, is_Cmp) = op3 "Cmp"
val (Resize_tm, mk_Resize, dest_Resize, is_Resize) = op3 "Resize"

(** Statements **)

val Skip_tm = ``Skip``;
val is_Skip = same_const Skip_tm;

val (Seq_tm, mk_Seq, dest_Seq, is_Seq) = op2 "Seq"
val (IfElse_tm, mk_IfElse, dest_IfElse, is_IfElse) = op3 "IfElse"
val (Case_tm, mk_Case, dest_Case, is_Case) = op3 "Case"
val (BlockingAssign_tm, mk_BlockingAssign, dest_BlockingAssign, is_BlockingAssign) = op2 "BlockingAssign"
val (NonBlockingAssign_tm, mk_NonBlockingAssign, dest_NonBlockingAssign, is_NonBlockingAssign) = op2 "NonBlockingAssign"

(* Other, and some convenience functions *)

val (_, _, dest_w2ver, is_w2ver) = op1 "w2ver"
val (_, _, dest_n2ver, is_n2ver) = op1 "n2ver"

fun mk_Var_ var = mk_Var (fromMLstring var);

(** Syntax for verilogMetaTheory, TODO: moved? **)

(*
local val s = HolKernel.syntax_fns1 "verilog" in
  val (vwrites_tm, mk_vwrites, dest_vwrites, is_vwrites) = s "vwrites"
end;
*)

end
