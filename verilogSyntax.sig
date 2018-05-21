signature verilogSyntax =
sig
  include Abbrev

  (* Syntax for both verilogTheory and verilogMetaTheory *)

  val value_ty : hol_type

  (* Values *)
  val dest_VBool : term -> term
  val is_VBool : term -> bool

  (* Expressions *)

  val is_ShiftArithR : term -> bool
  val is_ShiftLogicalL : term -> bool
  val is_ShiftLogicalR : term -> bool

  val is_ArrayEqual : term -> bool
  val is_ArrayNotEqual : term -> bool
  val is_LessThan : term -> bool
  val is_LowerThan : term -> bool
  val is_LessThanOrEqual : term -> bool
  val is_LowerThanOrEqual : term -> bool

  val is_SignExtend : term -> bool

  val ABOp_tm : term
  val Arith_tm : term
  val ArrayIndex_tm : term
  val ArraySlice_tm : term
  val BBOp_tm : term
  val BUOp_tm : term
  val Cmp_tm : term
  val Const_tm : term
  val InlineIf_tm : term
  val Resize_tm : term
  val Shift_tm : term
  val Var_tm : term
  val dest_ABOp : term -> term * term * term
  val dest_Arith : term -> term * term * term
  val dest_ArrayIndex : term -> term * term
  val dest_ArraySlice : term -> term * term * term * term
  val dest_BBOp : term -> term * term * term
  val dest_BUOp : term -> term * term
  val dest_Cmp : term -> term * term * term
  val dest_Const : term -> term
  val dest_InlineIf : term -> term * term * term
  val dest_Resize : term -> term * term * term
  val dest_Shift : term -> term * term * term
  val dest_Var : term -> term
  val is_ABOp : term -> bool
  val is_Arith : term -> bool
  val is_ArrayIndex : term -> bool
  val is_ArraySlice : term -> bool
  val is_BBOp : term -> bool
  val is_BUOp : term -> bool
  val is_Cmp : term -> bool
  val is_Const : term -> bool
  val is_InlineIf : term -> bool
  val is_Resize : term -> bool
  val is_Shift : term -> bool
  val is_Var : term -> bool
  val mk_ABOp : term * term * term -> term
  val mk_Arith : term * term * term -> term
  val mk_ArrayIndex : term * term -> term
  val mk_ArraySlice : term * term * term * term -> term
  val mk_BBOp : term * term * term -> term
  val mk_BUOp : term * term -> term
  val mk_Cmp : term * term * term -> term
  val mk_Const : term -> term
  val mk_InlineIf : term * term * term -> term
  val mk_Resize : term * term * term -> term
  val mk_Shift : term * term * term -> term
  val mk_Var : term -> term

  (* Statements *)

  val Skip_tm : term
  val is_Skip : term -> bool

  val BlockingAssign_tm : term
  val Case_tm : term
  val IfElse_tm : term
  val NonBlockingAssign_tm : term
  val Seq_tm : term
  val dest_BlockingAssign : term -> term * term
  val dest_Case : term -> term * term * term
  val dest_IfElse : term -> term * term * term
  val dest_NonBlockingAssign : term -> term * term
  val dest_Seq : term -> term * term
  val is_BlockingAssign : term -> bool
  val is_Case : term -> bool
  val is_IfElse : term -> bool
  val is_NonBlockingAssign : term -> bool
  val is_Seq : term -> bool
  val mk_BlockingAssign : term * term -> term
  val mk_Case : term * term * term -> term
  val mk_IfElse : term * term * term -> term
  val mk_NonBlockingAssign : term * term -> term
  val mk_Seq : term * term -> term

  (* Other, and some convenience functions *)

  val dest_w2ver : term -> term
  val is_w2ver : term -> bool

  val dest_n2ver : term -> term
  val is_n2ver : term -> bool

  val mk_Var_ : string -> term

end
