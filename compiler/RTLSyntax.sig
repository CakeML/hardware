signature RTLSyntax =
sig
  include Abbrev

  (* Values *)
  val CBool_tm : term
  val dest_CBool : term -> term
  val is_CBool : term -> bool
  val mk_CBool : term -> term

  (* Vars *)
  val RegVar_tm : term
  val dest_RegVar : term -> term * term
  val is_RegVar : term -> bool
  val mk_RegVar : term * term -> term

  val NetVar_tm : term
  val dest_NetVar : term -> term
  val is_NetVar : term -> bool
  val mk_NetVar : term -> term
  
  (* Cell inputs *)
  val NoIndexing_tm : term
  val is_NoIndexing : term -> bool

  val Indexing_tm : term
  val dest_Indexing : term -> term
  val is_Indexing : term -> bool
  val mk_Indexing : term -> term

  val SliceIndexing_tm : term
  val dest_SliceIndexing : term -> term * term
  val is_SliceIndexing : term -> bool
  val mk_SliceIndexing : term * term -> term
                            
  val ConstInp_tm : term
  val dest_ConstInp : term -> term
  val is_ConstInp : term -> bool
  val mk_ConstInp : term -> term

  val ExtInp_tm : term
  val dest_ExtInp : term -> term * term
  val is_ExtInp : term -> bool
  val mk_ExtInp : term * term -> term

  val VarInp_tm : term
  val dest_VarInp : term -> term * term
  val is_VarInp : term -> bool
  val mk_VarInp : term * term -> term

  val cell_input_ty : hol_type

  (* Outs *)
  val OutInp_tm : term
  val dest_OutInp : term -> term
  val is_OutInp : term -> bool
  val mk_OutInp : term -> term

  val OutInps_tm : term
  val dest_OutInps : term -> term
  val is_OutInps : term -> bool
  val mk_OutInps : term -> term

  (* Cell2 *)
  val CAnd_tm : term
  val COr_tm : term
  val CEqual_tm : term
                               
  (* Cells *)
  val NDetCell_tm : term
  val dest_NDetCell : term -> term * term
  val is_NDetCell : term -> bool
  val mk_NDetCell : term * term -> term

  val Cell1_tm : term
  val dest_Cell1 : term -> term * term * term
  val is_Cell1 : term -> bool
  val mk_Cell1 : term * term * term -> term

  val Cell2_tm : term
  val dest_Cell2 : term -> term * term * term * term
  val is_Cell2 : term -> bool
  val mk_Cell2 : term * term * term * term -> term

  val CellMux_tm : term
  val dest_CellMux : term -> term * term * term * term
  val is_CellMux : term -> bool
  val mk_CellMux : term * term * term * term -> term

  val CellLUT_tm : term
  val dest_CellLUT : term -> term * term * term
  val is_CellLUT : term -> bool
  val mk_CellLUT : term * term * term -> term

  val Carry4_tm : term
  val dest_Carry4 : term -> term * term * term * term * term
  val is_Carry4 : term -> bool
  val mk_Carry4 : term * term * term * term * term -> term

  val Circuit_tm : term
  val dest_Circuit : term -> term * term * term * term * term
  val is_Circuit : term -> bool
  val mk_Circuit : term * term * term * term * term -> term

  val cell_ty : hol_type

  val CBool_t_tm : term
  val is_CBool_t : term -> bool

  val CArray_t_tm : term
  val dest_CArray_t : term -> term
  val is_CArray_t : term -> bool
  val mk_CArray_t : term -> term

  val is_cget_var : term -> bool
  val is_cell_run : term -> bool
end
