structure RTLSyntax :> RTLSyntax =
struct

open HolKernel Abbrev;
open boolSyntax;
open RTLTheory;

(* Internal helpers *)
fun list_of_5tuple (a, b, c, d, e) = [a, b, c, d, e];
fun mk_5op tm = HolKernel.list_mk_icomb tm o list_of_5tuple;
fun dest_5op c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5]) =>
         if same_const t c then (t1, t2, t3, t4, t5) else raise e
    | _ => raise e;

val op1 = HolKernel.syntax_fns1 "RTL";
val op2 = HolKernel.syntax_fns2 "RTL";
val op3 = HolKernel.syntax_fns3 "RTL";
val op4 = HolKernel.syntax_fns4 "RTL";
val op5 = syntax_fns {n = 5, make = mk_5op, dest = dest_5op} "RTL";

(* Values *)
val (CBool_tm, mk_CBool, dest_CBool, is_CBool) = op1 "CBool";

(* Vars *)
val (RegVar_tm, mk_RegVar, dest_RegVar, is_RegVar) = op2 "RegVar";
val (NetVar_tm, mk_NetVar, dest_NetVar, is_NetVar) = op1 "NetVar";

(* Cell inputs *)
val NoIndexing_tm = “RTL$NoIndexing”;
fun is_NoIndexing tm = tm ~~ NoIndexing_tm;
val (Indexing_tm, mk_Indexing, dest_Indexing, is_Indexing) = op1 "Indexing";
val (SliceIndexing_tm, mk_SliceIndexing, dest_SliceIndexing, is_SliceIndexing) = op2 "SliceIndexing";

val (ConstInp_tm, mk_ConstInp, dest_ConstInp, is_ConstInp) = op1 "ConstInp";
val (ExtInp_tm, mk_ExtInp, dest_ExtInp, is_ExtInp) = op2 "ExtInp";
val (VarInp_tm, mk_VarInp, dest_VarInp, is_VarInp) = op2 "VarInp";

val cell_input_ty = mk_type ("cell_input", []);

(* Outs *)
val (OutInp_tm, mk_OutInp, dest_OutInp, is_OutInp) = op1 "OutInp";
val (OutInps_tm, mk_OutInps, dest_OutInps, is_OutInps) = op1 "OutInps";

(* Cells *)
val (NDetCell_tm, mk_NDetCell, dest_NDetCell, is_NDetCell) = op2 "NDetCell";
val (Cell1_tm, mk_Cell1, dest_Cell1, is_Cell1) = op3 "Cell1";
val (Cell2_tm, mk_Cell2, dest_Cell2, is_Cell2) = op4 "Cell2";
val (CellMux_tm, mk_CellMux, dest_CellMux, is_CellMux) = op4 "CellMux";
val (CellLUT_tm, mk_CellLUT, dest_CellLUT, is_CellLUT) = op3 "CellLUT";
val (Carry4_tm, mk_Carry4, dest_Carry4, is_Carry4) = op5 "Carry4";

(* Circuit *)
val (Circuit_tm, mk_Circuit, dest_Circuit, is_Circuit) = op5 "Circuit";

(* Types *)
val cell_ty = mk_type ("cell", []);

val CBool_t_tm = “CBool_t”;
fun is_CBool_t tm = tm ~~ CBool_t_tm;

val (CArray_t_tm, mk_CArray_t, dest_CArray_t, is_CArray_t) = op1 "CArray_t";

(* Semantics *)
val (cget_var_tm, mk_cget_var, dest_cget_var, is_cget_var) = op2 "cget_var";
val (cell_run_tm, mk_cell_run, dest_cell_run, is_cell_run) = op3 "cell_run";

end
