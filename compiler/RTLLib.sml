structure RTLLib =
struct

open hardwarePreamble sumExtraTheory RTLTheory;

fun cell_run_tac rw_tac =
 TRY (rename1 `NDetCell out t`) \\
 TRY (rename1 `Cell1 t out in1`) \\
 TRY (rename1 `Cell2 t out in1 in2`) \\ 
 TRY (rename1 `CellMux out in1 in2 in3`) \\
 TRY (rename1 `CellLUT out ins tb`) \\ TRY (Cases_on `t`) \\
 rw_tac [sum_bind_INR, cell_run_def,
         ndetcell_run_def,
         cell1_run_def,
         cell2_run_def,
         cellMux_run_def,
         cellLUT_run_def,
         cellCarry4_run_def];

end
