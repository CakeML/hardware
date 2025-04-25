open hardwarePreamble;

open regfileTheory;

open translatorLib verilogPrintLib;

val _ = new_theory "regfileCompile";

local
 val module_def = udma_def;
 val abstract_fields = [];
 val outputs = ["rd1", "rd2"];
 val comms = ["rf"];
in
 val trans_thm = module2hardware_old udma_def abstract_fields outputs comms
end

val verilogstr =
 definition"udma_v_def"
 |> REWRITE_RULE [definition"udma_v_seqs_def", definition"udma_v_combs_def",
 definition"udma_v_decls_def"]
 |> concl
 |> rhs
 |> verilog_print "udma";

print verilogstr;

val _ = export_theory ();
