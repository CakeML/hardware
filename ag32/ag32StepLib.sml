structure ag32StepLib =
struct

open hardwarePreamble;

open ag32MachineTheory;

(* Memory behavior-selection functions *)

local
  val is_mem_def = ``is_mem fext_accessor_circuit step' fext``
  |> SIMP_CONV (srw_ss()) [fext_accessor_circuit_def, is_mem_def]
  |> GEN_ALL;
  fun rw_mem conjn n = el conjn o CONJUNCTS o Q.SPEC n o PURE_REWRITE_RULE [is_mem_def]
in
val is_mem_do_nothing = rw_mem 1
val is_mem_inst_read = rw_mem 2
val is_mem_data_read = rw_mem 3
val is_mem_data_write = rw_mem 4
val is_mem_data_flush = rw_mem 5
(* special: *)
val is_mem_def_mem_no_errors = el 6 o CONJUNCTS o SPEC_ALL o PURE_REWRITE_RULE [is_mem_def]
end

(* Can be optimized ... *)
val no_mem_error_tac = reverse IF_CASES_TAC
                       >- rfs [is_mem_def, mem_no_errors_def] \\
                       pop_assum kall_tac;

end
