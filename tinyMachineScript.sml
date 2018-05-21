open preamble;

open tinyImplTheory;

(*
The tiny machine theory depends on tinyImpl theory and provides

 - a model of memory and,
 - a model of the interconnect between different components.
*)

val _ = new_theory "tinyMachine";

(* Step whole machine *)
val computer_Next_def = Define `
  computer_Next acc_Next s = let mem_s = mem_Next s in
                             let acc_s = acc_Next s in
                             let s' = Next s in
                             (* Most outputs are from the processor, so it's easiest to start from that state *)
                             s' with <| (* mem *)
                                        mem_inst_out := mem_s.mem_inst_out;
                                        mem_data_out := mem_s.mem_data_out;
                                        mem_fun := mem_s.mem_fun;

                                        (* acc *)
                                        acc_state := acc_s.acc_state;
                                        acc_res := acc_s.acc_res;
                                        acc_res_ready := acc_s.acc_res_ready
                                      |>`;

val _ = export_theory ();
