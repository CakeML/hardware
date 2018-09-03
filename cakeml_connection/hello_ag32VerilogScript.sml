open hardwarePreamble;

open hello_ag32ProofTheory;

open verilogTheory verilogTypeTheory verilogTranslatorTheory moduleTranslatorTheory;
open ag32MachineTheory ag32EqTheory ag32VerilogTheory;

open verilogTranslatorLib;

val _ = new_theory "hello_ag32Verilog";

val _ = guess_lengths ();
val _ = prefer_num ();

val exit_code_0_def = Define `
 exit_code_0 vs fextv <=>
  erun fextv <| vars := vs |> (ArrayIndex (Var "R") [Const (w2ver (1w:word6))]) = INR (w2ver (0w:word32))`;

(* Defined based on hello world program config *)
val halt_addr_def = Define `
 halt_addr mem_start = mem_start + n2w (heap_size + 4 * LENGTH data + 2 * ffi_offset)`;

val init_R_lift = Q.store_thm("init_R_lift",
 `!init hol_s s fext i.
   INIT_verilog init /\ relM hol_s init /\ INIT fext hol_s s /\ i <> 0w ==> s.R i = 0w`,
 rw [INIT_verilog_def, relM_def, relM_var_def, INIT_def, INIT_R_def] \\

 drule_first \\ pop_assum (fn th => rewrite_tac [GSYM th]) \\

 qmatch_asmsub_rename_tac `mget_var init "R" = INR r` \\
 fs [WORD_ARRAY_def, mget_var_ALOOKUP] \\
 Cases_on `r` \\ fs [w2ver_bij]);

val after_R_lift = Q.store_thm("after_R_lift",
 `!env (hol_s:state_circuit) (s:ag32_state) fext fextv n.
   relM_fextv fextv fext /\ relM hol_s env /\ hol_s.R = s.R /\ exit_code_0 env (fextv n) ==>
   s.R 1w = 0w`,
 rw [exit_code_0_def] \\
 assume_tac (hol2hardware_exp ``s:state_circuit`` ``(s:state_circuit).R 1w`` |> GEN_ALL) \\
 fs [Eval_def] \\

 drule_strip relM_relS \\
 fs [relM_fextv_fext_relS_fextv_fext] \\
 last_x_assum (qspec_then `n` assume_tac) \\
 first_x_assum (qspecl_then [`hol_s`, `fext n`, `env`, `fextv n`, `<| vars := env |>`] mp_tac) \\

 impl_tac >- (fs [relS_def, relS_var_def, get_var_def] \\ metis_tac []) \\
 strip_tac \\ fs [WORD_def] \\ rveq \\ fs [w2ver_bij] \\ metis_tac []);

val hello_verilog = Q.store_thm("hello_verilog",
 `!vstep fext fextv init mem_start.
   vstep = mrun fextv computer init ∧
   relM_fextv fextv fext ∧
   is_mem fext_accessor_verilog vstep fext ∧
   is_interrupt_interface fext_accessor_verilog vstep fext ∧
   is_mem_start_interface fext mem_start ∧
   mem_no_errors fext ∧
   vars_has_type init (relMtypes ⧺ ag32types) ∧
   INIT_verilog init ∧
   INIT_fext (fext 0) ∧

   byte_aligned mem_start ∧
   w2n mem_start + memory_size < dimword (:32) ∧

   (fext 0).mem = hello_init_memory mem_start
   ==>
   ?k vs'.
    vstep k = INR vs' /\
    let
     outs = MAP (\mem. get_print_string (mem_start, print_string_max_length, mem)) (fext k).io_events
    in
     (mget_var vs' "PC") = INR (w2ver (halt_addr mem_start)) ∧
     outs ≼ hello_outputs ∧
     (exit_code_0 vs' (fextv k) ==> outs = hello_outputs)`,
 rpt strip_tac \\
 drule_strip (vars_has_type_append |> SPEC_ALL |> EQ_IMP_RULE |> fst |> SPEC_ALL) \\

 drule_strip relM_backwards \\
 drule_strip INIT_backwards \\
 pop_assum (qspec_then `mem_start` strip_assume_tac) \\

 drule_strip (GEN_ALL hello_ag32_next) \\
 qmatch_asmsub_abbrev_tac `INIT _ _ s'` \\
 disch_then (qspec_then `s'` mp_tac) \\ qunabbrev_tac `s'` \\
 impl_tac >-
 (rw [ag32_targetTheory.is_ag32_init_state_def, ag32Theory.print_string_max_length_def]
  >- rfs [INIT_def]
  \\ match_mp_tac EQ_EXT \\
     rw [ag32_targetTheory.ag32_init_regs_def, combinTheory.UPDATE_APPLY] \\
     drule_strip init_R_lift \\ fs [] \\ metis_tac [combinTheory.UPDATE_APPLY]) \\

 strip_tac \\

 drule_strip (SIMP_RULE (srw_ss()) [] INIT_REL_circuit_verilog) \\

 qmatch_asmsub_abbrev_tac `FUNPOW _ _ s'` \\
 disch_then (qspecl_then [`k`, `s'`, `hol_s`] mp_tac) \\
 impl_tac >- (qunabbrev_tac `s'` \\ simp [combinTheory.UPDATE_APPLY]) \\ strip_tac \\

 asm_exists_tac \\ fs [REL_def, hello_machine_config_def] \\ conj_tac

 >- fs [relM_def, relM_var_def, WORD_def, halt_addr_def]

 \\ fs [extract_print_from_mem_get_print_string] \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\
    simp [] \\ strip_tac \\ drule_strip after_R_lift \\
    drule_first);

val _ = export_theory ();
