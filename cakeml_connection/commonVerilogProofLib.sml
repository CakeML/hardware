structure commonVerilogProofLib =
struct

open hardwarePreamble;

open verilogTypeTheory moduleTranslatorTheory;
open ag32MachineTheory ag32EqTheory ag32HaltTheory ag32VerilogTheory;

open commonVerilogProofTheory;

fun lift_tac ag32_next_thm config_def =
 rewrite_tac [verilog_sem_def] \\ rpt gen_tac \\
 SELECT_ELIM_TAC \\ conj_asm1_tac >- metis_tac[lift_fext_exists] \\

 rw [ag32_verilog_init_def] \\
 `mrun x computer ms = mrun x' computer ms` by metis_tac [lift_fext_unique] \\
 last_x_assum kall_tac \\ fs [] \\ pop_assum kall_tac \\
 drule_strip (vars_has_type_append |> SPEC_ALL |> EQ_IMP_RULE |> fst |> SPEC_ALL) \\

 drule_strip relM_backwards \\
 drule_strip INIT_backwards \\
 qmatch_asmsub_abbrev_tac `INIT _ _ s'` \\

 drule_strip (ag32_next_thm |> GEN_ALL) \\

 disch_then (qspec_then `s'` mp_tac) \\
 impl_tac >- (qunabbrev_tac `s'` \\ simp [ag32_targetTheory.is_ag32_init_state_def]) \\

 strip_tac \\
 first_x_assum(qspec_then`k1`mp_tac) \\
 impl_tac >- simp[] \\ strip_tac \\

 drule_strip (SIMP_RULE (srw_ss()) [] INIT_REL_circuit_verilog) \\
 pop_assum(qspec_then`k1`strip_assume_tac) \\
 qexists_tac `m` \\ rpt strip_tac' \\

 fs [is_lab_env_def] \\
 drule_strip is_mem_verilog \\
 drule_strip is_interrupt_interface_verilog \\
 drule_strip (SIMP_RULE (srw_ss()) [] circuit_halt_compute_step_full_actual') \\
 fs [arithmeticTheory.LESS_EQ_EXISTS] \\ 
 qmatch_assum_rename_tac `k = m + m1` \\ rveq \\
 disch_then (qspecl_then [`m`, `m1`] mp_tac) \\ impl_tac
 >- (rpt conj_tac
    >- (fs [REL_def] \\
       CONV_TAC (RAND_CONV (REWRITE_CONV [config_def] THENC EVAL)) \\
       EVAL_TAC)
    >- rfs [REL_def, get_mem_word_word_at_addr]
    \\ fs [halt_inv_def, REL_def]) \\
 strip_tac \\

 drule_strip computer_Next_relM_run \\ pop_assum (qspec_then `m1 + m` strip_assume_tac) \\
 fs [REL_def, is_halted_def, ag32_machine_configTheory.ag32_machine_config_def];

fun lift_stdout_tac spec_thm =
 rpt conj_tac

 >- fs [relM_def, relM_var_def, WORD_def]
 
 >- metis_tac [spec_thm, is_prefix_extract_writes]

 \\ strip_tac \\ rfs [] \\ drule_strip after_R_1w_lift \\ drule_first \\
 fs [spec_thm];

end
