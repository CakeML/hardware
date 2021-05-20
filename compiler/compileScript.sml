open hardwarePreamble;

open sumExtraTheory RTLTheory RTLPropsTheory;
 
open fullCompilerTheory LECTheory;

val _ = new_theory "compile";

(** Big ugly glue thm **)

Theorem compile_glue_thm:
 ∀m circuit tech_circuit fbits vfext rtlfext n.
 (* Compiler thm *)
 (∀fbits vfext rtlfext n.
   vertype_fext m.fextty vfext ∧
   same_fext vfext rtlfext ⇒
   blasted_circuit circuit ∧
   rtltype_extenv (circuit_extenv circuit) rtlfext ∧
   (∀var i. MEM var (FLAT (MAP vwrites m.combs)) ⇒ ~MEM (var, i) (MAP FST (circuit_regs circuit))) ∧
   ∃cenv' fbits'.
   circuit_run_no_pseudos rtlfext fbits circuit n = INR (cenv',fbits') ∧
   ∃vfbits.
   case sort_run vfext vfbits m n of
     INL e => T
   | INR (venv',vfbits') => verilog_netlist_rel m venv' cenv')
 ⇒
 (* Tech map+LEC thm *)
 (∀n fext fbits.
   blast_regs_distinct (circuit_regs circuit) ∧
   deterministic_netlist (circuit_nl_combs circuit) ∧
   (∀s n. populated_by_regs_only (circuit_regs circuit) s ⇒
          ISR (sum_foldM (cell_run (fext n)) s (circuit_nl_combs circuit))) ∧
   rtltype_extenv (circuit_extenv circuit) fext ⇒
   circuit_run_no_pseudos fext fbits tech_circuit n =
   circuit_run_no_pseudos fext fbits circuit n)
 ⇒
 vertype_fext m.fextty vfext ∧
 same_fext vfext rtlfext ⇒
 ∃cenv' fbits'.
  circuit_run_no_pseudos rtlfext fbits tech_circuit n = INR (cenv',fbits') ∧
  ∃vfbits. case sort_run vfext vfbits m n of
             INL e => T
           | INR (venv',vfbits') => verilog_netlist_rel m venv' cenv'
Proof
 rpt strip_tac \\
 drule_first \\
 pop_assum (strip_assume_tac o
            Ho_Rewrite.REWRITE_RULE [GSYM PULL_FORALL, RTLBlasterProofTheory.blasted_circuit_alt]) \\

 qspecl_then [‘rtlfext’, ‘fbits’,
              ‘circuit_extenv circuit’, ‘circuit_outs circuit’, ‘circuit_regs circuit’,
              ‘circuit_nl_combs circuit’, ‘[]’]
             mp_tac populated_by_regs_only_ISR_from_circuit_run \\
 impl_tac >- (rw [ISR_exists] \\ metis_tac [Circuit_components]) \\ strip_tac \\

 first_x_assum (qspecl_then [‘fbits’, ‘n’] strip_assume_tac) \\ simp [] \\ asm_exists_tac
QED

val _ = export_theory ();
