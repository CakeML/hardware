open hardwarePreamble;

open sumExtraTheory RTLTheory RTLPropsTheory;
 
open verilogTypeCheckerTheory PreCompilerTheory RTLCompilerTheory RTLDeterminizerTheory RTLUnusedRegsTheory RTLBlasterTheory;
open PreCompilerProofTheory RTLCompilerProofTheory RTLDeterminizerProofTheory RTLBlasterProofTheory;

val _ = new_theory "fullCompiler";

(** Run everything except technology mapping **)

Definition compile_def:
 compile keep m = do
  m <- typecheck m;
  m <- preprocess m;
  (circuit, tmpnum) <- RTLCompiler$compile m;
  circuit <- rtl_determinizer circuit;
  let circuit = rtl_rem_unused_regs keep circuit; in do
   (circuit, blast_s) <- blast_circuit circuit tmpnum;
   return circuit
  od
 od
End

Definition verilog_netlist_rel_def:
 verilog_netlist_rel keep venv cenv <=>
  !var.
   MEM var keep ==>
   case sum_alookup venv var of
     INL e => T
   | INR (VBool b) => cget_var cenv (RegVar var 0) = INR (CBool b)
   | INR (VArray bs) => !i. i < LENGTH bs ==> cget_var cenv (RegVar var i) = INR (CBool (EL i bs))
End

(* TODO: Move *)
Theorem rtl_determinizer_const:
 ∀extenv decls ps circuit.
 rtl_determinizer (Circuit extenv decls ps) = INR circuit ⇒ circuit_extenv circuit = extenv
Proof
 rw [rtl_determinizer_def, sum_map_INR] \\ pairarg_tac \\ fs [circuit_extenv_def]
QED

Theorem compile_correct:
 !fextenv decls ps circuit fbits vfext rtlfext keep n.
 let m = Module fextenv decls ps in

 compile keep m = INR circuit ∧
 writes_ok ps ∧

 vertype_fext fextenv vfext ∧
 same_fext vfext rtlfext ⇒
 blasted_circuit circuit ∧
 ?cenv'. circuit_run rtlfext fbits circuit n = INR cenv' /\
         ?vfbits. 
          case run vfext vfbits m n of
            INL e => T
          | INR (venv', vfbits') => verilog_netlist_rel keep venv' cenv'
Proof
 simp [compile_def, sum_bind_INR] \\ rpt strip_tac' \\ rpt (pairarg_tac \\ fs [sum_bind_INR]) \\ rveq \\

 Cases_on ‘m’ \\
 drule_strip typecheck_sound \\
 drule_strip typecheck_writes \\

 Cases_on ‘m'’ \\
 drule_strip preprocess_correct \\

 drule_strip rtl_compile_correct \\
 first_assum (qspecl_then [‘n’, ‘fbits’] strip_assume_tac) \\

 drule_strip rtl_determinizer_correct \\
 drule_strip deterministic_circuit_rtl_determinizer \\

 drule_strip rtl_rem_unused_regs_correct \\ first_x_assum (qspec_then ‘keep’ strip_assume_tac) \\
 drule_strip blast_circuit_correct \\

 (* test: *)
 impl_tac >- (rpt conj_tac
 >- (fs [circuit_extenv_rtl_rem_unused_regs, RTLCompilerTheory.compile_def, sum_bind_INR] \\ pairarg_tac \\ fs [] \\ rveq \\
     drule_strip rtl_determinizer_const \\ drule_strip rtltype_extenv_compile_fextenv \\ fs [])
 \\ simp [rtl_rem_unused_regs_preserves]) \\ strip_tac \\ simp [] \\

 first_x_assum (qspecl_then [‘n’, ‘fbits''’] strip_assume_tac) \\ simp [] \\
 
 qexists_tac ‘fbits'''’ \\ rpt TOP_CASE_TAC \\ fs [] \\ rfs [] \\ rveq \\ drule_first \\ fs [] \\

 rfs [det_rel_reg_def] \\
 rw [verilog_netlist_rel_def] \\ drule_first \\ TOP_CASE_TAC \\ drule_first \\
 fs [same_state_def] \\ drule_first \\
 fs [blast_reg_rel_def] \\ first_x_assum (qspec_then ‘var’ mp_tac) \\ simp [] \\
 rpt TOP_CASE_TAC \\ fs [same_value_def]
QED

val _ = export_theory ();
