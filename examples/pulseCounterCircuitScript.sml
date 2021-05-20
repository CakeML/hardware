open hardwarePreamble;

open newTranslatorTheory newTranslatorCoreLib;

val _ = new_theory "pulseCounterCircuit";

val _ = prefer_num ();

Datatype:
 state = <| count : word8; done : bool |>
End

Datatype:
 ext_state = <| pulse : bool |>
End

Definition pcounter_seq_def:
 pcounter_seq (fext:ext_state) (s:state) (s':state) =
  if fext.pulse then
   s' with count := s.count + 1w
  else
   s'
End

Definition pcounter_comb_def:
 pcounter_comb (fext:ext_state) (s:state) (s':state) =
  if s.count <+ 10w then
   s' with done := F
  else
   s' with done := T
End

val init_tm = add_x_inits “<| count := 0w |>”;

Definition pcounter_init_def:
 pcounter_init (fbits : num -> bool) = ^init_tm
End

Definition pcounter_def:
 pcounter = mk_module (procs [pcounter_seq]) (procs [pcounter_comb]) pcounter_init
End

Theorem pcounter_alt:
 pcounter = mk_module pcounter_seq pcounter_comb pcounter_init
Proof
 simp [pcounter_def, procs_sing]
QED

Definition pulse_spec_def:
 pulse_spec fext = !n. ?m. (fext (n + m)).pulse
End

Theorem pulse_later:
 !f t1 t2.
  (!t3. t3 < t2 ==> ~(f (t1 + t3)).pulse) \/
  (?t3. t3 < t2 /\ (!t4. t4 < t3 ==> ~(f (t1 + t4)).pulse) /\ (f (t1 + t3)).pulse)
Proof
 rpt gen_tac \\ Induct_on `t2` >- simp [] \\ pop_assum strip_assume_tac
 >- (Cases_on `(f (t1 + t2)).pulse`
  >- (disj2_tac \\ qexists_tac `t2` \\ simp [])
  \\ (disj1_tac \\ gen_tac \\ Cases_on `t3 = t2` \\ simp []))
 \\ disj2_tac \\ qexists_tac `t3` \\ simp []
QED

Theorem pulse_spec_alt:
 !fext. pulse_spec fext =
        !t1. ?t2. (!t3. t3 < t2 ==> ~(fext (t1 + t3)).pulse) /\ (fext (t1 + t2)).pulse
Proof
 metis_tac [pulse_spec_def, pulse_later]
QED

Theorem pcounter_comb_const:
 ∀fext s s'. (pcounter_comb fext s s').count = s'.count
Proof
 rw [pcounter_comb_def]
QED

Theorem pcounter_count_wait:
 !n m fext fbits.
 (∀t3. t3 < m ⇒ ¬(fext (n + t3)).pulse) ⇒
 (pcounter fext fbits (n + m)).count = (pcounter fext fbits n).count
Proof
 rpt strip_tac \\ Induct_on `m` \\ rpt strip_tac >- simp [] \\
 rewrite_tac [GSYM arithmeticTheory.ADD_SUC] \\
 fs [pcounter_alt, mk_module_def, mk_circuit_def, pcounter_comb_const, pcounter_seq_def] \\ rw [] \\
 first_x_assum (qspec_then ‘m’ mp_tac) \\ simp []
QED

Theorem pcounter_step_count_1:
 !n fext fbits.
  pulse_spec fext ⇒
  ?m. (pcounter fext fbits (n + m)).count = (pcounter fext fbits n).count + 1w
Proof
 rewrite_tac [pulse_spec_alt] \\ rpt strip_tac \\ pop_assum (qspec_then `n` strip_assume_tac) \\
 drule_strip pcounter_count_wait \\ qexists_tac `SUC t2` \\
 rewrite_tac [GSYM arithmeticTheory.ADD_SUC] \\
 fs [pcounter_alt, mk_module_def, mk_circuit_def, pcounter_comb_const, pcounter_seq_def]
QED

Theorem pcounter_step_count_n:
 !l n fext fbits.
  pulse_spec fext ⇒
  ?m. (pcounter fext fbits (n + m)).count = (pcounter fext fbits n).count + n2w l
Proof
 rpt strip_tac \\ Induct_on `l` >- (qexists_tac `0` \\ rw [pcounter_alt]) \\
 fs [] \\ drule_strip pcounter_step_count_1 \\
 first_x_assum (qspecl_then [`n + m`, ‘fbits’] strip_assume_tac) \\
 qexists_tac `m + m'` \\ fs [n2w_SUC]
QED

Theorem pcounter_correct:
 !fext fbits. pulse_spec fext ⇒ ?n. (pcounter fext fbits n).done
Proof
 rpt strip_tac \\
 drule_strip pcounter_step_count_n \\
 first_x_assum (qspecl_then [`11`, `0`, ‘fbits’] strip_assume_tac) \\
 qexists_tac ‘m’ \\ Cases_on ‘m’
 >- (fs [pcounter_alt, mk_module_def, mk_circuit_def, pcounter_comb_def, pcounter_init_def]) \\
 fs [pcounter_alt, mk_module_def, mk_circuit_def, pcounter_comb_const, pcounter_init_def] \\
 simp [pcounter_comb_def]
QED

(*
Maybe recover this at some point:

val _ = Datatype `R_state = <| a : word8; b : word8; c : word8 |>`;

val R_def = Define `
 R s = (let s' = s with <| a := 1w; b := 2w |> in
        let s'' = s' with a := s'.a + 1w in
        let tmp = 1w in
        case s''.c of 0w => s'' with c := tmp | _ => s'' with c := 0w)`;
*)

val _ = export_theory ();
