open hardwarePreamble;

val _ = new_theory "oracle";

val shift_seq_def = Define `
 shift_seq (k:num) s = \i. s (i + k)`;

val oracle_bit_def = Define `
 oracle_bit oracle = (oracle 0n, shift_seq 1 oracle)`

val oracle_bits_def = Define `
 (oracle_bits oracle 0 = ([], oracle)) /\
 (oracle_bits oracle (SUC n) = let (b, oracle') = oracle_bit oracle; (bs, oracle'') = oracle_bits oracle' n in (b :: bs, oracle''))`;

val init_seq_eq_def = Define `
 init_seq_eq f f' (n:num) <=> !n'. n' < n ==> f' n' = f n'`;

(* Should be called add prefix? *)
val replace_prefix_def = Define `
 replace_prefix f fprefix n (t:num) = if t < n then fprefix t else f (t - n)`;

(** Some simple properties **)

Theorem shift_seq_0:
 !f. shift_seq 0 f = f
Proof
 simp_tac (srw_ss() ++ boolSimps.ETA_ss) [shift_seq_def]
QED

Theorem shift_seq_1:
 !f. shift_seq 1 f = f o SUC
Proof
 simp [shift_seq_def, FUN_EQ_THM, arithmeticTheory.ADD1]
QED

Theorem shift_seq_add:
 !n m f. shift_seq (n + m) f = shift_seq m (shift_seq n f)
Proof
 Induct \\ rw [shift_seq_def]
QED

Theorem shift_seq_K:
 !n x. shift_seq n (K x) = K x
Proof
 rw [shift_seq_def, FUN_EQ_THM]
QED

Theorem shift_seq_if_lt:
 !n f g. shift_seq n (\t. if t < n then f t else g (t − n)) = g
Proof
 rw [shift_seq_def] \\ simp_tac (srw_ss() ++ boolSimps.ETA_ss) []
QED

Theorem shift_seq_replace_prefix:
 !f fprefix n. shift_seq n (replace_prefix f fprefix n) = f
Proof
 rw [shift_seq_def, replace_prefix_def] \\ simp_tac (bool_ss ++ boolSimps.ETA_ss) []
QED

Theorem init_seq_eq_sym:
 ∀f g n. init_seq_eq f g n ⇔ init_seq_eq g f n
Proof
 rw [init_seq_eq_def] \\ eq_tac \\ rw []
QED

Theorem init_seq_eq_shift_seq:
 !n m f g. init_seq_eq f g (n + m) ==> init_seq_eq (shift_seq n f) (shift_seq n g) m
Proof
 rw [shift_seq_def, init_seq_eq_def]
QED

Theorem init_seq_eq_shift_seq_suc:
 !n f g. init_seq_eq f g (SUC n) ==> init_seq_eq (shift_seq 1 f) (shift_seq 1 g) n
Proof
 rpt strip_tac \\ match_mp_tac init_seq_eq_shift_seq \\ fs [arithmeticTheory.ADD1]
QED

Theorem init_seq_eq_replace_prefix:
 !f g n. init_seq_eq g (replace_prefix f g n) n
Proof
 rw [init_seq_eq_def, replace_prefix_def]
QED

Theorem init_seq_eq_shorten:
 !m n f g. init_seq_eq f g n /\ m <= n ==> init_seq_eq f g m
Proof
 rw [init_seq_eq_def]
QED

Theorem oracle_bit_cong:
 !f f' g g' b b'.
 init_seq_eq f g 1 /\ oracle_bit f = (b, f') /\ oracle_bit g = (b', g') ==>
 b' = b
Proof
 rw [init_seq_eq_def, oracle_bit_def] \\ simp []
QED

Theorem oracle_bits_cong:
 !n f f' g g' bs bs'.
 init_seq_eq f g n /\ oracle_bits f n = (bs, f') /\ oracle_bits g n = (bs', g') ==>
 bs' = bs
Proof
 Induct \\ rw [oracle_bits_def] \\ rpt (pairarg_tac \\ fs []) \\ rveq \\
 qspec_then ‘1’ mp_tac init_seq_eq_shorten \\ disch_then drule_strip \\ impl_tac >- simp [] \\ strip_tac \\
 drule_strip oracle_bit_cong \\
 fs [oracle_bit_def] \\ rveq \\ drule_strip init_seq_eq_shift_seq_suc \\ drule_first
QED

Theorem oracle_bits_correct:
 !n bs oracle oracle'.
 oracle_bits oracle n = (bs, oracle') ==> oracle' = shift_seq n oracle /\ LENGTH bs = n
Proof
 Induct \\ simp [oracle_bits_def, shift_seq_def, ETA_THM] \\
 rpt strip_tac' \\ rpt (pairarg_tac \\ fs []) \\ rveq \\
 drule_first \\ fs [oracle_bit_def, shift_seq_def] \\ rw [arithmeticTheory.ADD1]
QED

Theorem oracle_bits_genlist:
 !n oracle. oracle_bits oracle n = (GENLIST oracle n, shift_seq n oracle)
Proof
 Induct \\ simp [oracle_bits_def, shift_seq_0] \\ rw [oracle_bit_def]
 >- simp [GENLIST_CONS, shift_seq_1]
 \\ simp [GSYM shift_seq_add, arithmeticTheory.ADD1]
QED

Theorem init_seq_eq_genlist:
 ∀f g n m. init_seq_eq f g n ∧ m ≤ n ⇒ GENLIST f m = GENLIST g m
Proof
 rw [init_seq_eq_def, GENLIST_FUN_EQ]
QED

val _ = export_theory ();

