open hardwarePreamble;

open alistTheory wordsTheory stringTheory bitstringTheory sptreeTheory balanced_mapTheory;
open wordsLib;

open oracleTheory sumExtraTheory;

val _ = new_theory "verilog";

(*******************************
  Verilog syntax
 *******************************)

(** Verilog values **)
Datatype:
 value = VBool bool
       | VArray (value list)
End

Datatype:
 vertype = VBool_t 
         | VArray_t num
         (* could have more general array type and merge VArray_t and VArray2_t,
            but this is fine for now:

                     /---------- width
                     v   v------ depth *)
         | VArray2_t num num
End

val value_size_def = definition "value_size_def";

Theorem MEM_IMP_value_size:
 !xs x. MEM x xs ==> value_size x < value1_size xs
Proof
 Induct \\ rw [value_size_def] \\ res_tac \\ DECIDE_TAC
QED

val _ = type_abbrev("envT", ``:(string, value) alist``);

(*Definition show_vertype_def:
 (show_vertype VBool_t = "logic") ∧
 (show_vertype (VArray_t l) = "logic[" ++ toString l ++ ":0]") ∧
End*)

val isVBool_def = Define `
 (isVBool (VBool _) = T) /\
 (isVBool (VArray _) = F)`;

(* Verilog to bool (VBool) *)
val ver2bool_def = Define `
  (ver2bool (VBool b) = INR b) /\
  (ver2bool (VArray _) = INL TypeError)`;

Theorem ver2bool_INR:
 ∀v b. ver2bool v = INR b ⇔ v = VBool b
Proof
 Cases \\ rw [ver2bool_def]
QED

(* Verilog to bitstring (1-dim VArray) *)
val ver2v_def = Define `
  (ver2v (VBool _) = INL TypeError) /\
  (ver2v (VArray vs) = sum_mapM ver2bool vs)`;

Theorem ver2v_INR:
 !v bs. ver2v v = INR bs <=> v = VArray (MAP VBool bs)
Proof
 Cases \\ rw [ver2v_def, sum_mapM_EL, ver2bool_INR] \\ eq_tac \\ strip_tac
 >- (match_mp_tac LIST_EQ \\ rw [EL_MAP])
 >- rw [EL_MAP]
QED

val ver2n_def = Define `
  ver2n v = sum_map v2n (ver2v v)`;

val v2ver_def = Define `
  v2ver bs = VArray (MAP VBool bs)`;

val n2ver_def = Define `
  n2ver n = v2ver (n2v n)`;

val w2ver_def = Define `
  w2ver w = v2ver (w2v w)`;

val ver2w_def = Define `
 ver2w v = sum_map v2w (ver2v v)`;

(* Metatheory for mapping from and to Verilog values *)

Theorem ver2n_lt:
 !bs n. ver2n (VArray bs) = INR n ==> n < 2 ** LENGTH bs
Proof
 rw [ver2n_def, sum_map_INR, ver2v_def, sum_mapM_EL] \\ metis_tac [bitstringTheory.v2n_lt]
QED

(*Theorem ver2n_VArray:
 !bs. ver2n (VArray bs) = INR (v2n bs)
Proof
 simp [ver2n_def, ver2v_def, sum_map_def]
QED*)

Theorem ver2n_INR:
 ∀v n. ver2n v = INR n ⇔ ∃bs. v = VArray (MAP VBool bs) ∧ v2n bs = n
Proof
 simp [ver2n_def, sum_map_INR, ver2v_INR]
QED

val sum_mapM_ver2bool_VBool = Q.store_thm("sum_mapM_ver2bool_VBool",
 `!l. sum_mapM ver2bool (MAP VBool l) = INR l`,
 Induct \\ rw [sum_mapM_def, ver2bool_def, sum_map_def]);

Theorem sum_mapM_ver2bool_INR:
 ∀vs bs. sum_mapM ver2bool vs = INR bs ⇔ vs = MAP VBool bs
Proof
 rpt strip_tac \\ eq_tac \\ rw [sum_mapM_ver2bool_VBool] \\
 fs [sum_mapM_EL, ver2bool_INR] \\
 match_mp_tac LIST_EQ \\ rw [EL_MAP]
QED

val ver2v_w2ver = Q.store_thm("ver2v_w2ver",
 `!w. ver2v (w2ver w) = INR (w2v w)`,
 rw [ver2v_def, w2ver_def, v2ver_def, sum_mapM_ver2bool_VBool]);

val v2ver_w2v = Q.store_thm("v2ver_w2v",
 `!w. v2ver (w2v w) = w2ver w`,
 rw [v2ver_def, w2ver_def]);

val w2v_n2w = Q.store_thm("w2v_n2w",
 `!n. w2v ((n2w n):'a word) = fixwidth (dimindex (:'a)) (n2v n)`,
 rewrite_tac [GSYM v2w_n2v, w2v_v2w]);

val w2v_w2w = Q.store_thm("w2v_w2w",
 `!(w:'a word).
   w2v ((w2w w):'b word) = fixwidth (dimindex (:'b)) (w2v w)`,
 rw [w2w_def] \\ bitstringLib.Cases_on_v2w `w` \\
 rw [w2n_v2w, n2w_v2n, w2v_v2w, v2n_lt,
     bitTheory.MOD_2EXP_def, arithmeticTheory.LESS_MOD]);

val ver2w_w2ver = Q.store_thm("ver2w_w2ver",
 `!v. ver2w (w2ver v) = INR v`,
 simp [ver2w_def, w2ver_def, v2ver_def, ver2v_def, sum_mapM_ver2bool_VBool, sum_map_def]);

(*
val GENLIST_K_APPEND = Q.store_thm("GENLIST_K_APPEND",
 `!a b c. GENLIST (K c) (a + b) = GENLIST (K c) b ⧺ GENLIST (K c) a`,
 rw [GENLIST_APPEND, combinTheory.K_DEF]);

val GENLIST_K_F_APPEND_F = Q.store_thm("GENLIST_K_F_APPEND_F",
 `GENLIST (K F) (dimindex (:'a) − 1) ⧺ [F] = GENLIST (K F) (dimindex (:'a))`,
 `[F] = GENLIST (K F) 1` by rw [] \\ pop_assum (fn th => PURE_REWRITE_TAC [th]) \\
 rw [GSYM GENLIST_K_APPEND, DIMINDEX_GT_0]);
*)

val ver2v_n2ver = Q.store_thm("ver2v_n2ver",
 `!n. ver2v (n2ver n) = INR (n2v n)`,
 rw [n2ver_def, ver2v_def, v2ver_def, ver2v_def, sum_mapM_ver2bool_VBool]);

val ver2n_n2ver = Q.store_thm("ver2n_n2ver",
 `!n. ver2n (n2ver n) = INR n`,
 rw [ver2n_def, ver2v_n2ver, sum_map_def]);

val ver2n_w2ver = Q.store_thm("ver2n_w2ver",
 `!w. ver2n (w2ver w) = INR (w2n w)`,
 rw [ver2n_def, w2ver_def, ver2v_def, v2ver_def, sum_mapM_ver2bool_VBool, sum_map_def, v2n_w2v]);

val w2v_inj = Q.store_thm("w2v_bij",
 `!x y. w2v x = w2v y <=> x = y`,
 metis_tac [v2w_w2v]);

val w2ver_bij = Q.store_thm("w2ver_bij",
 `!x y. w2ver x = w2ver y <=> x = y`,
 rpt strip_tac \\ eq_tac \\ rw [w2ver_def, v2ver_def, MAP_inj, w2v_inj]);

Definition verlength_def:
 (verlength (VBool _) = 1) ∧
 (verlength (VArray bs) = SUM (MAP verlength bs))
Termination
 WF_REL_TAC `measure value_size` \\ rw [] \\
 drule_strip MEM_IMP_value_size \\ decide_tac
End

Definition build_zero_def:
 (build_zero VBool_t = VBool F) /\
 (build_zero (VArray_t l) = VArray $ REPLICATE l (VBool F)) ∧
 (build_zero (VArray2_t w d) = VArray $ REPLICATE d (VArray $ REPLICATE w (VBool F)))
End

(* Verilog ASTs *)

(* Boolean unary operators *)
val _ = Datatype `
  buop = Not`;

(* Boolean binary operators *)
val _ = Datatype `
  bbop = And
       | Or
       | Equal`;

(* Array binary operators *)
val _ = Datatype `
  abop = BitwiseAnd
       | BitwiseOr
       | BitwiseXor`;

(* RotateR <-- note that there's no such primitive in Verilog *)
val _ = Datatype `
  shift = ShiftArithR
        | ShiftLogicalL
        | ShiftLogicalR`;

(* Array arithmetic operators *)
val _ = Datatype `
  arith = Minus
        | Plus
        | Times
        | Mod`;

(* Array comparisons *)
val _ = Datatype `
  cmp = (* The following two operations are not Verilog operations, as there whether something is
         less than or lower than depends on if the value is signed or not, a notion we don't have
         here. So when this is printed, sign casts will be inserted into the code... *)
        LessThan (* signed, in wordsTheory: < *)
      | LowerThan (* unsigned, in wordsTheory: <+ *)
      | LessThanOrEqual
      | LowerThanOrEqual
      | ArrayEqual`;

val _ = Datatype `
  resize = ZeroExtend
         | SignExtend`;

(** Expressions

    Note that in this semantics expressions cannot change state, e.g. no function calls or assignments are included. This is because we want a deterministic semantics (per process):

    > The ordering of assignment operations relative to any other operation within an expression is undefined. An implementation can warn whenever a variable is both written and read-or-written within an integral expression or in other contexts where an implementation cannot guarantee order of evaluation. -- 11.4.2 "Increment and decrement operators" **)

val _ = Datatype `
  exp = Const value
      | Var string
      | InputVar string

      (* Single indexing: variable (e.g. Var "foo") -> index length (number of bits) -> index expression *)
      | ArrayIndex exp num exp

      (* Indexing with upper and lower bound, assume that the bounds are constants.

         From "7.4.6 Indexing and slicing of arrays":

         > Slices of an array can only apply to one dimension, but other dimensions
         > can have single index values in an expression.

         So the assumption make sense, but we only allow a strict subset of full Verilog.

         Variable expression (e.g. Var "foo") -> indices expressions -> indices for subarray of last array *)
      | ArraySlice exp (*exp list*) num num

      (* This can be generalized to (exp list), but exp exp is enough for now *)
      | ArrayConcat exp exp

      | InlineIf exp exp exp

        (* For booleans, reduces to boolean *)
      | BUOp buop exp
      | BBOp exp bbop exp
        (* For arrays, reduces to array of same length *)
      | ABOp exp abop exp
      | Shift exp shift exp
      | Arith exp arith exp
        (* For arrays, reduces to boolean *)
      | Cmp exp cmp exp

      | Resize exp resize num`;

val exp_size_def = definition "exp_size_def";

val is_const_def = Define ‘
 (is_const (Const _) = T) /\
 (is_const _ = F)’;

val get_const_def = Define ‘
 (get_const (Const v) = INR v) /\
 (get_const _ = INL TypeError)’;

Theorem get_const_INR:
 !e v. get_const e = INR v <=> e = Const v
Proof
 Cases \\ simp [get_const_def]
QED
 
(*val MEM_IMP_exp_size = Q.store_thm("MEM_IMP_exp_size",
  `!xs x. MEM x xs ==> exp_size x < exp1_size xs`,
  Induct \\ rw [exp_size_def] \\ res_tac \\ DECIDE_TAC);*)

val _ = Datatype ‘
 write_spec = NoIndexing string
            | Indexing string num exp (* var -> index length (number of bits) -> index exp *)
            | SliceIndexing string num num’;

(** Process code, should maybe be renamed to "stmt" or similar **)
val _ = Datatype `
  vprog = Skip
(*      | Return exp <-- TODO: Not relevant currently, only needed if we would support function calls *)
        | Seq vprog vprog
          (* lhs var, compare operator, rhs var, true branch, false branch *)
        | IfElse exp vprog vprog
          (* type annotation (type of match subject),
             match subject, cases (first in list = first in program order), optional default case *)
        | Case vertype exp ((exp # vprog) list) (vprog option)
          (* rhs is some = assign rhs, rhs is none = assign non-deterministic value *)
        | BlockingAssign write_spec (exp option)
        | NonBlockingAssign write_spec (exp option)`;

val vprog_size_def = definition "vprog_size_def";

val MEM_IMP_vprog_size = Q.store_thm("MEM_IMP_vprog_size",
  `!cs cc cb. MEM (cc, cb) cs ==> vprog_size cb < vprog1_size cs`,
  Induct \\ rw [vprog_size_def] \\ rw [vprog_size_def] \\ res_tac \\ DECIDE_TAC);

Definition verFromList_def:
 (verFromList [] = Skip) ∧
 (verFromList (p::ps) = Seq p (verFromList ps))
End

Datatype:
 var_metadata =
 <| output : bool (* might want to generalize this later to handle input/output/internal *)
  ; type : vertype
  ; init : value option |>
End

(* todo: should handle init as well... *)
Datatype:
 mem = Memory (* might be possible to get away with just the below? *)
     | ByteMemory (* 4-bit enable; x-bit addr; 32-bit data read port; 32-bit data write port *)
End

(* can be dropped probably: *)
val _ = type_abbrev("declty", “:(string, var_metadata) alist”);

Datatype:
 module =
  <| fextty : (string, vertype) alist
   ; decls : declty
   ; ffs : vprog list
   ; combs : vprog list
   (*; mem : mem list*) |>
End

(*******************************
  Process semantics
 *******************************)

(* State *)
val _ = Datatype `
  pstate =
    <| vars : envT              (* global vars *)
  (* ; lvars : envT             (* local vars, not needed for now *) *)
     ; nbq : envT               (* non-blocking assignment queue *)
     ; fbits : num -> bool |>`; (* non-deterministic stream of bits *)

(* Variable handling *)
val get_var_def = Define `
  get_var s name = case ALOOKUP s.vars name of
                       SOME v => INR v
                     | NONE => INL UnknownVariable`;

val set_var_def = Define `
  set_var s name v = s with vars := (name, v) :: s.vars`;

val get_nbq_var_def = Define `
  get_nbq_var s name = case ALOOKUP s.nbq name of
                           SOME v => INR v
                         | NONE => INL UnknownVariable`;

val set_nbq_var_def = Define `
  set_nbq_var s name v = s with nbq := (name, v) :: s.nbq`;

Theorem get_var_ALOOKUP:
 !s name v. get_var s name = INR v <=> ALOOKUP s.vars name = SOME v
Proof
 rw [get_var_def] \\ TOP_CASE_TAC
QED

Theorem get_var_get_var_ALOOKUP_ALOOKUP:
 ∀var s s'. get_var s' var = get_var s var ⇔ ALOOKUP s'.vars var = ALOOKUP s.vars var
Proof
 rw [get_var_def] \\ every_case_tac
QED

Theorem get_var_sum_alookup:
 !s name. get_var s name = sum_alookup s.vars name
Proof
 rw [get_var_def] \\ TOP_CASE_TAC \\ metis_tac [sum_alookup_INR, sum_alookup_INL]
QED

Theorem get_nbq_var_ALOOKUP:
 !s name v. get_nbq_var s name = INR v <=> ALOOKUP s.nbq name = SOME v
Proof
 rw [get_nbq_var_def] \\ TOP_CASE_TAC
QED

Theorem get_nbq_var_get_nbq_var_ALOOKUP_ALOOKUP:
 ∀var s s'. get_nbq_var s' var = get_nbq_var s var ⇔ ALOOKUP s'.nbq var = ALOOKUP s.nbq var
Proof
 rw [get_nbq_var_def] \\ every_case_tac
QED

Theorem get_nbq_var_sum_alookup:
 !s name v. get_nbq_var s name = sum_alookup s.nbq name
Proof
 rw [get_nbq_var_def] \\ TOP_CASE_TAC \\ metis_tac [sum_alookup_INR, sum_alookup_INL]
QED

Definition get_use_nbq_var_def:
 get_use_nbq_var s use_nbq name =
  if use_nbq then
   case get_nbq_var s name of
     INR v => INR v
   | INL e => get_var s name
  else
   get_var s name
End

Theorem get_use_nbq_var_sum_alookup:
 ∀s use_nbq name.
 get_use_nbq_var s use_nbq name =
 if use_nbq then sum_alookup (s.nbq ++ s.vars) name else sum_alookup s.vars name
Proof
 rw [get_use_nbq_var_def, get_var_sum_alookup, get_nbq_var_sum_alookup, sum_alookup_append]
QED

Theorem get_use_nbq_var_F:
 ∀s name. get_use_nbq_var s F name = get_var s name
Proof
 rw [get_use_nbq_var_def]
QED

(* Misc *)
Definition array_type_length_def:
 (array_type_length (VArray_t l) = INR l) ∧
 (array_type_length _ = INL TypeError)
End

Theorem array_type_length_INR:
 !t len. array_type_length t = INR len <=> t = VArray_t len
Proof
 Cases \\ rw [array_type_length_def]
QED

val get_VBool_data_def = Define `
  (get_VBool_data (VBool vs) = INR vs) /\
  (get_VBool_data _ = INL TypeError)`;

Theorem get_VBool_data_INR:
 !v b. get_VBool_data v = INR b <=> v = VBool b
Proof
 Cases \\ rw [get_VBool_data_def]
QED

val ver_liftVBool_def = Define `
  (ver_liftVBool f (VBool b) = INR (VBool (f b))) /\
  (ver_liftVBool _ _ = INL TypeError)`;

Theorem ver_liftVBool_INR:
 !v v' f. ver_liftVBool f v = INR v' <=> ?b. v = VBool b /\ v' = VBool (f b)
Proof
 Cases \\ rw [ver_liftVBool_def] \\ metis_tac []
QED

val ver_liftVBoolM_def = Define `
  (ver_liftVBoolM f (VBool b) = sum_map VBool (f b)) /\
  (ver_liftVBoolM _ _ = INL TypeError)`;

val get_VArray_data_def = Define `
  (get_VArray_data (VArray vs) = INR vs) /\
  (get_VArray_data _ = INL TypeError)`;

Theorem get_VArray_data_INR:
 !v v'. get_VArray_data v = INR v' <=> v = VArray v'
Proof
 Cases \\ rw [get_VArray_data_def]
QED

val ver_liftVArray_def = Define `
  (ver_liftVArray f (VArray vs) = INR (VArray (f vs))) /\
  (ver_liftVArray _ _ = INL TypeError)`;

Theorem ver_liftVArray_INR:
 ∀v v' f. ver_liftVArray f v = INR v' ⇔ ∃bs. v = VArray bs ∧ v' = VArray (f bs)
Proof
 Cases \\ rw [ver_liftVArray_def] \\ metis_tac []
QED

val ver_liftVArrayM_def = Define `
  (ver_liftVArrayM f (VArray vs) = sum_map VArray (f vs)) /\
  (ver_liftVArrayM _ _ = INL TypeError)`;

val ver_mapVArray_def = Define `
  (ver_mapVArray f (VArray vs) = INR (f vs)) /\
  (ver_mapVArray _ _ = INL TypeError)`;

Theorem ver_mapVArray_INR:
 ∀vs f x. ver_mapVArray f vs = INR x ⇔ ∃bs. vs = VArray bs ∧ x = f bs
Proof
 Cases \\ rw [ver_mapVArray_def, EQ_SYM_EQ]
QED

val ver_to_VArray_def = Define `
  (ver_to_VArray (VBool b) = VArray [VBool b]) /\
  (ver_to_VArray v = v)`;

(* Only makes sense for 1-dim arrays *)
val ver_msb_def = Define `
  (ver_msb (VArray (VBool h::t)) = INR h) /\
  (ver_msb _ = INL TypeError)`;

(** Oracle misc for non-deterministic values **)

val nd_value_def = Define `
 (nd_value oracle VBool_t <=>
  let (b, oracle') = oracle_bit oracle in (VBool b, oracle')) /\
 (nd_value oracle (VArray_t len) <=>
  let (bs, oracle') = oracle_bits oracle len in (v2ver bs, oracle'))`;

val nd_reset_def = Define `
 (nd_reset s (VBool _) = let (b, fbits) = oracle_bit s.fbits in
                          (s with fbits := fbits, VBool b)) /\
 (nd_reset s (VArray bs) = let (bs, fbits) = oracle_bits s.fbits (LENGTH bs) in
                            (s with fbits := fbits, v2ver bs))`

(** Expressions **)

(* Same as bitstringTheory.fixwidth_def *)
val ver_fixwidth_def = Define `
  ver_fixwidth n v =
    let l = LENGTH v in
      if l < n then (PAD_LEFT (VBool F) n v) else DROP (l − n) v`;

(*Theorem ver_fixwidth_fixwidth:
 ∀n v. ver_fixwidth n v = fixwidth n v
Proof
 simp [ver_fixwidth_def, fixwidth_def, zero_extend_def]
QED*)

val erun_bbop_def = Define `
 (erun_bbop And l r = (l /\ r)) /\
 (erun_bbop Or l r = (l \/ r)) ∧
 (erun_bbop Equal l r = (l = r))`;

(* These could probably been done directly instead of converting to a bitstring and back *)
val erun_abop_def = Define `
 (erun_abop BitwiseAnd l r = band l r) /\
 (erun_abop BitwiseOr l r = bor l r) /\
 (erun_abop BitwiseXor l r = bxor l r)`;

val erun_shift_def = Define `
 (erun_shift ShiftArithR l r = TAKE (LENGTH l) (GENLIST (K (HD l)) r ++ l)) /\
 (erun_shift ShiftLogicalL l r = ver_fixwidth (LENGTH l) (PAD_RIGHT (VBool F) (LENGTH l + r) l)) /\
 (erun_shift ShiftLogicalR l r = TAKE (LENGTH l) (GENLIST (K (VBool F)) r ++ l))`;

val erun_arith_def = Define `
 (erun_arith Plus (l:num) r _ = INR (l + r)) /\
 (* max - r term is 2comp, see e.g. word_2comp: *)
 (erun_arith Minus l r max = INR (l + ((max - r) MOD max))) /\
 (erun_arith Times l r _ = INR (l * r)) /\
 (* this is ok as we only consider non-negative numbers: *)
 (erun_arith Mod l r _ = if r = 0 then INL InvalidArgument else INR (l MOD r))`;

(* Compare operations for arrays *)
val erun_cmp_def = Define `
 (* same as wordsTheory.WORD_LT, i.e. signed less than: *)
 (erun_cmp LessThan l r = sum_bind (ver2n l) (\ln.
                          sum_bind (ver2n r) (\rn.
                          sum_bind (ver_msb l) (\lmsb.
                          sum_for (ver_msb r) (\rmsb.
                          (lmsb = rmsb) /\ ln < rn \/ lmsb /\ ~rmsb))))) /\
 (* same as wordsTheory.WORD_LO, i.e. unsigned less than *)
 (erun_cmp LowerThan l r = sum_bind (ver2n l) (\l.
                           sum_for (ver2n r) (\r.
                           l < r))) /\
 (* same as wordsTheory.WORD_LE: *)
 (erun_cmp LessThanOrEqual l r = sum_bind (ver2n l) (\ln.
                                 sum_bind (ver2n r) (\rn.
                                 sum_bind (ver_msb l) (\lmsb.
                                 sum_for (ver_msb r) (\rmsb.
                                 (lmsb = rmsb) /\ ln <= rn \/ lmsb /\ ~rmsb))))) /\
 (* same as wordsTheory.WORD_LS: *)
 (erun_cmp LowerThanOrEqual l r = sum_bind (ver2n l) (\l.
                                  sum_for (ver2n r) (\r.
                                  l <= r))) ∧

 (erun_cmp ArrayEqual l r = do
  l <- get_VArray_data l;
  r <- get_VArray_data r;
  return (l = r)
 od)`;

val erun_resize_def = Define `
 (erun_resize ZeroExtend l r = if LENGTH l < r then INR (PAD_LEFT (VBool F) r l)
                                               else INR (DROP (LENGTH l - r) l)) /\
 (erun_resize SignExtend l r = if LENGTH l <= r then INR (PAD_LEFT (HD l) r l)
                                                else INL TypeError)`;

val get_array_index_def = Define `
  (get_array_index i (VArray vs) = sum_revEL i vs) /\
  (get_array_index _ _ = INL TypeError)`;

Theorem get_array_index_INR:
 !v v' i. get_array_index i v = INR v' <=>
          ?bs. v = VArray bs /\ v' = revEL i bs /\ i < LENGTH bs
Proof
 Cases \\ rw [get_array_index_def] \\ eq_tac \\ rpt strip_tac'
 >- fs [sum_map_INR, sum_revEL_INR]
 >- rw [sum_revEL_revEL, sum_map_def]
QED

Definition get_array_slice_def:
 (get_array_slice msb lsb (VArray vs) =
  let len = LENGTH vs in
   if msb < len ∧ lsb ≤ msb then
    INR (VArray (TAKE (msb - lsb + 1) (DROP (len - msb - 1) vs)))
   else     
    INL InvalidIndex) /\
 (get_array_slice _ _ _ = INL TypeError)
End

Theorem get_array_slice_INR:
 ∀v v' ih il.
 get_array_slice ih il v = INR v' ⇔
 ∃vs. ih < LENGTH vs ∧
      il ≤ ih ∧
      v = VArray vs ∧
      v' = VArray (TAKE (ih − il + 1) (DROP (LENGTH vs − ih − 1) vs))
Proof
 Cases \\ rw [get_array_slice_def] \\ eq_tac \\ rw []
QED

val erun_get_var_def = Define `
 (erun_get_var _ s (Var vname) = get_var s vname) /\
 (erun_get_var fext s (InputVar vname) = fext vname) /\
 (erun_get_var _ _ _ = INL TypeError)`;

(* state -> num -> exp -> Error + value *)
val erun_def = Define `
 (erun _ _ (Const v) = return v) /\

 (erun fext s (Var vname) = erun_get_var fext s (Var vname)) /\

 (erun fext s (InputVar vname) = erun_get_var fext s (InputVar vname)) /\

 (erun fext s (ArrayIndex vexp _ i) = do
  v <- erun_get_var fext s vexp;
  i <- erun fext s i;
  i <- ver2n i;
  get_array_index i v
 od) /\

 (erun fext s (ArraySlice vexp msb lsb) = do
  v <- erun_get_var fext s vexp;
  get_array_slice msb lsb v
 od) /\

 (erun fext s (ArrayConcat lhs rhs) = do
  lhs <- erun fext s lhs;
  rhs <- erun fext s rhs;
  case (lhs, rhs) of
    (VArray lhs, VArray rhs) => return (VArray (lhs ++ rhs))
  | _ => INL TypeError
 od) /\

 (erun fext s (InlineIf c lhs rhs) = do
  c <- erun fext s c;
  c <- get_VBool_data c;
  if c then erun fext s lhs else erun fext s rhs
 od) /\

 (* Boolean operations *)
 (* Note that some operations should be lazy according to the standard,
    but this does not matter here because expressions in our semantics are side-effect free
    (although, we could get e.g. an out-of-bounds array read where the standard would not,
     but at the same time, the standard does not even have out-of-bounds errors so this is really
     an effect of another design choice). *)
 (erun fext s (BUOp _ exp) = sum_bind (erun fext s exp) (ver_liftVBool $~)) /\
 (erun fext s (BBOp lhs binop rhs) = do
  lhs <- erun fext s lhs;
  rhs <- erun fext s rhs;
  case (lhs, rhs) of
    (VBool lhs, VBool rhs) => return (VBool (erun_bbop binop lhs rhs))
  | _ => INL TypeError
 od) /\

 (* Array operations *)
 (erun fext s (ABOp lhs binop rhs) = do
  lhs <- erun fext s lhs;
  rhs <- erun fext s rhs;
  lhs <- ver2v lhs;
  rhs <- ver2v rhs;
  return (v2ver (erun_abop binop lhs rhs))
 od) /\

 (erun fext s (Shift lhs sop rhs) = do
  lhs <- erun fext s lhs;
  rhs <- erun fext s rhs;
  lhs <- get_VArray_data lhs;
  rhs <- ver2n rhs;
  return (VArray (erun_shift sop lhs rhs))
 od) /\

 (erun fext s (Arith lhs aop rhs) = do
  lhs <- erun fext s lhs;
  rhs <- erun fext s rhs;
  lhslen <- ver_mapVArray LENGTH lhs;
  lhs <- ver2n lhs;
  rhs <- ver2n rhs;
  res <- erun_arith aop lhs rhs (2 ** lhslen);
  (* For well-typed programs both inputs have same length, make sure same length out: *)
  ver_liftVArray (ver_fixwidth lhslen) (n2ver res)
 od) /\

 (erun fext s (Cmp lhs cmp rhs) = do
  lhs <- erun fext s lhs;
  rhs <- erun fext s rhs;
  res <- erun_cmp cmp lhs rhs;
  return (VBool res)
 od) /\

 (erun fext s (Resize lhs resize rhs) = do
  lhs <- erun fext s lhs;
  lhs <- get_VArray_data (ver_to_VArray lhs);
  res <- erun_resize resize lhs rhs;
  return (VArray res)
 od)`;

(** Statements **)

val set_index_def = Define `
  (set_index _ [] _ = INL InvalidIndex) /\
  (set_index 0 (v::vs) rhse = INR (rhse::vs)) /\
  (set_index (SUC i) (v::vs) rhse = sum_for (set_index i vs rhse) (CONS v))`;

val prun_set_var_index_def = Define `
  (prun_set_var_index vname i vd rhse =
   let len = LENGTH vd in
     if len <= i then
       INL InvalidIndex
     else
       sum_for (set_index (len - i - 1) vd rhse) (\vnew. (vname, VArray vnew)))`;

val set_slice_def = Define `
 set_slice take_n drop_n olddata newdata =
  (* Can be done more efficiently *)
  let first       = TAKE take_n olddata;
      first_skip  = DROP take_n olddata;
      middle      = TAKE drop_n first_skip;
      middle_skip = DROP drop_n first_skip in
  INR (first ++ newdata ++ middle_skip)`;

val prun_set_slice_def = Define `
 prun_set_slice ih il olddata newdata =
  let len = LENGTH olddata in
   if il <= ih /\ ih < len then
    set_slice (len - ih - 1) ((ih - il) + 1) olddata newdata
   else
    INL InvalidIndex`;

val assn_def = Define ‘
 (assn _ s use_nbq (NoIndexing vname) rhse = INR (vname, rhse)) /\

 (assn fext s use_nbq (Indexing vname _ i) rhse =
  sum_bind (erun fext s i) (\ie.
  sum_bind (ver2n ie) (\inum.
  sum_bind (get_use_nbq_var s use_nbq vname) (\v.
  sum_bind (get_VArray_data v) (\vd.
  (*sum_bind (get_VBool_data rhse) (\rhse.*)
  prun_set_var_index vname inum vd rhse))))) /\

 (assn fext s use_nbq (SliceIndexing vname ih il) rhs =
  sum_bind (get_use_nbq_var s use_nbq vname) (\v.
  sum_bind (get_VArray_data v) (\olddata.
  sum_bind (get_VArray_data rhs) (\rhsdata.
  sum_for  (prun_set_slice ih il olddata rhsdata) (\newdata.
   (vname, VArray newdata))))))’;

val prun_bassn_def = Define `
  prun_bassn fext s lhs rhse = sum_for (assn fext s F lhs rhse) (\(name, v). set_var s name v)`;

val prun_nbassn_def = Define `
 prun_nbassn fext s lhs rhse = sum_for (assn fext s T lhs rhse) (\(name, v). set_nbq_var s name v)`;

val prun_assn_lhs_prev_def = Define `
 (prun_assn_lhs_prev s (NoIndexing var) = get_var s var) /\
 (prun_assn_lhs_prev s _ = INL NotImplemented)`;

val prun_assn_rhs_def = Define `
 (prun_assn_rhs fext s lhs NONE = sum_map (nd_reset s) (prun_assn_lhs_prev s lhs)) /\
 (prun_assn_rhs fext s lhs (SOME e) = sum_map (\v. (s, v)) (erun fext s e))`;

val prun_def = Define `
 (prun fext s Skip = INR s) /\

 (prun fext s (Seq p0 p1) = do
  s' <- prun fext s p0;
  prun fext s' p1
 od) /\

 (prun fext s (IfElse c p0 p1) = do
  c <- erun fext s c;
  c <- get_VBool_data c;
  if c then (prun fext s p0) else (prun fext s p1)
 od) /\

 (* inefficient but simple implementation, runs e multiple times
    (in particular, the standard says that e must always be executed, which is not guaranteed here)... *)
 (prun fext s (Case ty e ((ccond, cprog)::cs) default) = do
  v <- erun fext s e;
  cv <- erun fext s ccond;
  (if (v = cv) then
    prun fext s cprog
  else
    prun fext s (Case ty e cs default))
 od) /\
 (prun fext s (Case ty e [] (SOME p)) = prun fext s p) /\
 (prun fext s (Case ty e [] NONE) = INR s) /\

 (prun fext s (BlockingAssign lhs rhs) = sum_bind (prun_assn_rhs fext s lhs rhs)
                                                  (λ(s, v). prun_bassn fext s lhs v)) /\

 (* Note that we for the semantics of non-blocking assignments assume that we never
    write both blockingly and non-blockingly to the same array.

    If we would be interested in programs with such mixed assignments, then we would
    have to keep track of indexes more carefully (i.e. make the semantics more complicated).
    For our purposes this assumption is fine, but when the semantics is used in other
    contexts this assumption might need re-evaluation.

    If the above assumption does not hold, non-blocking writes will overwrite all blocking writes
    (regardless of if indexes overlap or not). *)
 (prun fext s (NonBlockingAssign lhs rhs) = sum_bind (prun_assn_rhs fext s lhs rhs)
                                                     (λ(s, v). prun_nbassn fext s lhs v))`;

(** Module **)

(* Semantics *)

(* step and commit *)
Definition mstep_ffs_def:
 mstep_ffs fext fbits ps vs = do
  s <<- <| vars := vs; nbq := []; fbits := fbits |>;
  s <- sum_foldM (prun fext) s ps;
  return (s.nbq ++ s.vars, s.fbits)
 od
End

Definition mstep_combs_def:
 mstep_combs fext fbits ps vs = do
  s <<- <| vars := vs; nbq := []; fbits := fbits |>;
  s <- sum_foldM (prun fext) s ps;
  (* simply drop nbq since combs should never include any non-blocking assignments;
     i.e. non-blocking writes are no-ops in comb blocks. *)
  return (s.vars, s.fbits)
 od
End

Definition mrun_def:
 (mrun fext fbits ffs combs vs 0 = mstep_combs (fext 0) fbits combs vs) ∧
 (mrun fext fbits ffs combs vs (SUC n) = do
  (vs, fbits) <- mrun fext fbits ffs combs vs n;
  (vs, fbits) <- mstep_ffs (fext n) fbits ffs vs;
  mstep_combs (fext (SUC n)) fbits combs vs
 od)
End

Definition run_decls_def:
 (run_decls fbits [] vs = (fbits, vs)) /\
 (run_decls fbits ((var, data) :: decls) vs =
  case data.init of
    NONE => let (v, fbits') = nd_value fbits data.type in run_decls fbits' decls ((var, v)::vs)
  | SOME v => run_decls fbits decls ((var, v)::vs))
End

(* Top-level run *)
Definition run_def:
 run fext fbits m n = do
  (fbits', vs) <<- run_decls fbits m.decls [];
  mrun fext fbits' m.ffs m.combs vs n
 od
End

Definition decls_type_def:
 decls_type decls var = case ALOOKUP decls var of
                          NONE => INL UnknownVariable
                        | SOME data => INR data.type
End

Theorem decls_type_INR:
 !decls var t. decls_type decls var = INR t ⇔ ∃data. ALOOKUP decls var = SOME data ∧ data.type = t
Proof
 rw [decls_type_def, CaseEq"option"]
QED

Theorem decls_type_INL:
 !decls var e. decls_type decls var = INL e ⇔ e = UnknownVariable ∧ ALOOKUP decls var = NONE
Proof
 rw [decls_type_def, CaseEq"option", CONJ_COMM]
QED

(* Mostly for compatibility with old proofs? *)
Theorem decls_type_sum_alookup:
 !decls var. decls_type decls var = sum_alookup (MAP (λ(var, data). (var, data.type)) decls) var
Proof
 rw [decls_type_def, sum_alookup_def, alistTheory.ALOOKUP_MAP] \\ TOP_CASE_TAC \\ simp []
QED

Theorem decls_type_append:
 ∀l1 l2 var.
 decls_type (l1 ++ l2) var =
 case decls_type l1 var of
  INL e => decls_type l2 var
 | INR v => INR v
Proof
 simp [decls_type_sum_alookup, sum_alookup_append]
QED

(** Various syntactic predicates **)

val is_vervar_def = Define `
 (is_vervar (Var var) = T) /\
 (is_vervar (InputVar var) = T) /\
 (is_vervar _ = F)`;

Theorem is_vervar_cases:
 ∀e. is_vervar e ⇔ (∃var. e = Var var) ∨ (∃var. e = InputVar var)
Proof
 Cases \\ simp [is_vervar_def]
QED

val exp_var_def = Define `
 (exp_var (Var var) = SOME var) /\
 (exp_var (InputVar var) = SOME var) /\
 (exp_var _ = NONE)`;

(* Variables (not included external inputs) read by an expression *)
val evreads_def = Define `
  (evreads (Const _) = []) /\
  (evreads (Var vname) = [vname]) /\
  (evreads (InputVar _) = []) /\
  (evreads (ArrayIndex vexp _ iexp) = evreads vexp ++ evreads iexp) /\
  (evreads (ArraySlice vexp _ _) = evreads vexp) /\
  (evreads (ArrayConcat l r) = evreads l ++ evreads r) /\
  (evreads (InlineIf e1 e2 e3) = evreads e1 ++ evreads e2 ++ evreads e3) /\
  (evreads (BUOp _ e) = evreads e) /\
  (evreads (BBOp l _ r) = evreads l ++ evreads r) /\
  (evreads (ABOp l _ r) = evreads l ++ evreads r) /\
  (evreads (Shift l _ r) = evreads l ++ evreads r) /\
  (evreads (Arith l _ r) = evreads l ++ evreads r) /\
  (evreads (Cmp l _ r) = evreads l ++ evreads r) /\
  (evreads (Resize e _ _) = evreads e)`;

val evreads_index_def = Define `
 (evreads_index (Indexing _ _ i) = evreads i) /\
 (evreads_index _ = [])`;

val vreads_def = tDefine "vreads" `
  (vreads Skip = []) /\
  (vreads (Seq l r) = vreads l ++ vreads r) /\
  (vreads (IfElse c l r) = evreads c ++ vreads l ++ vreads r) /\
  (vreads (Case ty m cs d) = (evreads m) ++
                             (FLAT (MAP (\(cc, cb). evreads cc ++ vreads cb) cs)) ++
                             (case d of SOME d' => vreads d' | NONE => [])) /\
  (* NOTE: In some sense you are also reading lhs in some cases, e.g. when updating part of
           an array, but this is implementation-specific (more concretely, we also need to know about same shape...).
           But this predicate can be seen as "reads-excluding-reads-needed-for-writes". *)
  (vreads (BlockingAssign lhs rhs) = evreads_index lhs ++ (case rhs of SOME rhs => evreads rhs | NONE => [])) /\
  (vreads (NonBlockingAssign lhs rhs) = evreads_index lhs ++ (case rhs of SOME rhs => evreads rhs | NONE => []))`

  (WF_REL_TAC `measure vprog_size` \\ rw [] \\
   imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

(* Just makes sense for expressions used as lhs for assignments *)
val evwrites_def = Define ‘
 (evwrites (NoIndexing vname) = vname) /\
 (evwrites (Indexing vname _ _) = vname) /\
 (evwrites (SliceIndexing vname _ _) = vname)’;

(* Blocking writes *)
val vwrites_def = tDefine "vwrites" `
  (vwrites Skip = []) /\
  (vwrites (Seq l r) = vwrites l ++ vwrites r) /\
  (vwrites (IfElse c l r) = vwrites l ++ vwrites r) /\
  (vwrites (Case ty m cs d) = (FLAT (MAP (\(_, cb). vwrites cb) cs)) ++
                              (case d of SOME d' => vwrites d' | NONE => [])) /\
  (vwrites (BlockingAssign e _) = [evwrites e]) /\
  (vwrites (NonBlockingAssign _ _) = [])`

  (WF_REL_TAC `measure vprog_size` \\ rw [] \\
   imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

(* Non-blocking writes *)
val vnwrites_def = tDefine "vnwrites" `
  (vnwrites Skip = []) /\
  (vnwrites (Seq l r) = vnwrites l ++ vnwrites r) /\
  (vnwrites (IfElse c l r) = vnwrites l ++ vnwrites r) /\
  (vnwrites (Case ty m cs d) = (FLAT (MAP (\(_, cb). vnwrites cb) cs)) ++
                               (case d of SOME d' => vnwrites d' | NONE => [])) /\
  (vnwrites (BlockingAssign _ _) = []) /\
  (vnwrites (NonBlockingAssign e _) = [evwrites e])`

  (WF_REL_TAC `measure vprog_size` \\ rw [] \\
   imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

Definition writes_ok_def:
 writes_ok ps <=> !var. ~(MEM var (FLAT (MAP vwrites ps)) /\ MEM var (FLAT (MAP vnwrites ps)))
End

Definition writes_overlap_ok_def:
 writes_overlap_ok combs ffs ⇔
 ∀var. MEM var (FLAT (MAP vwrites combs)) ⇒ ¬MEM var (FLAT (MAP vwrites ffs)) ∧ ¬MEM var (FLAT (MAP vnwrites ffs))
End

Definition writes_overlap_ok_pseudos_def:
 writes_overlap_ok_pseudos pseudos ffs ⇔
 ∀var. member string_cmp var pseudos ⇒ ¬MEM var (FLAT (MAP vwrites ffs)) ∧ ¬MEM var (FLAT (MAP vnwrites ffs))
End

Definition module_ok_def:
 module_ok m ⇔ writes_ok m.ffs ∧ writes_ok m.combs ∧ writes_overlap_ok m.combs m.ffs
End

val _ = export_theory ();
