open hardwarePreamble;

open alistTheory wordsTheory stringTheory bitstringTheory sptreeTheory;
open wordsLib;

open sumExtraTheory;

val _ = new_theory "verilog";

(*******************************
  Verilog syntax
 *******************************)

(** Verilog values **)
val _ = Datatype `
  value = VBool bool
        | VArray (value list)`;

val value_size_def = definition "value_size_def";

val MEM_IMP_value_size = Q.store_thm("MEM_IMP_value_size",
  `!xs x. MEM x xs ==> value_size x < value1_size xs`,
  Induct \\ rw [value_size_def] \\ res_tac \\ DECIDE_TAC);

val _ = type_abbrev("envT", ``:(string, value) alist``);

val isVBool_def = Define `
 (isVBool (VBool _) = T) /\
 (isVBool (VArray _) = F)`;

(* Verilog to bool (VBool) *)
val ver2bool_def = Define `
  (ver2bool (VBool b) = INR b) /\
  (ver2bool (VArray _) = INL TypeError)`;

(* Verilog to bitstring (1-dim VArray) *)
val ver2v_def = Define `
  (ver2v (VBool _) = INL TypeError) /\
  (ver2v (VArray vs) = sum_mapM ver2bool vs)`;

val ver2n_def = Define `
  ver2n v = sum_map v2n (ver2v v)`;

val v2ver_def = Define `
  v2ver bs = VArray (MAP VBool bs)`;

val n2ver_def = Define `
  n2ver n = v2ver (n2v n)`;

val w2ver_def = Define `
  w2ver w = VArray (MAP VBool (w2v w))`;

val ver2w_def = Define `
 ver2w v = sum_map v2w (ver2v v)`;

(* Metatheory for mapping from and to Verilog values *)

val sum_mapM_VBool = Q.store_thm("sum_mapM_VBool",
 `!l. sum_mapM ver2bool (MAP VBool l) = INR l`,
 Induct \\ rw [sum_mapM_def, ver2bool_def, sum_map_def]);

val ver2v_w2ver = Q.store_thm("ver2v_w2ver",
 `!w. ver2v (w2ver w) = INR (w2v w)`,
 rw [ver2v_def, w2ver_def, sum_mapM_VBool]);

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
 simp [ver2w_def, w2ver_def, ver2v_def, sum_mapM_VBool, sum_map_def]);

(*
val GENLIST_K_APPEND = Q.store_thm("GENLIST_K_APPEND",
 `!a b c. GENLIST (K c) (a + b) = GENLIST (K c) b ⧺ GENLIST (K c) a`,
 rw [GENLIST_APPEND, combinTheory.K_DEF]);

val GENLIST_K_F_APPEND_F = Q.store_thm("GENLIST_K_F_APPEND_F",
 `GENLIST (K F) (dimindex (:'a) − 1) ⧺ [F] = GENLIST (K F) (dimindex (:'a))`,
 `[F] = GENLIST (K F) 1` by rw [] \\ pop_assum (fn th => PURE_REWRITE_TAC [th]) \\
 rw [GSYM GENLIST_K_APPEND, DIMINDEX_GT_0]);
*)

val sum_mapM_ver2bool_VBool = Q.store_thm("sum_mapM_ver2bool_VBool",
 `!l. sum_mapM ver2bool (MAP VBool l) = INR l`,
 Induct \\ rw [sum_mapM_def, ver2bool_def, sum_map_def]);

val ver2v_n2ver = Q.store_thm("ver2v_n2ver",
 `!n. ver2v (n2ver n) = INR (n2v n)`,
 rw [n2ver_def, ver2v_def, v2ver_def, ver2v_def, sum_mapM_ver2bool_VBool]);

val ver2n_n2ver = Q.store_thm("ver2n_n2ver",
 `!n. ver2n (n2ver n) = INR n`,
 rw [ver2n_def, ver2v_n2ver, sum_map_def]);

val ver2n_w2ver = Q.store_thm("ver2n_w2ver",
 `!w. ver2n (w2ver w) = INR (w2n w)`,
 rw [ver2n_def, w2ver_def, ver2v_def, sum_mapM_ver2bool_VBool, sum_map_def, v2n_w2v]);

val w2v_inj = Q.store_thm("w2v_inj",
 `!x y. w2v x = w2v y ==> x = y`,
 metis_tac [v2w_w2v]);

val w2ver_bij = Q.store_thm("w2ver_bij",
 `!x y. (w2ver x = w2ver y) <=> (x = y)`,
 rpt strip_tac \\ EQ_TAC \\ rw [w2ver_def, MAP_inj, w2v_inj]);

(* Assignments must keep variable types, and equality checks can only be done between values
   of the same type.

   We assume that we can never get empty VArrays in top-level call, because such values are not
   "well-formed". *)
val same_shape_def = Define `
 (same_shape (VBool _) (VBool _) = T) /\
 (same_shape (VArray []) (VArray []) = T) /\
 (same_shape (VArray (x::xs)) (VArray (y::ys)) =
  (same_shape x y /\ same_shape (VArray xs) (VArray ys))) /\
 (same_shape _ _ = F)`;

(* Verilog ASTs *)

(* "Boolean" operators, i.e. logical operations that only works on booleans,
   but could probably be extended to arrays if needed (if so, would still return a boolean).

   Note: In Verilog code this looks polymorphic, in the sense that = is use both for booleans
         and vectors, but it's probably not polymorphic in any real sense; so here we have two
         different operations. *)

(* Boolean unary operators *)
val _ = Datatype `
  buop = Not`;

(* Boolean binary operators *)
val _ = Datatype `
  bbop = And
       | Equal
       | NotEqual
       | Or`;

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
  cmp = ArrayEqual
      | ArrayNotEqual
      (* The following two operations are not Verilog operations, as there whether something is
         less than or lower than depends on if the value is signed or not, a notion we don't have
         here. So when this is printed, sign casts will be inserted into the code... *)
      | LessThan (* signed, in wordsTheory: < *)
      | LowerThan (* unsigned, in wordsTheory: <+ *)
      | LessThanOrEqual
      | LowerThanOrEqual`;

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

      (* Single indexing: variable (e.g. Var "foo") -> indices expressions *)
      | ArrayIndex exp (exp list)

      (* Indexing with upper and lower bound, assume that the bounds are constants.

         From "7.4.6 Indexing and slicing of arrays":

         > Slices of an array can only apply to one dimension, but other dimensions
         > can have single index values in an expression.

         So the assumption make sense, but we only allow a strict subset of full Verilog.

         Variable expression (e.g. Var "foo") -> indices expressions -> indices for subarray of last array *)
      | ArraySlice exp (exp list) num num

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
        (* For arrays, reduces to boolean. Equality for arrays is here. *)
      | Cmp exp cmp exp

        (* This is a hack because we do not have resizing (and sign handling) formalized,
           should be removed in separate later pass (as done with non-blocking assignments).

           Removing them requires non-local reasoning, i.e. reasoning not compatible with the
           translator (first-step) approach. *)
      | Resize exp resize num`;

val exp_size_def = definition "exp_size_def";

val MEM_IMP_exp_size = Q.store_thm("MEM_IMP_exp_size",
  `!xs x. MEM x xs ==> exp_size x < exp1_size xs`,
  Induct \\ rw [exp_size_def] \\ res_tac \\ DECIDE_TAC);

(** Programs (actually, code in processes) **)
val _ = Datatype `
  vprog = Skip
(*      | Return exp <-- TODO: Not relevant currently, only needed if we would support function calls *)
        | Seq vprog vprog
          (* lhs var, compare operator, rhs var, true branch, false branch *)
        | IfElse exp vprog vprog
          (* match subject, cases (first in list = first in program order), optional default case *)
        | Case exp ((exp # vprog) list) (vprog option)
        | BlockingAssign exp exp
        | NonBlockingAssign exp exp`;

val vprog_size_def = definition "vprog_size_def";

val MEM_IMP_vprog_size = Q.store_thm("MEM_IMP_vprog_size",
  `!cs cc cb. MEM (cc, cb) cs ==> vprog_size cb < vprog1_size cs`,
  Induct \\ rw [vprog_size_def] \\ rw [vprog_size_def] \\ res_tac \\ DECIDE_TAC);

(*******************************
  Process semantics
 *******************************)

(* State *)
val pstate_def = Datatype `
  pstate =
    <| vars : envT     (* global vars *)
  (* ; lvars : envT    (* local vars, not needed for now *) *)
     ; nbq : envT |>`; (* non-blocking assignment queue *)

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

(** Evaluation

Informal invariant: Array shapes must be maintained always, this is an implicit assumption everywhere.
**)

(** Expressions **)

val get_VBool_def = Define `
  (get_VBool_data (VBool vs) = INR vs) /\
  (get_VBool_data _ = INL TypeError)`;

val ver_liftVBool_def = Define `
  (ver_liftVBool f (VBool b) = INR (VBool (f b))) /\
  (ver_liftVBool _ _ = INL TypeError)`;

val ver_liftVBoolM_def = Define `
  (ver_liftVBoolM f (VBool b) = sum_map VBool (f b)) /\
  (ver_liftVBoolM _ _ = INL TypeError)`;

val get_VArray_def = Define `
  (get_VArray_data (VArray vs) = INR vs) /\
  (get_VArray_data _ = INL TypeError)`;

val ver_liftVArray_def = Define `
  (ver_liftVArray f (VArray vs) = INR (VArray (f vs))) /\
  (ver_liftVArray _ _ = INL TypeError)`;

val ver_liftVArrayM_def = Define `
  (ver_liftVArrayM f (VArray vs) = sum_map VArray (f vs)) /\
  (ver_liftVArrayM _ _ = INL TypeError)`;

val ver_mapVArray_def = Define `
  (ver_mapVArray f (VArray vs) = INR (f vs)) /\
  (ver_mapVArray _ _ = INL TypeError)`;

val ver_to_VArray_def = Define `
  (ver_to_VArray (VBool b) = VArray [VBool b]) /\
  (ver_to_VArray v = v)`;

val get_1dim_VArray_data_def = Define `
  (get_1dim_VArray_data (VArray vs) = if vs <> [] /\ EVERY isVBool vs then INR vs else INL TypeError) /\
  (get_1dim_VArray_data _ = INL TypeError)`;

(* Only makes sense for 1-dim arrays *)
val ver_msb_def = Define `
  (ver_msb (VArray (VBool h::t)) = INR h) /\
  (ver_msb _ = INL TypeError)`;

(* Same as bitstringTheory.fixwith_def *)
val ver_fixwidth_def = Define `
  ver_fixwidth n v =
    let l = LENGTH v in
      if l < n then (PAD_LEFT (VBool F) n v) else DROP (l − n) v`;

val erun_bbop_def = Define `
 (erun_bbop And l r = (l /\ r)) /\
 (erun_bbop Equal l r = (l = r)) /\
 (erun_bbop NotEqual l r = (l <> r)) /\
 (erun_bbop Or l r = (l \/ r))`;

(* These could probably been done directly instead of converting to a bitstring and back *)
val erun_abop_def = Define `
 (erun_abop BitwiseAnd l r = band l r) /\
 (erun_abop BitwiseOr l r = bor l r) /\
 (erun_abop BitwiseXor l r = bxor l r)`;

val erun_shift_def = Define `
 (erun_shift ShiftArithR l r = let len = LENGTH l in GENLIST (K (HD l)) (MIN len r) ++ TAKE (len - r) l) /\
 (erun_shift ShiftLogicalL l r = ver_fixwidth (LENGTH l) (PAD_RIGHT (VBool F) (LENGTH l + r) l)) /\
 (erun_shift ShiftLogicalR l r = ver_fixwidth (LENGTH l) (TAKE (LENGTH l - r) l))`;

val erun_arith_def = Define `
 (erun_arith Plus (l:num) r _ = l + r) /\
 (erun_arith Minus l r max = l + ((max - r) MOD max)) /\ (* max - r term is 2comp, see e.g. word_2comp *)
 (erun_arith Times l r _ = l * r) /\
 (erun_arith Mod l r _ = l MOD r)`;

(* Compare operations for arrays *)
val erun_cmp_def = Define `
 (erun_cmp ArrayEqual l r = INR (l = r)) /\
 (erun_cmp ArrayNotEqual l r = INR (l <> r)) /\
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
                           l <= r)))`;

(* Can use HD here because we have checked that l is a valid 1-dim array before calling this *)
val erun_resize_def = Define `
 (erun_resize ZeroExtend l r = if LENGTH l < r then INR (PAD_LEFT (VBool F) r l)
                                               else INR (DROP (LENGTH l - r) l)) /\
 (erun_resize SignExtend l r = if LENGTH l <= r then INR (PAD_LEFT (HD l) r l)
                                                else INL TypeError)`;

val get_array_index_def = Define `
  (get_array_index [] v = INR v) /\
  (get_array_index (i::is) (VArray vs) = sum_bind (sum_revEL i vs)
                                                  (get_array_index is)) /\
  (get_array_index _ _ = INL TypeError)`;

val get_array_slice_def = Define `
  (get_array_slice msb lsb (VArray vs) =
   let len = LENGTH vs in
     if len < msb \/ msb < lsb then
       INL InvalidIndex
     else
       INR (VArray (TAKE (msb - lsb + 1) (DROP (len - msb - 1) vs)))) /\
  (get_array_slice _ _ _ = INL TypeError)`;

val erun_get_var_def = Define `
 (erun_get_var _ s (Var vname) = get_var s vname) /\
 (erun_get_var fext s (InputVar vname) = fext vname) /\
 (erun_get_var _ _ _ = INL TypeError)`;

(* state -> num -> exp -> Error + value *)
val erun_def = tDefine "erun" `
 (erun _ _ (Const v) = INR v) /\
 (erun fext s (Var vname) = erun_get_var fext s (Var vname)) /\
 (erun fext s (InputVar vname) = erun_get_var fext s (InputVar vname)) /\
 (erun fext s (ArrayIndex vexp is) = (* index array must be non-empty *)
                                 if is = [] then
                                   INL InvalidIndex
                                 else
                                   sum_bind (erun_get_var fext s vexp) (\v.
                                   sum_bind (sum_mapM (erun fext s) is) (\ise.
                                   sum_bind (sum_mapM ver2n ise) (\isn.
                                   get_array_index isn v)))) /\
 (* TODO: Shortcut here as we do not need "deep" indexing currently. *)
 (erun fext s (ArraySlice vexp [] msb lsb) = sum_bind (erun_get_var fext s vexp) (get_array_slice msb lsb)) /\
 (erun _ _ (ArraySlice _ _ _ _) = INL NotImplemented) /\

 (* TODO: This is only concatenation for 1-dim arrays *)
 (erun fext s (ArrayConcat lhs rhs) = sum_bind (erun fext s lhs) (\lhs.
                                      sum_bind (erun fext s rhs) (\rhs.
                                      sum_bind (get_1dim_VArray_data lhs) (\lhs.
                                      sum_for (get_1dim_VArray_data rhs) (\rhs.
                                       VArray (lhs ++ rhs)))))) /\

 (erun fext s (InlineIf c lhs rhs) = sum_bind (erun fext s c) (\c.
                                       sum_bind (get_VBool_data c) (\c.
                                       if c then erun fext s lhs else erun fext s rhs))) /\

 (* Boolean operations *)
 (erun fext s (BUOp _ exp) = sum_bind (erun fext s exp) (ver_liftVBool $~)) /\
 (erun fext s (BBOp lhs binop rhs) = sum_bind (erun fext s lhs) (\lhs.
                                       sum_bind (erun fext s rhs) (\rhs.
                                       case (lhs, rhs) of
                                          (VBool lhs, VBool rhs) => INR (VBool (erun_bbop binop lhs rhs))
                                        | _ => INL TypeError))) /\

 (* Array operations *)
 (erun fext s (ABOp lhs binop rhs) = sum_bind (erun fext s lhs) (\lhs.
                                       sum_bind (erun fext s rhs) (\rhs.
                                       if same_shape lhs rhs then
                                         sum_bind (ver2v lhs) (\lhs.
                                         sum_for (ver2v rhs) (\rhs.
                                         v2ver (erun_abop binop lhs rhs)))
                                       else
                                         INL TypeError))) /\
 (erun fext s (Shift lhs sop rhs) = sum_bind (erun fext s lhs) (\lhs.
                                      sum_bind (erun fext s rhs) (\rhs.
                                      (* Sameness does not make sense here. *)
                                      sum_bind (get_1dim_VArray_data lhs) (\lhs.
                                      sum_for (ver2n rhs) (\rhs.
                                      VArray (erun_shift sop lhs rhs)))))) /\
 (erun fext s (Arith lhs aop rhs) = sum_bind (erun fext s lhs) (\lhs.
                                      sum_bind (erun fext s rhs) (\rhs.
                                      if same_shape lhs rhs then
                                        sum_bind (ver_mapVArray LENGTH lhs) (\lhslen.
                                        sum_bind (ver2n lhs) (\lhsn.
                                        sum_bind (ver2n rhs) (\rhsn.
                                        ver_liftVArray (ver_fixwidth lhslen)
                                                       (n2ver (erun_arith aop lhsn rhsn (2 ** lhslen))))))
                                      else
                                        INL TypeError))) /\
 (erun fext s (Cmp lhs cmp rhs) = sum_bind (erun fext s lhs) (\lhs.
                                    sum_bind (erun fext s rhs) (\rhs.
                                    if same_shape lhs rhs then
                                      sum_for (erun_cmp cmp lhs rhs) VBool
                                    else
                                      INL TypeError))) /\
 (erun fext s (Resize lhs resize rhs) = sum_bind (erun fext s lhs) (\lhs.
                                          sum_bind (get_1dim_VArray_data (ver_to_VArray lhs)) (\lhs.
                                          sum_map VArray (erun_resize resize lhs rhs))))`

 (WF_REL_TAC `measure (\(_, _, e). exp_size e)` \\ rw [] \\
 drule MEM_IMP_exp_size \\ DECIDE_TAC);

(** Statements **)

val set_index_def = Define `
  (set_index _ [] _ = INL InvalidIndex) /\
  (set_index 0 (v::vs) rhse = if same_shape rhse v then INR (rhse::vs) else INL TypeError) /\
  (set_index (SUC i) (v::vs) rhse = sum_for (set_index i vs rhse) (CONS v))`;

val prun_set_var_index_def = Define `
  (prun_set_var_index vname i vd rhse =
   let len = LENGTH vd in
     if len <= i then
       INL InvalidIndex
     else
       sum_for (set_index (len - i - 1) vd rhse) (\vnew. (vname, VArray vnew)))`;

(* TODO: Does not need support array slice assignments (yet), which is the most ugly case *)
val assn_def = Define `
 (assn _ s (Var vname) rhse =
  sum_bind (get_var s vname) (\v.
  if same_shape rhse v then INR (vname, rhse)
                       else INL TypeError)) /\
 (assn fext s (ArrayIndex (Var vname) [i]) rhse =
  sum_bind (erun fext s i) (\ie.
  sum_bind (ver2n ie) (\inum.
  sum_bind (get_var s vname) (\v.
  sum_bind (get_VArray_data v) (\vd.
  prun_set_var_index vname inum vd rhse))))) /\
 (assn _ _ (ArrayIndex _ _) _ = INL NotImplemented) /\
 (assn _ _ (ArraySlice _ _ _ _) _ = INL NotImplemented) /\
 (assn _ _ _ _ = INL TypeError)`;

(* Right hand side already evaluated, this also breaks writing non-blockingly to the same array in the same cycle for most cases *)
val prun_bassn_def = Define `
  prun_bassn fext s lhs rhse = sum_for (assn fext s lhs rhse) (\(name, v). set_var s name v)`;

val prun_nbassn_def = Define `
 prun_nbassn fext s lhs rhse = sum_for (assn fext s lhs rhse) (\(name, v). set_nbq_var s name v)`;

val prun_def = Define `
  (prun _ s Skip = INR s) /\
  (prun fext s (Seq p0 p1) = sum_bind (prun fext s p0) (\s'. prun fext s' p1)) /\
  (prun fext s (IfElse c p0 p1) =
   sum_bind (erun fext s c) (\ce.
   sum_bind (get_VBool_data ce) (\cv.
   if cv then (prun fext s p0) else (prun fext s p1)))) /\
  (prun fext s (Case e ((ccond, cprog)::cs) default) =
   (* inefficient but simple implementation, runs e multiple times... *)
   sum_bind (erun fext s e) (\ev.
   sum_bind (erun fext s ccond) (\cconde.
   (* TODO: Should check same shape here also maybe...
            would probably make proofs more irritating, but doable. *)
   if (ev = cconde) then
     prun fext s cprog
   else
     prun fext s (Case e cs default)))) /\
  (prun fext s (Case e [] (SOME p)) = prun fext s p) /\
  (prun _ s (Case e [] NONE) = INR s) /\
  (prun fext s (BlockingAssign lhs rhs) = sum_bind (erun fext s rhs) (prun_bassn fext s lhs)) /\
  (prun fext s (NonBlockingAssign lhs rhs) = sum_bind (erun fext s rhs) (prun_nbassn fext s lhs))`;

(*******************************
  Module semantics
 *******************************)

(* State *)

val mget_var_def = Define `
  mget_var (vs:envT) name =
       case ALOOKUP vs name of
           SOME v => INR v
         | NONE => INL UnknownVariable`;

(* Evaluation function *)

val mstep_def = Define `
  mstep fextt ps s = sum_foldM (prun fextt) s ps`;

(* mstep, then commit *)
val mstep_commit_def = Define `
 mstep_commit fextt ps vs = let s = <| vars := vs; nbq := [] |> in
                            sum_map (\s. s.nbq ++ s.vars) (mstep fextt ps s)`;

val mrun_def = Define `
  (mrun fext ps vs 0 = INR vs) /\
  (mrun fext ps vs (SUC n) = sum_bind (mrun fext ps vs n) (mstep_commit (fext n) ps))`;

(** Various syntactic predicates **)

val is_vervar_def = Define `
 (is_vervar (Var var) = T) /\
 (is_vervar (InputVar var) = T) /\
 (is_vervar _ = F)`;

val evreads_def = tDefine "evreads" `
  (evreads (Const _) = []) /\
  (evreads (Var vname) = [vname]) /\
  (evreads (InputVar _) = []) /\ (* TODO: <-- this is now variables that can be affected by writes? *)
  (evreads (ArrayIndex vexp es) = evreads vexp ++ FLAT (MAP evreads es)) /\
  (evreads (ArraySlice vexp es _ _) = evreads vexp ++ FLAT (MAP evreads es)) /\
  (evreads (ArrayConcat l r) = evreads l ++ evreads r) /\
  (evreads (InlineIf e1 e2 e3) = evreads e1 ++ evreads e2 ++ evreads e3) /\
  (evreads (BUOp _ e) = evreads e) /\
  (evreads (BBOp l _ r) = evreads l ++ evreads r) /\
  (evreads (ABOp l _ r) = evreads l ++ evreads r) /\
  (evreads (Shift l _ r) = evreads l ++ evreads r) /\
  (evreads (Arith l _ r) = evreads l ++ evreads r) /\
  (evreads (Cmp l _ r) = evreads l ++ evreads r) /\
  (evreads (Resize e _ _) = evreads e)`

  (WF_REL_TAC `measure exp_size` \\ rw [] \\
   imp_res_tac MEM_IMP_exp_size \\ DECIDE_TAC);

val evreads_index_def = Define `
 (evreads_index (ArrayIndex _ es) = FLAT (MAP evreads es)) /\
 (evreads_index (ArraySlice _ es _ _) = FLAT (MAP evreads es)) /\
 (evreads_index _ = [])`;

val vreads_def = tDefine "vreads" `
  (vreads Skip = []) /\
  (vreads (Seq l r) = vreads l ++ vreads r) /\
  (vreads (IfElse c l r) = evreads c ++ vreads l ++ vreads r) /\
  (vreads (Case m cs d) = (evreads m) ++
                          (FLAT (MAP (\(cc, cb). evreads cc ++ vreads cb) cs)) ++
                          (case d of SOME d' => vreads d' | NONE => [])) /\
  (* NOTE: In some sense you are also reading lhs in some cases, e.g. when updating part of
           an array, but this is implementation-specific (more concretely, we also need to know about same shape...).
           But this predicate can be seen as "reads-excluding-reads-needed-for-writes". *)
  (vreads (BlockingAssign lhs rhs) = evreads_index lhs ++ evreads rhs) /\
  (vreads (NonBlockingAssign lhs rhs) = evreads_index lhs ++ evreads rhs)`

  (WF_REL_TAC `measure vprog_size` \\ rw [] \\
   imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

(* Just makes sense for expressions used as lhs for assignments *)
val evwrites_def = Define `
 (evwrites (Var vname) = [vname]) /\
 (evwrites (ArrayIndex (Var vname) _) = [vname]) /\
 (evwrites (ArraySlice (Var vname) _ _ _) = [vname]) /\
 (evwrites _ = [])`;

(* Blocking writes *)
val vwrites_def = tDefine "vwrites" `
  (vwrites Skip = []) /\
  (vwrites (Seq l r) = vwrites l ++ vwrites r) /\
  (vwrites (IfElse c l r) = vwrites l ++ vwrites r) /\
  (vwrites (Case m cs d) = (FLAT (MAP (\(_, cb). vwrites cb) cs)) ++
                           (case d of SOME d' => vwrites d' | NONE => [])) /\
  (vwrites (BlockingAssign e _) = evwrites e) /\
  (vwrites (NonBlockingAssign _ _) = [])`

  (WF_REL_TAC `measure vprog_size` \\ rw [] \\
   imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

(* Non-blocking writes *)
val vnwrites_def = tDefine "vnwrites" `
  (vnwrites Skip = []) /\
  (vnwrites (Seq l r) = vnwrites l ++ vnwrites r) /\
  (vnwrites (IfElse c l r) = vnwrites l ++ vnwrites r) /\
  (vnwrites (Case m cs d) = (FLAT (MAP (\(_, cb). vnwrites cb) cs)) ++
                            (case d of SOME d' => vnwrites d' | NONE => [])) /\
  (vnwrites (BlockingAssign _ _) = []) /\
  (vnwrites (NonBlockingAssign e _) = evwrites e)`

  (WF_REL_TAC `measure vprog_size` \\ rw [] \\
   imp_res_tac MEM_IMP_vprog_size \\ DECIDE_TAC);

val _ = export_theory ();
