structure translatorLib =
struct

open hardwarePreamble;

open verilogTheory;

open translatorTheory;
open translatorCoreLib translatorExpLib translatorStmLib;

open stringSyntax listSyntax;

(* Test:
open avgCircuitTheory;
val module_def = avg_def;
val outputs = ["avg"];
val comms = ["h0", "h1", "h2", "h3"];

open pulseCounterCircuitTheory;
val module_def = pcounter_def;
val outputs = ["done"];
val comms = ["count"];

val tm = “s' with done := T”

val s = “s:state”
val s' = “s':state”
*)

fun build_state_rel_var comms (field, data : allfieldinfo) = let
 val ty = #ty data
 val accessf = #accessor data
 val fieldHOL = fromMLstring field
 val pred = accessf |> type_of |> dom_rng |> snd |> predicate_for_type
in
 if mem field comms then
  [``state_rel_cvar hol_s hol_s' ver_s ^fieldHOL ^pred ^accessf``]
 else
  [``state_rel_var hol_s' ver_s ^fieldHOL ^pred ^accessf``]
end;

fun build_module_state_rel_var (field, data : allfieldinfo) = let
 val ty = #ty data
 val accessf = #accessor data
 val fieldHOL = fromMLstring field
 val pred = accessf |> type_of |> dom_rng |> snd |> predicate_for_type
in
  ``module_state_rel_var hol_s ver_s ^fieldHOL ^pred ^accessf``
end;

fun build_fextv_var (field, field_data : TypeBase.rcd_fieldinfo) = let
 val fieldHOL = fromMLstring field
 val accessf = #accessor field_data
 val pred = accessf |> dest_const |> snd |> dom_rng |> snd |> hol2ver_for_type
in
 ``fextv ^fieldHOL = INR (^pred (^accessf fext))``
end;

fun build_fextv_others vars = let
 val vars = pred_setSyntax.mk_set vars
 val tm = ``!var. var ∉ ^vars ⇒ fextv var = INL UnknownVariable``
in
 inst [ alpha |-> value_ty ] tm
end;

(* Prioritize "-" since we might be translating interactively *)
fun get_def theory tm = let
 val name = tm |> dest_const |> fst

 fun get_first_def [(t, name)] = fetch t name
   | get_first_def ((t, name) :: defs) =
      case total (fetch t) (name) of
          NONE => get_first_def defs
        | SOME def => def
in
 get_first_def [("-", name ^ "_trans"), ("-", name ^ "_def"),
                (theory, name ^ "_trans"), (theory, name ^ "_def")]
end;

fun procs2hardware tstate theory procs = let
 val procs = procs |> dest_comb |> snd |> listSyntax.dest_list |> fst |> rev
 val trans = map (step2hardware tstate o get_def theory) procs
in
 case trans of
  [] => ISPECL [#fext_rel tstate, #rel tstate] Eval_list_nil
  | [t] => MATCH_MP Eval_Eval_list_base t
  | t::ts => foldr (fn (t, th) => MATCH_MP Eval_Eval_list_step (CONJ t th))
                   (MATCH_MP Eval_Eval_list_base t)
                   ts
end;

fun build_fextty (field, field_data : TypeBase.rcd_fieldinfo) =
 pairSyntax.mk_pair(fromMLstring field, field_data |> #ty |> verty_for_type);

fun build_decl outputs oracle (field, v) = let
 fun lift_option_value opt =
  case opt of
    NONE => optionSyntax.mk_none value_ty
  | SOME v => optionSyntax.mk_some v

 val ty = type_of v
 val verty = verty_for_type ty
 val v' = if free_in oracle v then
           optionSyntax.mk_none value_ty
          else if can dom_rng ty then (* is function type, i.e. 2d array *)
           (if combinSyntax.is_K_1 v andalso
              (v |> combinSyntax.dest_K_1 |> dest_word_literal) = Arbnum.zero then
             optionSyntax.mk_some (mk_build_zero verty)
            else
             raise UnableToTranslate (v, "unsupported initial value"))
          else
           optionSyntax.mk_some (mk_comb(hol2ver_for_type ty, v))

 val decl = TypeBase.mk_record (“:var_metadata”, [("output", if mem field outputs then T else F),
                                                  ("type", verty),
                                                  ("init", v')])
 val decl = pairSyntax.mk_pair(fromMLstring field, decl)
in
 decl
end;

(* Too simple but works for now... *)
fun build_module_rel_init module_rel init decls =
 prove(“^module_rel ^init (SND (run_decls fbits ^decls []))”, cheat (*EVAL_TAC \\ simp []*));

fun dest_record_rec tm =
 tm
 |> TypeBase.dest_record
 |> snd
 |> map (fn (f, d) => if TypeBase.is_record d then dest_record_rec d else [(f, d)])
 |> flatten;

(*
TODOs for the above (need to handle 2d arrays):

rw [module_state_rel_def, module_state_rel_var_def] \\
rw [run_decls_def, decls_def]

computeLib.del_consts [“build_zero”]
CONV_TAC (RAND_CONV EVAL) \\
computeLib.del_funs [build_zero_def]
rw [module_state_rel_def, module_state_rel_var_def] \\

TRY (EVAL_TAC \\ simp [] \\ NO_TAC)
EVAL_TAC \\ simp []*)

fun init_translator module_def abstract_fields comms = let
 val (module, def) = module_def |> concl |> dest_eq
 val state_ty = module |> dest_const |> snd |> dom_rng |> snd |> dom_rng |> snd |> dom_rng |> snd
 val fext_ty = module |> dest_const |> snd |> dom_rng |> fst |> dom_rng |> snd

  (* Build tstate... *)

 (* TODO: Name... *)
 val state_rel_def =
 all_fields_of state_ty
 |> map (build_state_rel_var comms)
 |> flatten
 |> list_mk_conj
 |> (fn tm => Define `state_rel hol_s hol_s' ver_s = ^tm`);

 val is_state_rel_var_def =
 all_fields_of state_ty
 |> map (fromMLstring o fst)
 |> (fn vars => listSyntax.mk_list (vars, string_ty))
 |> (fn tm => Define `is_state_rel_var var = MEM var ^tm`);

 (* TODO: Name... *)
 val module_state_rel_def =
 all_fields_of state_ty
 |> map build_module_state_rel_var
 |> list_mk_conj
 |> (fn tm => Define `module_state_rel hol_s ver_s = ^tm`);

 val fextv_vars =
 TypeBase.fields_of fext_ty
 |> filter (fn (f, _) => not (mem f abstract_fields))
 |> map build_fextv_var;

 (* This was needed for Silver at some point to hide fext lifting from theorems,
    would have otherwise not have been needed. *)
 val fextv_others =
 TypeBase.fields_of fext_ty
 |> map (fromMLstring o fst)
 |> build_fextv_others;

 (* TODO: Name... *)
 val fextv_rel_def =
 fextv_vars @ [fextv_others]
 |> list_mk_conj
 |> inst [ alpha |-> ``:error`` ]
 |> (fn tm => Define `fextv_rel fextv fext = ^tm`);

 val tstate = build_tstate fextv_rel_def state_rel_def is_state_rel_var_def module_state_rel_def abstract_fields comms fext_ty state_ty
in
 tstate
end;

(*
module_def = expected input format: name = mk_cirucit (procs seqs) (procs combs) init
abstract_fields = fields of fext only used for "abstract" modeling, i.e. never read or written to by circuit directly (used e.g. to model state machines outside of the circuit)
outputs = outputs of circuit
comms = variables that should be written to nonblockingly
*)
fun module2hardware tstate module_def abstract_fields outputs comms = let
 val (module, def) = module_def |> concl |> dest_eq
 val module_name = module |> dest_const |> fst

 fun new_module_definition name tm = let
  val name = concat $ module_name :: (if name = "" then ["_v"] else ["_v_", name])
  val def = new_definition(name ^ "_def", mk_icomb(mk_comb(equality, mk_var(name, alpha)), tm))
  val _ = computeLib.add_funs [def]
 in
  def
 end

 val theory = module |> dest_thy_const |> #Thy
 val state_ty = module |> dest_const |> snd |> dom_rng |> snd |> dom_rng |> snd |> dom_rng |> snd
 val fext_ty = module |> dest_const |> snd |> dom_rng |> fst |> dom_rng |> snd

 (* Build the Verilog module... *)

 val (_, [seqs, combs, init]) = strip_comb def
 val seqs = procs2hardware tstate theory seqs |> GEN_ALL
 val seqs_v_def = new_module_definition "seqs" (seqs |> concl |> strip_forall |> snd |> rand)
 val seqs = REWRITE_RULE [GSYM seqs_v_def] seqs

 val combs = procs2hardware tstate theory combs |> GEN_ALL
 val combs_v_def = new_module_definition "combs" (combs |> concl |> strip_forall |> snd |> rand)
 val combs = REWRITE_RULE [GSYM combs_v_def] combs

 val th = MATCH_MP Eval_lists_mrun (LIST_CONJ [seqs, combs, #module_rel_rel tstate, #rel_module_rel tstate])
 val precond = th |> concl |> strip_forall |> snd |> dest_imp |> fst |> EVAL_PROVE
 val th = MATCH_MP th precond

 val fextty_tm = TypeBase.fields_of fext_ty
                 |> filter (fn (f, _) => not (mem f abstract_fields))
                 |> map build_fextty
                 |> (fn l => listSyntax.mk_list (l, “:string # vertype”))

 val init_def = get_def theory init
 val (init, init_values) = init_def |> concl |> strip_forall |> snd |> dest_eq                                   
 val init_values = init_values |> dest_record_rec

 (* TODO: Must also handle let-variables... should write pass that finds them all *)
 (* Hack for now: *)
 val expected_oracle = “fbits : num -> bool”
 val decls_tm = map (build_decl outputs expected_oracle) init_values
                |> (fn l => listSyntax.mk_list (l, “:string # var_metadata”))
 val decls_def = new_module_definition "decls" decls_tm

 val precond = build_module_rel_init (#module_rel tstate) init (decls_def |> concl |> lhs)
 val th = MATCH_MP th precond

 val module_tm = TypeBase.mk_record (“:module”, [("fextty", fextty_tm),
                                                 ("decls", decls_def |> concl |> lhs),
                                                 ("ffs", seqs_v_def |> concl |> lhs),
                                                 ("combs", combs_v_def |> concl |> lhs)])
 val module_v_def = new_module_definition "" module_tm

 val th = MATCH_MP mk_circuit_to_mk_module (th |> SPEC_ALL |> UNDISCH_ALL |> GEN_ALL)
 val th = SPEC (module_v_def |> concl |> lhs) th
 val th = EVAL_MP th
 val th = th |> DISCH_ALL |> GEN_ALL
 val th = PURE_REWRITE_RULE [GSYM module_def] th
in
 th
end;

end
