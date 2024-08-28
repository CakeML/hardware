structure compileLib =
struct

open hardwarePreamble;

open fullCompilerTheory compileTheory;

open GreedyTechMapLib LECLib;

fun compile module_def = let
 val module = module_def |> concl |> lhs
 val prefix = module |> dest_const |> fst
  
 fun new_circuit_definition name tm = let
  val name = concat [prefix, "_", name]
  val def = new_definition(name ^ "_def", mk_icomb(mk_comb(equality, mk_var(name, alpha)), tm))
  val _ = computeLib.add_funs [def]
 in
  def
 end
  
 (** Compile **)
 val compile_tm = compile_def |> concl |> strip_forall |> snd |> lhs |> dest_comb |> fst
 val _ = print "EVAL compile..."
 val timer = Timer.startRealTimer ();
 val compile_result = mk_comb (compile_tm, module) |> EVAL
 val _ = timer |> Timer.checkRealTimer |> Time.toString |> (fn time => print ("DONE (" ^ time ^ ")\n"));

 (* TODO: Add error handling *)
 val circuit = compile_result |> concl |> rhs |> sumSyntax.dest_inr |> fst

 val (extenv, outs, regs, nl, nl_should_be_empty) = dest_Circuit circuit;
 
 val extenv_def = new_circuit_definition "extenv" extenv
 val outs_def = new_circuit_definition "outs" outs
 val regs_def = new_circuit_definition "regs" regs
 val nl_def = new_circuit_definition "nl" nl

 val circuit' = mk_Circuit(extenv_def |> concl |> lhs,
                           outs_def |> concl |> lhs,
                           regs_def |> concl |> lhs,
                           nl_def |> concl |> lhs,
                           nl_should_be_empty)
 val circuit_def = new_circuit_definition "circuit" circuit'

 (* A little more involved than expected since when combs nl is empty we do not want to
    replace ffs nl as well... *)
 val compile_result = compile_result
                    |> (CONV_RULE o RHS_CONV o RAND_CONV o RATOR_CONV)
                        (REWRITE_CONV (map SYM [extenv_def, outs_def, regs_def, nl_def]))
                    |> REWRITE_RULE [SYM circuit_def]
 
 (** Tech map **)
 val _ = print "Running technology mapping..."
 val timer = Timer.startRealTimer ();
 val tech_nl = greedy_tech_map circuit
 val _ = timer |> Timer.checkRealTimer |> Time.toString |> (fn time => print ("DONE (" ^ time ^ ")\n"));

 val tech_nl_def = new_circuit_definition "tech_nl" tech_nl
 (*val tech_circuit_def = new_circuit_definition "tech_circuit" circuit'*)

 (** LEC **)
 val _ = print "LECing..."
 val timer = Timer.startRealTimer ();
 val lec_result = lec extenv_def outs_def regs_def nl_def tech_nl_def
 val _ = timer |> Timer.checkRealTimer |> Time.toString |> (fn time => print ("DONE (" ^ time ^ ")\n"));

 val tech_circuit_def = new_circuit_definition "tech_circuit"
                                               (lec_result |> concl |> strip_forall |> snd |> dest_imp |> snd
                                                           |> lhs |> strip_comb |> snd |> el 3)
 val lec_result = REWRITE_RULE (map SYM [circuit_def, tech_circuit_def]) lec_result

 (** Glue everything together **)
 val compile_correct_inst = MATCH_MP compile_correct compile_result

 val th = MATCH_MP compile_glue_thm compile_correct_inst
 val th = MATCH_MP th lec_result
in
 (REWRITE_RULE [extenv_def, outs_def, regs_def, tech_nl_def] tech_circuit_def,
  th)
end

end
