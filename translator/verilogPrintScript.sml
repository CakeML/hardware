open hardwarePreamble;

open verilogTheory;

val _ = new_theory "verilogPrint";

val buop_print_def = Define `
 buop_print Not = "!"`;

val bbop_print_def = Define `
 (bbop_print And = "&&") /\
 (bbop_print Equal = "==") /\
 (bbop_print NotEqual = "!=") /\
 (bbop_print Or = "||")`;

val abop_print_def = Define `
 (abop_print BitwiseAnd = "&") /\
 (abop_print BitwiseOr = "|") /\
 (abop_print BitwiseXor = "^^")`;

val arith_print_def = Define `
 (arith_print Minus = "-") /\
 (arith_print Plus = "+") /\
 (arith_print Times = "*") /\
 (arith_print Mod = "%")`;

val type_print_idx_def = Define `
 type_print_idx i = "[" ++ toString (i - 1) ++ ":0]"`;

val type_print_def = Define `
 (type_print VBool_t = "logic") /\
 (type_print (VArray_t is) = "logic" ++ CONCAT (MAP type_print_idx is))`;

val var_type_print_def = Define `
 var_type_print xs = MAP (\(var, ty). type_print ty ++ " " ++ var) xs`;

val _ = export_theory ();
