open preamble;

open verilogTheory;

val _ = new_theory "verilogPrint";

val buop_print = Define `
 buop_print Not = "!"`;

val bbop_print = Define `
 (bbop_print And = "&&") /\
 (bbop_print Equal = "==") /\
 (bbop_print NotEqual = "!=") /\
 (bbop_print Or = "||")`;

val abop_print = Define `
 (abop_print BitwiseAnd = "&") /\
 (abop_print BitwiseOr = "|") /\
 (abop_print BitwiseXor = "^^")`;

val arith_print = Define `
 (arith_print Minus = "-") /\
 (arith_print Plus = "+") /\
 (arith_print Times = "*")`;

val _ = export_theory ();
