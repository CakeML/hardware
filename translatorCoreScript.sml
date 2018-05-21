open preamble;

open bitstringSyntax boolSyntax combinSyntax numSyntax stringSyntax;
open arithmeticTheory bitstringTheory indexedListsTheory optionTheory wordsTheory wordsSyntax;

open dep_rewrite;
open Abbrev;

open wordsLib;

open verilogTheory verilogMetaTheory verilogSyntax;

val _ = new_theory "translatorCore";

(** Type predicates **)

val BOOL_def = Define `
  BOOL (b:bool) = \v. v = VBool b`;

val WORD_def = Define `
  WORD (w:'a word) = \v. v = w2ver w`;

(* Arrays are in reverse order as we only have packed arrays in "reverse order"
   in this formalization *)
val WORD_ARRAY_def = Define `
  WORD_ARRAY (a:'a word -> 'b word) v =
   case v of
       VBool _ => F
     | VArray vs => LENGTH vs = dimword(:'a) /\
                    !i. sum_revEL (w2n i) vs = INR (w2ver (a i))`;

(** Various lemmas **)

val WORD_ver2n = Q.store_thm("WORD_ver2n",
 `!w v. WORD w v ==> ver2n v = INR (w2n w)`,
 rw [WORD_def, ver2n_def, ver2v_def, w2ver_def, sum_mapM_VBool, sum_map_def, v2n_w2v]);

val _ = export_theory();
