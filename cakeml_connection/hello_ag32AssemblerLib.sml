structure hello_ag32AssemblerLib =
struct

open hardwarePreamble;

open hello_ag32ProofTheory;

(**
Extract machine code words from hello_init_memory_words_def
**)

fun words_to_file filename words =
 ``MAP word_to_hex_string ^words``
 |> EVAL |> concl |> rhs
 |> listSyntax.dest_list |> fst
 |> map (fn tm => stringSyntax.fromHOLstring tm ^ "\n")
 |> concat
 |> writeFile filename;

val (low_mem, zeroes_mem, high_mem) =
 case hello_init_memory_words_def |> concl |> rhs |> listSyntax.strip_append of
  h1 :: h2 :: h3 :: t => (listSyntax.mk_append (h1, h2), h3, listSyntax.list_mk_append t);

(** Low **)

val cmp = wordsLib.words_compset ();
val () = computeLib.extend_compset
    [computeLib.Extenders
      [ag32_targetLib.add_ag32_encode_compset],
     computeLib.Defs
      [hello_ag32CompileTheory.code_def
      ,hello_ag32CompileTheory.data_def]
    ] cmp;

val eval = computeLib.CBV_CONV cmp;

val hello_startup_code_eval =
 hello_startup_code_def
 |> CONV_RULE (RHS_CONV (RAND_CONV (RAND_CONV EVAL
                                    THENC
                                    listLib.MAP_CONV eval)
                         THENC
                         EVAL));

val low_mem_ground = low_mem |> (REWRITE_CONV [hello_startup_code_eval] THENC EVAL);
val low_mem_ground' = low_mem_ground |> concl |> rhs;

val () = words_to_file "low_mem_words.mem" low_mem_ground';

(** Middle **)

(* Number of words: *)
val zeroes_mem_len =
 zeroes_mem
 |> rator |> rand
 |> (REWRITE_CONV [heap_size_def, hello_startup_code_eval] THENC EVAL);

(** High **)

(* TODO: *)
computeLib.add_funs [ag32Theory.Encode_def, ag32Theory.enc_def, ag32Theory.ri2bits_def,

                     hello_ag32CompileTheory.data_def, hello_ag32CompileTheory.code_def,

                     bitstringTheory.v2w_def];

val hello_ag32_ffi_code_eval =
 ``MAP Encode hello_ag32_ffi_code`` |> EVAL;

val words_of_bytes_rw = Q.prove(
 `(words_of_bytes be [] = []:word32 list) /\
  (words_of_bytes be [x1] = word_of_bytes be 0w [x1] :: []:word32 list) /\
  (words_of_bytes be [x1;x2] = word_of_bytes be 0w [x1;x2] :: []:word32 list) /\
  (words_of_bytes be [x1;x2;x3] = word_of_bytes be 0w [x1;x2;x3] :: []:word32 list) /\
  (words_of_bytes be (x1::x2::x3::x4::xs) =
   word_of_bytes be 0w [x1;x2;x3;x4] :: words_of_bytes be xs:word32 list)`,
 simp [data_to_word_memoryProofTheory.words_of_bytes_def,miscTheory.bytes_in_word_def]);

val word_of_bytes_rw = Q.prove(
  `word_of_bytes F 0w [b1;b2;b3;b4] =
    (16777216w*w2w b4 + 65536w*w2w b3 + 256w*w2w b2 + w2w b1):word32`,
  fs [data_to_word_memoryProofTheory.word_of_bytes_def,LET_THM,
      wordSemTheory.set_byte_def,wordSemTheory.byte_index_def,wordSemTheory.word_slice_alt_def]
  \\ blastLib.BBLAST_TAC);

val word_add_n2w_4 = Q.prove(
 `n2w w1 + n2w w2 + n2w w3 + n2w w4 = n2w (w1 + w2 + w3 + w4)`,
 rw [word_add_n2w]);

local
val all_8bits_ints = Math.pow (2.0, 8.0) |> trunc |> flip (curry List.tabulate) I;

val ty8 = fcpSyntax.mk_int_numeric_type 8
val ty32 = fcpSyntax.mk_int_numeric_type 32

val w2w_all =
 all_8bits_ints
 |> map numSyntax.term_of_int
 |> map (fn n => wordsSyntax.mk_n2w (n, ty8))
 |> map (fn n => wordsSyntax.mk_w2w (n, ty32))

val mult_base =
 w2w_all
 |> map EVAL

val mults =
 [16777216, 65536, 256]
 |> map numSyntax.term_of_int
 |> map (fn n => wordsSyntax.mk_n2w (n, ty32));
in
val mult_all =
 w2w_all
 |> map (fn n => (map (fn mult => wordsSyntax.mk_word_mul (mult, n)) mults))
 |> flatten
 |> map EVAL
 |> (fn xs => mult_base @ xs)
 |> LIST_CONJ
end;

(* max_print_depth := 50 *)

(*
Testing:

val foo =
``(words_of_bytes F (TAKE 40000 code)):word32 list``
|> RAND_CONV EVAL
|> concl |> rhs;

val clock = start_time ();
foo
|> REWRITE_CONV [words_of_bytes_rw, word_of_bytes_rw, mult_all, word_add_n2w_4]
|> concl |> rhs
|> EVAL;
end_time clock;
*)

(* val clock = start_time (); *)
val words_of_bytes_code_eval =
 ``(words_of_bytes F code):word32 list``
 |> (REWRITE_CONV [hello_ag32CompileTheory.code_def,
                   words_of_bytes_rw,word_of_bytes_rw,mult_all,word_add_n2w_4]
     THENC EVAL);
(* end_time clock; *)

val high_mem_words =
 high_mem
 |> (REWRITE_CONV [hello_ag32_ffi_code_eval,words_of_bytes_code_eval] THENC EVAL)
 |> concl |> rhs;

val () = words_to_file "high_mem_words.mem" high_mem_words;

end
