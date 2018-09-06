structure hello_ag32AssemblerLib =
struct

open hardwarePreamble;

open (*hello_ag32CompileTheory*) hello_ag32ProofTheory;

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
    (w2w b1 || w2w b2 << 8 || w2w b3 << 16 || w2w b4 << 24):word32`,
  fs [data_to_word_memoryProofTheory.word_of_bytes_def,LET_THM,
      wordSemTheory.set_byte_def,wordSemTheory.byte_index_def,wordSemTheory.word_slice_alt_def]
  \\ blastLib.BBLAST_TAC);

local
val all_8bits_ints = Math.pow (2.0, 8.0) |> trunc |> flip (curry List.tabulate) I;

val ty8 = fcpSyntax.mk_int_numeric_type 8
val ty32 = fcpSyntax.mk_int_numeric_type 32

val shift_base =
 all_8bits_ints
 |> map numSyntax.term_of_int
 |> map (fn n => wordsSyntax.mk_n2w (n, ty8))
 |> map (fn n => wordsSyntax.mk_w2w (n, ty32))

val shift0 =
 shift_base
 |> map EVAL

val shifts = map term_of_int [8, 16, 24]

val shift_others =
 shift_base
 |> map (fn n => (map (fn shift => wordsSyntax.mk_word_lsl (n, shift)) shifts))
 |> flatten
 |> map EVAL
in
val shifts_all = shift0 @ shift_others |> LIST_CONJ
end;

(* max_print_depth := 50 *)

val words_of_bytes_code_eval =
 ``(words_of_bytes F code):word32 list``
 |> (REWRITE_CONV [hello_ag32CompileTheory.code_def,words_of_bytes_rw,word_of_bytes_rw,shifts_all]
     THENC EVAL);

val high_mem_words =
 high_mem
 |> (REWRITE_CONV [hello_ag32_ffi_code_eval,words_of_bytes_code_eval] THENC EVAL)
 |> concl |> rhs;

val () = words_to_file "high_mem_words.mem" high_mem_words;

end
