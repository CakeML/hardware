structure ag32AssemblerLib =
struct

open hardwarePreamble;

(**
Extract machine code words from hello_init_memory_words_def
**)

(*open helloProofTheory helloCompileTheory;*)
open wordcountProofTheory wordcountCompileTheory;

val [startup_code, startup_code_padding,
     cline_arg_count, cline_args,
     stdin_pointer, stdin_length, stdin,
     output_buffer,
     ffi_code,
     heap_and_stack,
     ffi_jumps,
     cakeml_code,
     cakeml_data] =
 wordcount_init_memory_words_def |> SPEC_ALL |> concl |> rhs |> listSyntax.strip_append;
(* hello_init_memory_words_def |> SPEC_ALL |> concl |> rhs |> listSyntax.strip_append;*)

(** Various JSON infrastructure **)

fun list_toJSON l =
 String.concat ["[", String.concatWith ", " l, "]"];

fun HOLlist_toJSON l =
 ``MAP w2n ^l``
 |> EVAL |> concl |> rhs
 |> listSyntax.dest_list |> fst
 |> map (Arbnumcore.toString o dest_numeral)
 |> list_toJSON;

fun outputJSONfield fd key value =
 (TextIO.output (fd, "\"" ^ key ^ "\": ");
 TextIO.output (fd, value));

(** Startup **)

(*
val cmp = wordsLib.words_compset ();
val () = computeLib.extend_compset
    [computeLib.Extenders
      [ag32_targetLib.add_ag32_encode_compset],
     computeLib.Defs
      [code_def
      ,data_def
      ,config_def]
      ] cmp;

val eval = computeLib.CBV_CONV cmp;
*)

val LENGTH_code =
 ``LENGTH code`` |> (REWRITE_CONV [code_def] THENC EVAL);
val LENGTH_data =
 ``LENGTH data`` |> (REWRITE_CONV [data_def] THENC EVAL);
val LENGTH_conf =
 ``LENGTH (THE config.ffi_names)`` |> (REWRITE_CONV [config_def] THENC EVAL);

val startup_code_eval =
 wordcount_startup_code_def
 |> CONV_RULE (RHS_CONV (RAND_CONV (RAND_CONV EVAL
                                    THENC
                                    (REWRITE_CONV [LENGTH_code, LENGTH_data, LENGTH_conf])
                                    THENC
                                    listLib.MAP_CONV ag32_targetLib.ag32_encode_conv)
                         THENC
                         EVAL));

val startup_code_ground =
 startup_code |> (REWRITE_CONV [startup_code_eval] THENC EVAL);
val startup_code_padding_ground =
 startup_code_padding |> (REWRITE_CONV [startup_code_eval] THENC EVAL);

val full_startup_code =
 listSyntax.mk_append (startup_code_ground |> concl |> rhs,
                       startup_code_padding_ground |> concl |> rhs)
 |> EVAL |> concl |> rhs;

(** Command-line arguments **)

(* Sanity check *)
val _ = assert (equal 1) (cline_arg_count |> listSyntax.dest_list |> fst |> length);

(* More difficult to sanity check cline_args... *)

val cline_size_words = ``cline_size DIV 4`` |> EVAL |> concl |> rhs;

(** Stdin **)

(* Sanity check *)
val _ = assert (equal 1) (stdin_pointer |> listSyntax.dest_list |> fst |> length);
val _ = assert (equal 1) (stdin_length |> listSyntax.dest_list |> fst |> length);

val stdin_size_words = ``stdin_size DIV 4`` |> EVAL |> concl |> rhs;

(** Output buffer (for stdout/stderr) **)

val output_buffer_size_words =
 ``LENGTH ^output_buffer``
 |> ((REWRITE_CONV [rich_listTheory.LENGTH_REPLICATE]) THENC EVAL)
 |> concl |> rhs;

(** Heap + stack **)

val heap_and_stack_size_words =
 ``LENGTH ^heap_and_stack``
 |> ((REWRITE_CONV [rich_listTheory.LENGTH_REPLICATE]) THENC EVAL)
 |> concl |> rhs;

(** FFI **)

(* TODO: *)
computeLib.add_funs [ag32Theory.Encode_def,
                     ag32Theory.enc_def, ag32Theory.encShift_def,
                     ag32Theory.ri2bits_def,

                     (*data_def, code_def,*)

                     bitstringTheory.v2w_def];

val ffi_code_words =
 ffi_code |> EVAL;

val ffi_jumps_words =
 ffi_jumps |> (REWRITE_CONV [config_def] THENC EVAL);

(** cakeml code **)

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
val cakeml_code_eval =
 cakeml_code
 |> (REWRITE_CONV [code_def,
                   words_of_bytes_rw,word_of_bytes_rw,mult_all,word_add_n2w_4]
     THENC EVAL);
(* end_time clock; *)

val top_mem = (let
 val ffi_jumps_words = ffi_jumps_words |> concl |> rhs
 val cakeml_code_eval = cakeml_code_eval |> concl |> rhs
 val cakeml_data = cakeml_data |> (REWRITE_CONV [data_def] THENC EVAL) |> concl |> rhs
in
 ``^ffi_jumps_words ++ ^cakeml_code_eval ++ ^cakeml_data``
end) |> EVAL;

(** Write everything do file... *)

val fd = TextIO.openOut "prg.json"

val _ = TextIO.output (fd, "{\n");

(* startup_code, startup_code_padding *)

val _ = outputJSONfield fd "startup_code"
                        (full_startup_code |> HOLlist_toJSON);
val _ = TextIO.output (fd, ",\n");

(* cline_arg_count, cline_args *)

val _ = outputJSONfield fd "cline_args_size"
                        (cline_size_words |> dest_numeral |> Arbnumcore.toString);
val _ = TextIO.output (fd, ",\n");

(* stdin_pointer, stdin_length, stdin *)

val _ = outputJSONfield fd "stdin_size"
                        (stdin_size_words |> dest_numeral |> Arbnumcore.toString);
val _ = TextIO.output (fd, ",\n");

(* output_buffer *)

val _ = outputJSONfield fd "output_buffer_size"
                        (output_buffer_size_words |> dest_numeral |> Arbnumcore.toString);
val _ = TextIO.output (fd, ",\n");

(* ffi_code *)

val _ = outputJSONfield fd "ffi_code"
                        (ffi_code_words |> concl |> rhs |> HOLlist_toJSON);
val _ = TextIO.output (fd, ",\n");

(* heap_and_stack *)

val _ = outputJSONfield fd "heap_and_stack_size"
                        (heap_and_stack_size_words |> dest_numeral |> Arbnumcore.toString);
val _ = TextIO.output (fd, ",\n");

(* top_mem: ffi_jumps, cakeml_code, cakeml_data *)

val _ = outputJSONfield fd "top_mem"
                        (top_mem |> concl |> rhs |> HOLlist_toJSON);

(* close stream... *)

val _ = TextIO.output (fd, "}\n");
val _ = TextIO.closeOut fd;

end