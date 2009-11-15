
Include "../../../lib/nat.g".
Include "../../../lib/warray.g".
Include "../../../lib/warray-util.g".
Include "../../../lib/stdio.g".
Include "../../../lib/boxedword.g".

%Set "print_parsed".

%Set "debug_eta_expand".
%Set "debug_to_carraway".

Set "use_malloc".

%%hackery to get word equal to 2^20
Define word20 := (word_plus word8 (word_plus word8 (word_plus word2 word2))).
Define mysize := (word_set_bit word20 join (lt (to_nat word20) wordlen) tt word0).

Define fill_array: Fun(spec n:word)(#unique l:<warray boxedWord n>)(i:word)
  (u:{(lt (to_nat i) (to_nat n)) = tt}). #unique <warray boxedWord n> :=
  fun fill_array(spec n:word)(#unique l:<warray boxedWord n>)(i:word)
                (u:{(lt (to_nat i) (to_nat n)) = tt}) : #unique <warray boxedWord n>.
  match (eqword i word0) with
    ff => (fill_array n (warray_set boxedWord i (boxWord i) n l u) (word_minus i word1)
               [lt_trans (word_to_nat (word_minus i word1))
                         (word_to_nat i) (word_to_nat n)
                   [word_minus_shrink i] u])
  | tt => l
  end.

Define trusted assumed1 : { (le (to_nat word0) (to_nat (word_minus mysize word1))) = tt } := truei.

Define search : Fun(!#unique l:<warray boxedWord mysize>)(i:word)(b:bool). bool
  := fun search(!#unique l:<warray boxedWord mysize>)(i:word)(b:bool) : bool.
  let ret = (warray_binary_search boxedWord mysize (inspect_unique <warray boxedWord mysize> l) word0 (word_minus mysize word1) (boxWord i)
              boxedWord_comp trans cong (lt * (to_nat mysize)) join (to_nat word0) Z
                                [lt_word_set_bit word20 join (lt (to_nat word20) wordlen) tt word0]
              [word_minus_shrink mysize]
	      assumed1) in
  match (eqword i word0) with
    ff => (search l (word_minus i word1) (and ret b))
  | tt => (and ret b)
  end.

Define test :=
  let a = (mk_uholder word word0) in
  let arr = (warray_new boxedWord mysize (inspect boxedWord a)) in
  let arr' = (fill_array mysize arr (word_minus mysize word1)
                 [word_minus_shrink mysize]) in
  let ret = (search arr' (word_minus mysize word1) tt) in
  do
    (dec boxedWord a)
    (warray_free boxedWord mysize arr')
    match ret with
      ff => let s = "False" in
              (println_string stdio s)
    | tt => let s = "True" in
              (println_string stdio s)
    end
  end.

Compile test to "test_warray_g.c".
