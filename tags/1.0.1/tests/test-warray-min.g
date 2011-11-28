
Include "../lib/nat.g".
Include "../lib/warray.g".
Include "../lib/stdio.g".
Include "../lib/boxedword.g".

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

Define trusted word0_lt_mysize : { (lt (to_nat word0) (to_nat mysize)) = tt } := truei.

Define test :=
  let a = (mk_uholder word word0) in
  let arr = (warray_new boxedWord mysize (inspect boxedWord a)) in
  let arr' = (fill_array mysize arr (word_minus mysize word1)
                 [word_minus_shrink mysize]) in
  let ret = (warray_minElement boxedWord mysize word0 
              (inspect_unique <warray boxedWord mysize> arr') a 
               boxedWord_le word0_lt_mysize) in
  do
    (warray_free boxedWord mysize arr')
    match ret with
      mk_uholder _ retw =>
      match (eqword retw word0) with
        ff => let s = "False" in
                (println_string stdio s)
      | tt => let s = "True" in
                (println_string stdio s)
      end
    end
  end.

Compile test to "test-warray-min.c".
