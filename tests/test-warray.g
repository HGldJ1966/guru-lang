Include "../lib/nat.g".
Include "../lib/warray.g".
Include "../lib/stdio.g".

%Set "debug_eta_expand".
%Set "debug_to_carraway".

Set "use_malloc".

%%hackery to get word equal to 2^20
Define word20 := (word_plus word8 (word_plus word8 (word_plus word2 word2))).
Define mysize := (word_set_bit word20 join (lt (to_nat word20) wordlen) tt word0).

Define fill_array: Fun(spec n:word)(#unique l:<warray word n>)(i:word)
  (u:{(lt (to_nat i) (to_nat n)) = tt}). #unique <warray word n> :=
  fun fill_array(spec n:word)(#unique l:<warray word n>)(i:word)
      		(u:{(lt (to_nat i) (to_nat n)) = tt}) : #unique <warray word n>.
  match (eqword i word0) with
    ff => (fill_array n (warray_set word i i n l u) (word_minus i word1)
       	  	      [lt_trans (word_to_nat (word_minus i word1))
		      		(word_to_nat i)
				(word_to_nat n)
				[word_minus_shrink i] u])
  | tt => l
  end.

Define test :=
  let a = word0 in
  let arr = (warray_new word mysize (inspect word a)) in
  let arr' = (fill_array mysize arr (word_minus mysize word1)
      	     		 [word_minus_shrink mysize]) in
  let val = word7 in
  let ret = (warray_binary_search word mysize 
      	     (inspect_unique <warray word mysize> arr') 
    	     word0 (word_minus mysize word1) val
	     word_comp
	     join (ltword word0 mysize) tt
	     [word_minus_shrink mysize]
	     join (ltword word0 (word_minus mysize word1)) tt) in
  do
    (dec nat a)
    (warray_free word mysize arr')
    match ret with
      ff => let s = "not found" in
      	      (println_string stdio s)
    | tt => let s = "found" in
      	      (println_string stdio s)
    end
  end.

Compile test to "test-warray.c".
