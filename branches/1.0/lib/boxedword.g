Include "uholder.g".
Include "word.g".

%%our boxed word type to give ownership properties
Define boxedWord := <uholder word>.

Define boxWord : Fun(w:word) . boxedWord :=
  fun(w:word).
  (mk_uholder word w).
 
Define trusted boxWord_tot : Forall(w:word).Exists(bw:boxedWord).{(boxWord w) = bw} := truei.

Total boxWord boxWord_tot.

Define unboxWord : Fun(bw:boxedWord) . word :=
  fun(bw:<uholder word>).
  match bw by x1 x2 with
    mk_uholder T w => cast w by symm inj <uholder *> x2 %mean trick that is required
  end.

Define trusted unboxWord_tot : Forall(bw:boxedWord).Exists(w:word).{(unboxWord bw) = w} := truei.

Total unboxWord unboxWord_tot.

Define boxedWord_comp : Fun(^ #owned bw1 bw2:boxedWord) . comp :=
  fun(^ #owned bw1 bw2:boxedWord).
  match bw1 with
    mk_uholder T1 w1 => match bw2 with
    	       	     	  mk_uholder T2 w2 => (word_comp w1 w2)
			end
  end.

Define trusted boxedWord_minus_shrink : Forall(bw:boxedWord)
  (u:{(lt (to_nat (word_minus (unboxWord bw) word1)) (to_nat (unboxWord bw))) = tt}).
  {(lt (to_nat (unboxWord (boxWord (word_minus (unboxWord bw) word1)))) (to_nat (unboxWord bw))) = tt}
  := truei.

Define trusted boxedWord_minus_shrink2 : Forall(w:word)
  (u:{(lt (to_nat (word_minus w word1)) (to_nat w)) = tt}).
  {(lt (to_nat (unboxWord (boxWord (word_minus w word1)))) (to_nat w)) = tt}
  := truei.
