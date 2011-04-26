Include "uholder.g".
Include trusted "word.g".

%%our boxed word type to give ownership properties
Define boxedWord := <uholder word>.

Define boxWord : Fun(w:word) . boxedWord :=
  fun(w:word).
  (mk_uholder word w).
 
Define trusted boxWord_tot : Forall(w:word).Exists(bw:boxedWord).{(boxWord w) = bw} := truei.

Total boxWord boxWord_tot.

Define unboxWord : Fun(^ #owned bw:boxedWord) . word :=
  fun(^ #owned bw:boxedWord).
  match bw by x1 x2 with
    mk_uholder T w => cast w by symm inj <uholder *> x2 %mean trick that is required
  end.

Define unboxWordu : Fun(bw:boxedWord) . word :=
  fun(bw:boxedWord).
  match bw by x1 x2 with
    mk_uholder T w => cast w by symm inj <uholder *> x2 %mean trick that is required
  end.

Define trusted unboxWord_tot : Forall(bw:boxedWord).Exists(w:word).{(unboxWord bw) = w} := truei.

Total unboxWord unboxWord_tot.

Define trusted unboxWord_boxWord :
	Forall(b:boxedWord).{ (boxWord (unboxWord b)) = b } := truei.


Define boxedWord_comp : Fun(^ #owned bw1 bw2:boxedWord) . comp :=
  fun(^ #owned bw1 bw2:boxedWord).
  match bw1 with
    mk_uholder T1 w1 => match bw2 with
    	       	     	  mk_uholder T2 w2 => (word_comp w1 w2)
			end
  end.

Define boxedWord_le : Fun(bw1 bw2:boxedWord) . bool :=
  fun(bw1 bw2:boxedWord).
  match bw1 with
    mk_uholder T1 w1 => match bw2 with
    	       	     	  mk_uholder T2 w2 => (leword w1 w2)
			end
  end.

Define boxedWord_lt : Fun(bw1 bw2:boxedWord) . bool :=
  fun(bw1 bw2:boxedWord).
  match bw1 with
    mk_uholder T1 w1 => match bw2 with
    	       	     	  mk_uholder T2 w2 => (ltword w1 w2)
			end
  end.

Define boxedWord_eq : Fun(^ #owned bw1 bw2:boxedWord) . bool :=
  fun(^ #owned bw1 bw2:boxedWord).
  match bw1 with
    mk_uholder T1 w1 => match bw2 with
    	       	     	  mk_uholder T2 w2 => (eqword w1 w2)
			end
  end.

Define boxedWord_to_nat : Fun(bw:boxedWord).nat :=
 fun(bw:boxedWord).
 match bw by x1 x2 with
   mk_uholder T w => six 
 end.

Define nat_to_boxedWord : Fun(n:nat).boxedWord :=
 fun(n:nat).
   (boxWord word1).

Define trusted word_to_boxedWord_to_word :
  Forall(w:word).
    { (unboxWord (boxWord w)) = w }
  := truei.

Define trusted boxedWord_to_word_to_boxedWord :
  Forall(bw:boxedWord).
    { (boxWord (unboxWord bw)) = bw }
  := truei.

  
Define trusted boxedWord_to_nat_to_boxedWord :
  Forall(bw:boxedWord).
    { (nat_to_boxedWord (boxedWord_to_nat bw)) = bw }
  := truei.

Define trusted nat_to_boxedWord_to_nat :
  Forall(n:nat)
        (u:{ (le n (to_nat word_max)) = tt }).
    { (boxedWord_to_nat (nat_to_boxedWord n)) = n }
  := truei.
  
Define trusted boxedWord_minus_shrink : Forall(bw:boxedWord)
  (u:{(lt (to_nat (word_minus (unboxWord bw) word1)) (to_nat (unboxWord bw))) = tt}).
  {(lt (to_nat (unboxWord (boxWord (word_minus (unboxWord bw) word1)))) (to_nat (unboxWord bw))) = tt}
  := truei.

Define trusted boxedWord_minus_shrink2 : Forall(w:word)
  (u:{(lt (to_nat (word_minus w word1)) (to_nat w)) = tt}).
  {(lt (to_nat (unboxWord (boxWord (word_minus w word1)))) (to_nat w)) = tt}
  := truei.
