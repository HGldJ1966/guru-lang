%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% word-indexed arrays of refcounted data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include trusted "word.g".
Include trusted "unique_owned.g".
Include trusted "comparator.g".

%Set "print_parsed".

Define primitive type_family_abbrev warray := fun(A:type)(n:word).<vec A (to_nat wordlen n)> <<END
#define gdelete_warray(x)
END.

Define primitive warray_new
 : Fun(spec A:type)(n:word)(^ #owned a:A).#unique <warray A n> := 
  fun(A:type)(n:word)(a:A). (mkvec A a (to_nat wordlen n)) <<END
void *gwarray_new(int n, void *a) {
  void **h = (void **)guru_malloc(sizeof(void *)*128);
  // fprintf(stdout,"gmk_warray(%x).\n", h);
  int c;
  for (c = 0; c < n; c++)
    h[c] = ginc(a); 
  return h;
}
END.

Define primitive warray_get
   : Fun(spec A:type)(spec n:word)(! #unique_owned l:<warray A n>)
        (i:word)
        (u:{(lt (to_nat i) (to_nat n)) = tt}). #<owned l> A := 
  fun(A:type)(spec n:word)(l:<warray A n>)(i:word)(u:{(lt (to_nat i) (to_nat n)) = tt}). 
    (vec_get A (to_nat wordlen n) l (to_nat wordlen i) u) <<END
inline void* gwarray_get(void **l, int i) { return l[i]; }
END.

Define primitive warray_set 
  : Fun(A:type)(i:word)(a:A)(spec n:word)(#unique l:<warray A n>)
       (u:{(lt (to_nat i) (to_nat n)) = tt}). #unique <warray A n> :=
  fun(A:type)(i:word)(a:A)(spec n:word)(l:<warray A n>)(u:{(lt (to_nat i) (to_nat n)) = tt}).
   (vec_update A (to_nat wordlen n) l (to_nat wordlen i) a u) <<END
void *gwarray_set(int A, int c, void *d, void *l) {
  gdec(A,((void **)l)[c]);
  ((void **)l)[c] = d;
  return l;
}
END.

Define primitive warray_free : Fun(A:type)(n:word)(^ #unique l:<warray A n>).void :=
  fun(A:type)(n:word)(l:<warray A n>).voidi <<END
void gwarray_free(int A, int n, void *l) {
  int c;
  // fprintf(stdout,"gwarray_free(%x).\n", l);
  for (c = 0; c < n; c++) 
    gdec(A,((void **)l)[c]);
  carraway_free(l);
}
END.

Define warray_binary_search
  : Fun(A:type)                 %% type of the warray
       (spec n:word)            %% length of the warray
       (^ #unique_owned l:<warray A n>) %% the warray to search
       (first last:word)        %% first and last index of the search
       (value:A)                %% value to search for
       (c:Fun(^ #owned a b:A). comp)    %% comparator function
       (u:{(lt (to_nat first) (to_nat n)) = tt})
       (v:{(lt (to_nat last) (to_nat n)) = tt})
       (w:{(le (to_nat first) (to_nat last)) = tt})
       . bool :=
  fun warray_binary_search(A:type)(spec n:word)(^ #unique_owned l:<warray A n>)
     (first last:word)(value:A)
     (c:Fun(^ #owned a b:A). comp)
     (u:{(lt (to_nat first) (to_nat n)) = tt})
     (v:{(lt (to_nat last) (to_nat n)) = tt})
     (w:{(le (to_nat first) (to_nat last)) = tt}):bool.
    let mid = (word_plus first (word_div2 (word_minus last first))) by midu in
    abbrev midP = (word_to_nat (word_plus first (word_div2 (word_minus last first)))) in
    abbrev midProof = 
    	   trans cong (lt (to_nat *) (to_nat n)) midu
                 [lt_trans midP (word_to_nat last) (word_to_nat n)
                           [ltle_trans midP
                         	       (word_to_nat (word_plus first (word_minus last first)))
                          	       (word_to_nat last)
                          	       [word_plus_shrink first (word_div2 (word_minus last first))
                            			  	 (word_minus last first)
                            				 [word_div2_shrink (word_minus last first)]]
                          	       [word_plus_minus_shrink first last]]
                           v] in
    abbrev midMinusOneProof = [lt_trans (word_to_nat (word_minus mid word1)) midP (word_to_nat n)
                                	trans cong (lt (to_nat (word_minus mid word1)) (to_nat *)) symm midu 
				      	      [word_minus_shrink mid]
                                	trans cong (lt (to_nat *) (to_nat n)) symm midu midProof] in
    match (c (warray_get A n l mid midProof) (inspect A value)) with
      LT => match (leword (word_plus mid word1) last) by ltu ign with
              ff => do (consume_unique_owned <warray A n> l)
                       (dec A value)
                       ff %not found
                    end
            | tt => 
            abbrev ltuP = trans join (le (word_to_nat (word_plus mid word1)) (word_to_nat last)) 
		                     (leword (word_plus mid word1) last)
                                ltu in

             (warray_binary_search A n l (word_plus mid word1)
                     last value c [lelt_trans (word_to_nat (word_plus mid word1)) 
		     	  	  	      (word_to_nat last) (word_to_nat n)
                                   ltuP v]
                     v ltuP)
            end
    | EQ => do (consume_unique_owned <warray A n> l)
               (dec A value)
               tt %found
            end
    | GT => match (leword first (word_minus mid word1)) by gtu ign with
              ff => do (consume_unique_owned <warray A n> l)
                       (dec A value)
                       ff %not found
                    end
            | tt => (warray_binary_search A n l first (word_minus mid word1)
                     value c u midMinusOneProof 
		     trans join (le (word_to_nat first) (word_to_nat (word_minus mid word1)))
		     	   	(leword first (word_minus mid word1)) gtu)
            end
    end.
