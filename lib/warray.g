%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% word-indexed arrays of refcounted data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include trusted "word.g".
Include trusted "unique.g".
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
   : Fun(spec A:type)(spec n:word)(! #unique l:<warray A n>)
        (i:word)
        (u:{(lt (to_nat i) (to_nat n)) = tt}). #<owned l> A := 
  fun(A:type)(spec n:word)(l:<warray A n>)(i:word)(u:{(lt (to_nat i) (to_nat n)) = tt}). 
    (vec_get A (to_nat wordlen n) l (to_nat wordlen i) u) <<END
#define gwarray_get(l,i) (((void **)l)[i])
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
  : Fun(A:type)			%% type of the warray
       (spec n:word)		%% length of the warray
       (#unique l:<warray A n>) %% the warray to search
       (first last:word)    	%% first and last index of the search
       (value:A)		%% value to search for
       (c:Fun(a b:A). comp)	%% comparator function
       (u:{(lt (to_nat first) (to_nat n)) = tt})
       (v:{(lt (to_nat last) (to_nat n)) = tt})
       . bool :=
  fun warray_binary_search(A:type)(spec n:word)(#unique l:<warray A n>)
     (first last:word)(value:A)
     (c:Fun(a b:A). comp)
     (u:{(lt (to_nat first) (to_nat n)) = tt})
     (v:{(lt (to_nat last) (to_nat n)) = tt}):bool.
    let mid = (word_plus first (word_div2 (word_minus last first))) by midu in
    abbrev midP = (word_to_nat (word_plus first (word_div2 (word_minus last first)))) in
    abbrev midProof = [lt_trans midP (word_to_nat last)	(word_to_nat n)
	                [ltle_trans midP
	      		  (word_to_nat (word_plus first (word_minus last first)))
			  (word_to_nat last)
                          [word_plus_shrink first (word_div2 (word_minus last first))
	      	            (word_minus last first)
		            [word_div2_shrink (word_minus last first)]]
	                  [word_plus_minus_shrink first last]]
	                v] in
    abbrev midMinusOneProof = [lt_trans (word_to_nat (word_minus (word_plus first (word_div2 (word_minus last first))) word1))
	     	 	        midP
		 		(word_to_nat n)
	         		[word_minus_shrink (word_plus first (word_div2 (word_minus last first)))]
	         		midProof] in
    match (ltword first last) with
      ff => ff %not found
    | tt =>
    match (c (warray_get A n l 
              (word_plus first (word_div2 (word_minus last first)))
	      midProof)
           value) with
      LT => (warray_binary_search A n l (word_plus (word_plus first (word_div2 (word_minus last first))) word1)
      	     last value c midMinusOneProof v)
    | EQ => tt %found
    | GT => (warray_binary_search A n l first
      	     (word_minus (word_plus first (word_div2 (word_minus last first))) word1)
	     value c u midMinusOneProof)
    end
    end.
