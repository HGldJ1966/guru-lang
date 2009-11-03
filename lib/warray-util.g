Include trusted "warray.g".

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

Define trusted word_Si_eq_i2 
  : Forall(i i2 : word)(u: {i2 = (word_inc2 i)}).
       {(S (to_nat i) ) = (to_nat i2)} := truei.
  % Duckki: there is a similar lemma in word.g

Define warray_maxElement 
  : Fun (A:type)(n:word)(i:word)(l:<warray A n>)
       (max: A)(leA : Fun(x y:A).bool)
       (u:{(lt (to_nat i) (to_nat n)) = tt})
       . #<owned l> A :=
  fun warray_maxElement(A:type)(n:word)(i:word)(l:<warray A n>)
     (max: A)(leA : Fun(x y:A).bool)
     (u:{(lt (to_nat i) (to_nat n)) = tt})
     : #<owned l> A.
	let current = (warray_get A n l i u) in
		match (leA max current) by leAp leAt with
		    ff => let inc_i = (word_inc2 i) in
			     match (eqword inc_i n) by eqwp eqwt with
			      ff =>
				 abbrev h0 = hypjoin (eqbv inc_i n) ff by eqwp end in 
				 abbrev h1 = [to_nat_neq1 wordlen inc_i n h0] in
				 	
				 abbrev u1 = hypjoin (eqnat (S (to_nat i)) (to_nat n)) ff by 
					     h1 [word_Si_eq_i2 i inc_i inc_i_eq] end in 
				 abbrev u2 = hypjoin (lt (S (to_nat i)) (to_nat n)) tt by			
				     [x_lt_y_SxNEQy_Sx_lt_y (to_nat wordlen i) (to_nat wordlen n) u u1] end in 
				 abbrev u3 = hypjoin (lt (to_nat inc_i) (to_nat n)) tt by 
					     u2 [word_Si_eq_i2 i inc_i inc_i_eq] end in
	 			(warray_maxElement A n inc_i l max leA u3)
			   | tt => max
		            end
				
	          | tt => let inc_i' = (word_inc2 i) in
			   match  (eqword inc_i' n) by eqwp' eqwt' with
			     ff => 
				abbrev h0' = hypjoin (eqbv inc_i' n) ff by eqwp' end in
				abbrev h1' = [to_nat_neq1 wordlen inc_i' n h0'] in 		
			
	      			abbrev v1 = hypjoin (eqnat (S (to_nat i)) (to_nat n)) ff 
					    by h1' [word_Si_eq_i2 i inc_i' inc_i'_eq ] end in			
				abbrev v2 = hypjoin (lt (S (to_nat i)) (to_nat n)) tt by
				     [x_lt_y_SxNEQy_Sx_lt_y (to_nat wordlen i) (to_nat wordlen n) u v1] end in
				abbrev v3 = hypjoin (lt (to_nat inc_i') (to_nat n)) tt by 
					    v2 [word_Si_eq_i2 i inc_i' inc_i'_eq] end in 
				(warray_maxElement A n inc_i' l current leA v3)
			   | tt => current
			   end
		  end.

Define warray_minElement 
  : Fun (A:type)(n:word)(i:word)(l:<warray A n>)
       (min: A)(leA : Fun(x y:A).bool)
       (u:{(lt (to_nat i) (to_nat n)) = tt})
       . #<owned l> A :=
  fun warray_minElement(A:type)(n:word)(i:word)(l:<warray A n>)
     (min: A)(leA : Fun(x y:A).bool)
     (u:{(lt (to_nat i) (to_nat n)) = tt})
     : #<owned l> A.
        let current = (warray_get A n l i u) in
		match (leA min current) by leAp leAt with
		    ff => let inc_i = (word_inc2 i) in
			     match (eqword inc_i n) by eqwp eqwt with
			      ff => abbrev h0 = hypjoin (eqbv inc_i n) ff by eqwp end in 
				    abbrev h1 = [to_nat_neq1 wordlen inc_i n h0] in
				 	
				    abbrev u1 = hypjoin (eqnat (S (to_nat i)) (to_nat n)) ff by 
						h1 [word_Si_eq_i2 i inc_i inc_i_eq] end in 
				    abbrev u2 = hypjoin (lt (S (to_nat i)) (to_nat n)) tt by			
				     [x_lt_y_SxNEQy_Sx_lt_y (to_nat wordlen i) (to_nat wordlen n) u u1] end in 
				    abbrev u3 = hypjoin (lt (to_nat inc_i) (to_nat n)) tt by 
						u2 [word_Si_eq_i2 i inc_i inc_i_eq] end in
	 			    (warray_minElement A n inc_i l current leA u3)
				 
			   | tt => current
		            end
				
	          | tt => let inc_i' = (word_inc2 i) in
			   match  (eqword inc_i' n) by eqwp' eqwt' with
			     ff => 
				abbrev h0' = hypjoin (eqbv inc_i' n) ff by eqwp' end in
				abbrev h1' = [to_nat_neq1 wordlen inc_i' n h0'] in 		
			
	      			abbrev v1 = hypjoin (eqnat (S (to_nat i)) (to_nat n)) ff 
					    by h1' [word_Si_eq_i2 i inc_i' inc_i'_eq ] end in			
				abbrev v2 = hypjoin (lt (S (to_nat i)) (to_nat n)) tt by
				     [x_lt_y_SxNEQy_Sx_lt_y (to_nat wordlen i) (to_nat wordlen n) u v1] end in
				abbrev v3 = hypjoin (lt (to_nat inc_i') (to_nat n)) tt by 
					    v2 [word_Si_eq_i2 i inc_i' inc_i'_eq] end in 
				(warray_minElement A n inc_i' l min leA v3)
			   | tt => min
			   end
		  end.


Define warray_isElement 
  : Fun (A:type)(n:word)(i:word)(l:<warray A n>)
       (key:A)(eqA : Fun(^ #owned a b: A).bool)
       (u:{(lt (to_nat i) (to_nat n)) = tt})
       . bool :=
  fun warray_isElement(A:type)(n:word)(i:word)(l:<warray A n>)
     (key:A)(eqA : Fun(^ #owned a b: A).bool)
     (u:{(lt (to_nat i) (to_nat n)) = tt})
     : bool.
	let current = (warray_get A n l i u) in
	    match (eqA current key) by eqAp eqAt with
		ff => let inc_i = (word_inc2 i) in
			match (eqword inc_i n) by eqwp eqwt with
			   ff => abbrev h0 = hypjoin (eqbv inc_i n) ff by eqwp end in 
				 abbrev h1 = [to_nat_neq1 wordlen inc_i n h0] in
				 	
				 abbrev u1 = hypjoin (eqnat (S (to_nat i)) (to_nat n)) ff by 
				     h1 [word_Si_eq_i2 i inc_i inc_i_eq] end in 
				 abbrev u2 = hypjoin (lt (S (to_nat i)) (to_nat n)) tt by			
				     [x_lt_y_SxNEQy_Sx_lt_y (to_nat wordlen i) (to_nat wordlen n) u u1] end in 
				 abbrev u3 = hypjoin (lt (to_nat inc_i) (to_nat n)) tt by 
				      u2 [word_Si_eq_i2 i inc_i inc_i_eq] end in
	 			 (warray_isElement A n inc_i l key eqA u3)
			 | tt => ff 
			 end
	      | tt => tt
	      end.

Define warray_indexOf 
  : Fun (A:type)(n:word)(i:word)(l:<warray A n>)
       (key:A)(eqA : Fun(^ #owned a b: A).bool)
       (u:{(lt (to_nat i) (to_nat n)) = tt})
       . <option word> :=
  fun warray_indexOf(A:type)(n:word)(i:word)(l:<warray A n>)
     (key:A)(eqA : Fun(^ #owned a b: A).bool)
     (u:{(lt (to_nat i) (to_nat n)) = tt})
     : <option word>.
        let current = (warray_get A n l i u) in
	    match (eqA current key) by eqAp eqAt with
		ff => let inc_i = (word_inc2 i) in
			match (eqword inc_i n) by eqwp eqwt with
			     ff => abbrev h0 = hypjoin (eqbv inc_i n) ff by eqwp end in 
				   abbrev h1 = [to_nat_neq1 wordlen inc_i n h0] in
				 	
				   abbrev u1 = hypjoin (eqnat (S (to_nat i)) (to_nat n)) ff by 
					       h1 [word_Si_eq_i2 i inc_i inc_i_eq] end in 
				   abbrev u2 = hypjoin (lt (S (to_nat i)) (to_nat n)) tt by			
				     [x_lt_y_SxNEQy_Sx_lt_y (to_nat wordlen i) (to_nat wordlen n) u u1] end in 
				   abbrev u3 = hypjoin (lt (to_nat inc_i) (to_nat n)) tt by 
					       u2 [word_Si_eq_i2 i inc_i inc_i_eq] end in
	 			  (warray_indexOf A n inc_i l key eqA u3)

			   | tt => (nothing word)
		           end

	      | tt => (something word i)
	      end.


Define warray_lastIndexOf 
  : Fun (A:type)(n:word)(i:word)(l:<warray A n>)
       (key:A)(max:word)(eqA : Fun(^ #owned a b: A).bool)
       (u:{(lt (to_nat i) (to_nat n)) = tt})
       . word :=
  fun warray_lastIndexOf(A:type)(n:word)(i:word)(l:<warray A n>)
     (key:A)(max:word)(eqA : Fun(^ #owned a b: A).bool)
     (u:{(lt (to_nat i) (to_nat n)) = tt})
     : word.
	let current = (warray_get A n l i u) in
	    match (eqA current key) by eqAp eqAt with
		 ff => let inc_i = (word_inc2 i) in
			match (eqword inc_i n) by eqwp eqwt with
			   ff =>   abbrev h0 = hypjoin (eqbv inc_i n) ff by eqwp end in 
				   abbrev h1 = [to_nat_neq1 wordlen inc_i n h0] in
				 	
				   abbrev u1 = hypjoin (eqnat (S (to_nat i)) (to_nat n)) ff by 
					       h1 [word_Si_eq_i2 i inc_i inc_i_eq] end in 
				   abbrev u2 = hypjoin (lt (S (to_nat i)) (to_nat n)) tt by			
				     [x_lt_y_SxNEQy_Sx_lt_y (to_nat wordlen i) (to_nat wordlen n) u u1] end in 
				   abbrev u3 = hypjoin (lt (to_nat inc_i) (to_nat n)) tt by 
					       u2 [word_Si_eq_i2 i inc_i inc_i_eq] end in
	 			  (warray_lastIndexOf A n inc_i l key max eqA u3)
			 | tt => max
			 end

	       | tt => let inc_i = (word_inc2 i) in
			match (eqword inc_i n) by eqwp eqwt with
			   ff =>   abbrev h0 = hypjoin (eqbv inc_i n) ff by eqwp end in 
				   abbrev h1 = [to_nat_neq1 wordlen inc_i n h0] in
				 	
				   abbrev u1 = hypjoin (eqnat (S (to_nat i)) (to_nat n)) ff by 
					       h1 [word_Si_eq_i2 i inc_i inc_i_eq] end in 
				   abbrev u2 = hypjoin (lt (S (to_nat i)) (to_nat n)) tt by			
				     [x_lt_y_SxNEQy_Sx_lt_y (to_nat wordlen i) (to_nat wordlen n) u u1] end in 
				   abbrev u3 = hypjoin (lt (to_nat inc_i) (to_nat n)) tt by 
					       u2 [word_Si_eq_i2 i inc_i inc_i_eq] end in
	 			  (warray_lastIndexOf A n inc_i l key i eqA u3)
			 | tt => i
			 end
	       end.

