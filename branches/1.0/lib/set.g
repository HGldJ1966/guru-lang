Include trusted "list.g".

% l1 is a subset of l2
Define list_subset : Fun(A:type)(eqA : Fun(^ #owned a b: A).bool)(l1 l2:<list A>) . bool :=
  fun list_subset (A:type)(eqA:Fun(^ #owned a b:A).bool)(l1 l2:<list A>) : bool .
                     (list_all A fun(a:A).(member A a l2 eqA) l1).


Define list_seteq: Fun(A:type)(eqA : Fun(^ #owned a b: A).bool)(l1 l2 :<list A>). bool := 
   fun list_seteq (A:type)(eqA : Fun(^ #owned a b: A).bool)(l1 l2:<list A>) : bool.
                   (and (list_subset A eqA l1 l2)(list_subset A eqA l2 l1)).


Define list_intersect : Fun(A:type)(eqA : Fun(^ #owned a b: A).bool)(l1 l2:<list A>) . <list A> :=
  fun list_intersect (A:type)(eqA:Fun(^ #owned a b:A).bool)(l1 l2:<list A>) : <list A> .
                     (filter A fun(a:A).(member A a l2 eqA) l1).


Define append_helper : Forall(A:type)(a:A)(eqA : Fun(^ #owned a b: A).bool)(l'' l' : <list A>). {(append l' (cons a l'')) = (append (append l' (cons a nil)) l'')} :=
   foralli(A:type)(a:A)(eqA : Fun(^ #owned a b: A).bool)( l'' : <list A>).
     induction(l' : <list A>) return  {(append l' (cons a l'')) = (append (append l' (cons a nil)) l'')} with
         nil _ =>
                  trans cong (append * (cons a l'')) l'_eq
                  trans join (append nil (cons a l'')) (append (append nil (cons a nil)) l'')
                        cong (append (append * (cons a nil)) l'') symm l'_eq

       | cons _ b k =>
                       trans cong (append * (cons a l'')) l'_eq
                       trans join (append (cons b k) (cons a l'')) (append (cons b nil)(append k (cons a l'')))
                       trans cong (append (cons b nil) *) [l'_IH k]
                       trans join (append (cons b nil) (append (append k (cons a nil)) l''))
                                  (append (append (cons b k) (cons a nil)) l'')
                             cong (append (append * (cons a nil)) l'') symm l'_eq


       end.


Define list_setmember: Forall(A:type)(a:A)
                         (eqA:Fun(^ #owned x y: A).bool)
                         (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
                         (u:{(eqA a a)= tt})(l'' l':<list A>).
                         { (member a (append l' (cons a l'')) eqA) = tt } :=
   foralli(A:type)(a:A)(eqA:Fun(^ #owned x y: A).bool)
          (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
          (u: {(eqA a a) = tt})(l'':<list A>).
       induction(l':<list A>) return  { (member a (append l' (cons a l'')) eqA) = tt } with

        nil _ =>
               trans cong (member a (append * (cons a l'')) eqA) l'_eq
                     hypjoin (member a (append nil (cons a l'')) eqA) tt by u end

     | cons _ b k =>
                   trans cong (member a (append * (cons a l'')) eqA) l'_eq
                   trans join (member a (append (cons b k) (cons a l'')) eqA)
                        (member a (append (cons b nil) (append k (cons a l''))) eqA)
                   trans join (member a (append (cons b nil) (append k (cons a l''))) eqA)
                        (member a (append (cons b k) (cons a l'')) eqA)
                   trans join (member a (append (cons b k) (cons a l'')) eqA)
                        (member a (append (cons b nil) (append k (cons a l''))) eqA)
                   case terminates (eqA a b) by eqA_total by eqAp eqAt with
                         default bool => hypjoin (member a (append (cons b nil) (append k (cons a l''))) eqA)
                                         tt by eqAp [l'_IH k] end
                       end  
    end.


Define list_SubsetOfSelf : Forall(A:type)(eqA : Fun(^ #owned a b: A).bool)
                            (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
                            (u: Forall(a:A).{(eqA a a ) = tt})
                            (l : <list A>).
                            Forall(l': <list A>).{(list_subset A eqA l (append l' l)) = tt} :=
   foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
          (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
          (u: Forall(a:A). {(eqA a a ) = tt}).
        induction(l : <list A>) return Forall(l':<list A>).{(list_subset A eqA l (append l' l)) = tt} with
             nil _ => foralli(l': <list A>).
                        trans cong (list_subset eqA * (append l' *)) l_eq
                              join (list_subset eqA nil (append l' nil)) tt
           | cons _ a l'' =>  foralli(l': <list A>).
                                trans cong (list_subset eqA * (append l' *)) l_eq
                                trans hypjoin (list_subset eqA (cons a l'')(append l' (cons a l'')))
                                              (list_subset eqA l'' (append l' (cons a l'')))
                                              by [list_setmember A a eqA eqA_total [u a] l'' l' ] end
                                trans cong (list_subset eqA A l'' *) [append_helper A a eqA l'' l' ]
                                [l_IH l'' (append A l' (cons A a (nil A))) ]


           end.


Define member_trans_lemma: Forall(A:type)(a:A)(eqA :Fun(^ #owned a b: A).bool)
				 (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
				 (l1 l2: <list A>) (u: {(member A a l1 eqA) = tt})(v:{(list_subset eqA l1 l2) = tt}) 
				 (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
					{(member A a l2 eqA) = tt} :=
	foralli (A:type)(a:A)(eqA :Fun(^ #owned a b: A).bool)
		(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z }).
	   induction(l1: <list A>) return Forall(l2:<list A>)(u: {(member A a l1 eqA) = tt})
		    (v:{(list_subset eqA l1 l2) = tt})(eqA_to_equals:Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
			{(member A a l2 eqA) = tt} with
	  	nil _ => foralli (l2:<list A>)(u: {(member A a l1 eqA) = tt})
				 (v:{(list_subset eqA l1 l2) = tt})
				 (eqA_to_equals:Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
			contra
			trans symm u
			trans cong (member A a * eqA) l1_eq
			trans join (member A a nil eqA) ff
			clash ff tt
			{(member A a l2 eqA) = tt}
				
	    | cons _ b l1' => foralli (l2:<list A>)(u: {(member A a l1 eqA) = tt})
				      (v:{(list_subset eqA l1 l2) = tt})
				      (eqA_to_equals:Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).			
				case terminates (eqA a b) by eqA_total by eqAp eqAt with
				   ff => 						
					case terminates (member A b l2 eqA) by member_total by memp memt with
					   ff => contra
						 trans symm v
						 trans hypjoin (list_subset eqA l1 l2) ff by memp l1_eq end
						 clash ff tt
						 {(member A a l2 eqA) = tt}
					| tt => 
					 abbrev H = symm hypjoin tt (list_subset eqA l1' l2) by memp l1_eq u v end in
					 abbrev H2 = hypjoin (member A a l1' eqA) tt by eqAp u l1_eq end in
					 [l1_IH l1' l2 H2 H eqA_to_equals]
					 end
				| tt => 			
				    case terminates (member A b l2 eqA) by member_total by memp memt with
					ff => contra
					      trans symm v
					      trans hypjoin (list_subset eqA l1 l2) ff by memp l1_eq end
					      clash ff tt
					      {(member A a l2 eqA) = tt}
				      | tt => hypjoin (member A a l2 eqA) tt by memp eqAp [eqA_to_equals a b eqAp] end
									
				      end
				end
				
	  end.


Define list_transitivity : Forall(A:type)(eqA: Fun(a b: A).bool)
				 (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
				 (l1 l2 l3: <list A>)(u:{(list_subset eqA l1 l2) = tt})
				 (v:{(list_subset eqA l2 l3) = tt})(w:Forall(a:A).{(eqA a a) = tt})
				 (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
				 {(list_subset eqA l1 l3) = tt} :=
    foralli(A:type)(eqA: Fun(a b: A).bool)(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z }).
	induction(l1: <list A>) return Forall(l2 l3: <list A>)(u:{(list_subset eqA l1 l2) = tt})
					     (v:{(list_subset eqA l2 l3) = tt})(w:Forall(a:A).{(eqA a a) = tt})
					     (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
					     {(list_subset eqA l1 l3) = tt} with
	     nil _ => foralli(l2 l3: <list A>)(u:{(list_subset eqA l1 l2) = tt})(v:{(list_subset eqA l2 l3) = tt})
			(w:Forall(a:A).{(eqA a a) = tt})(eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
			hypjoin (list_subset eqA l1 l3) tt by l1_eq end
	   | cons _ a l1' =>  foralli(l2 l3: <list A>)(u:{(list_subset eqA l1 l2) = tt})
		                     (v:{(list_subset eqA l2 l3) = tt})(w:Forall(a:A).{(eqA a a) = tt})
                                     (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
			
			abbrev l1'_subset_l3 =
			abbrev U1 =
			abbrev U1' =		
			symm trans symm hypjoin (list_subset eqA l1' (cons a l1')) tt by 
			                        [list_SubsetOfSelf A eqA eqA_total w l1' (cons A a (nil A)) ] end
			     symm cong (list_subset eqA l1' * ) l1_eq in
			[l1_IH l1' l1 l2 U1' u w eqA_to_equals] in
			[l1_IH l1' l2 l3 U1 v w eqA_to_equals] in

			abbrev a_in_l3 = 
			abbrev a_in_l2 = 
			abbrev a_in_l1 = hypjoin (member A a l1 eqA) tt by [w a] l1_eq end in
			hypjoin (member A a l2 eqA) tt by 
				[member_trans_lemma A a eqA eqA_total l1 l2 a_in_l1 u eqA_to_equals] end in

			hypjoin (member A a l3 eqA) tt by 
				[member_trans_lemma A a eqA eqA_total l2 l3 a_in_l2 v eqA_to_equals] end  in

			hypjoin (list_subset eqA l1 l3) tt by l1_eq l1'_subset_l3 a_in_l3 end
			


			
			
	   end.

Define list_subset_total :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (l1 l2:<list A>).
  Exists(x:bool).
    { (list_subset A eqA l1 l2) = x } :=
  foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
		   (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z }).
	induction(l1: <list A>) return Forall(l2:<list A>).Exists(z:bool).{(list_subset eqA l1 l2) = z} with
	   nil _ => foralli(l2:<list A>).
		      existsi tt {(list_subset eqA l1 l2) = * } 
			  hypjoin (list_subset eqA l1 l2) tt by l1_eq end
	 | cons _ a t => foralli(l2:<list A>).
			   case terminates (member A a l2 eqA) by member_total by memp memt with
				  ff => existsi ff {(list_subset eqA l1 l2) = * }
					   hypjoin (list_subset eqA l1 l2) ff by l1_eq  memp end
				| tt => existsi terminates (list_subset A eqA t l2) by [l1_IH t]
							 {(list_subset eqA l1 l2) = *}
					   hypjoin (list_subset eqA l1 l2) (list_subset eqA t l2) by memp l1_eq end
					
					
				end
				
	 end.
                                              

Define list_seteq_total :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (l1 l2:<list A>).
  Exists(x:bool).
    { (list_seteq A eqA l1 l2) = x } :=
  foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
			         (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z }).
	    induction(l1 : <list A>) return Forall(l2 :<list A>). Exists(z:bool).{(list_seteq eqA l1 l2) = z} with
		 nil _ => foralli(l2: <list A>).
		            case l2 with
			      nil _ => existsi tt {(list_seteq eqA l1 l2) = * }
					  hypjoin (list_seteq eqA l1 l2) tt by l1_eq l2_eq end
			    | cons _ b w => existsi ff {(list_seteq eqA l1 l2) = *}
					  hypjoin (list_seteq eqA l1 l2) ff by l1_eq l2_eq end
			    end
	      |  cons _ a t => foralli(l2: <list A>).
		                 case l2 with
				     nil _ => existsi ff {(list_seteq eqA l1 l2) = *}
						 hypjoin (list_seteq eqA l1 l2) ff by l1_eq l2_eq end
				   | cons _ b' w' => case terminates (list_subset A eqA l1 l2) by 
								list_subset_total by lsp lst with
						ff => existsi ff {(list_seteq eqA l1 l2) = *}
								hypjoin (list_seteq eqA l1 l2) ff by l1_eq l2_eq lsp end
					      | tt => case terminates (list_subset A eqA l2 l1) by
						  list_subset_total by lsp2 lst2 with
						     ff => existsi ff {(list_seteq eqA l1 l2) = *}
							  hypjoin (list_seteq eqA l1 l2) ff by l1_eq l2_eq lsp lsp2 end
						   | tt => existsi tt {(list_seteq eqA l1 l2) = *}
							  hypjoin (list_seteq eqA l1 l2) tt by l1_eq l2_eq lsp lsp2 end
						   end
					     end
				   end
	      end.



Define equal_to_subset : Forall(A:type)(eqA : Fun(^ #owned a b: A).bool)
		(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(l1 l2 :<list A>)
		(u:{ (list_seteq eqA l1 l2) = tt}).
		{(list_subset eqA l1 l2) = tt} :=
	foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
		(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(l1 l2: <list A>) 
		(u:{ (list_seteq eqA l1 l2) = tt}).
		abbrev u' = hypjoin  (and (list_subset A eqA l1 l2)(list_subset A eqA l2 l1)) tt by u end in
	  [andtt_e1 terminates (list_subset A eqA l1 l2) by [list_subset_total A eqA eqA_total l1 l2]
		    terminates (list_subset A eqA l2 l1) by [list_subset_total A eqA eqA_total l2 l1] u']
	.

Define list_seteq_reflx : Forall(A:type)(eqA : Fun(^ #owned a b: A).bool)
	(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(u:Forall(a:A).{(eqA a a) = tt})(l: <list A>).
		{(list_seteq eqA l l) = tt} :=
   foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
	(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(u:Forall(a:A).{(eqA a a) = tt})(l: <list A>).
	
	
	abbrev u' = hypjoin (list_subset eqA l l) tt by [list_SubsetOfSelf A eqA eqA_total u l (nil A)] end in
	symm trans symm u'
	hypjoin (list_subset eqA l l) (list_seteq eqA l l ) by u' end
	
.

Define list_seteq_symm : Forall(A:type)(eqA : Fun(^ #owned a b: A).bool)
		(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(l1 l2 :<list A>)
		(u:{ (list_seteq eqA l1 l2) = tt}).
		{(list_seteq eqA l2 l1) = tt} :=
   foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
	  (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(l1 l2 :<list A>)
	  (u:{ (list_seteq eqA l1 l2) = tt}).
	
	abbrev A1 =	
	abbrev u' = hypjoin  (and (list_subset A eqA l1 l2)(list_subset A eqA l2 l1)) tt by u end in
	   [andtt_e1 terminates (list_subset A eqA l1 l2) by [list_subset_total A eqA eqA_total l1 l2]
		    terminates (list_subset A eqA l2 l1) by [list_subset_total A eqA eqA_total l2 l1 ] u'] in
	
	abbrev A2 = 
	abbrev v' = hypjoin (and (list_subset A eqA l1 l2)(list_subset A eqA l2 l1)) tt by u end in
	   [andtt_e2 terminates (list_subset A eqA l1 l2) by [list_subset_total A eqA eqA_total l1 l2] 
		    terminates (list_subset A eqA l2 l1) by [list_subset_total A eqA eqA_total l2 l1 ] v'] in
	
	symm trans symm u
	     trans hypjoin (list_seteq A eqA l1 l2) (list_subset A eqA l1 l2) by 
			   u [equal_to_subset A eqA eqA_total l1 l2 u] end
	     hypjoin (list_subset A eqA l1 l2)(list_seteq A eqA l2 l1) by A1 A2 end
	
.

Define list_seteq_trans: Forall(A:type)(eqA: Fun(a b: A).bool)
				 (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
				 (l1 l2 l3: <list A>)(u:{(list_seteq eqA l1 l2) = tt})
				 (v:{(list_seteq eqA l2 l3) = tt})(w:Forall(a:A).{(eqA a a) = tt})
				 (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
				 { (list_seteq eqA l1 l3) = tt}:=
	foralli(A:type)(eqA: Fun(a b: A).bool)
				 (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
				 (l1 l2 l3: <list A>)(u:{(list_seteq eqA l1 l2) = tt})
				 (v:{(list_seteq eqA l2 l3) = tt})(w:Forall(a:A).{(eqA a a) = tt})
				 (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
	   case terminates (list_subset A eqA l1 l3) by list_subset_total by lsp lst with
		  ff => contra
			
		   abbrev U1 = hypjoin (list_subset A eqA l1 l2) tt by [equal_to_subset A eqA eqA_total l1 l2 u] end in
		   abbrev U2 = hypjoin (list_subset A eqA l2 l3) tt by [equal_to_subset A eqA eqA_total l2 l3 v] end in	

			trans symm [list_transitivity A eqA eqA_total l1 l2 l3 U1 U2 w eqA_to_equals]
			trans hypjoin (list_subset A eqA l1 l3) ff by lsp end
			clash ff tt
			{ (list_seteq eqA l1 l3) = tt}
		| tt => case terminates (list_subset A eqA l3 l1) by list_subset_total by lsp2 lst2 with
			   ff => contra
				    abbrev v' = hypjoin (list_seteq eqA l3 l2) tt by 
					[list_seteq_symm A eqA eqA_total l2 l3 v ] end in 

				    abbrev V1 = hypjoin (list_subset A eqA l3 l2) tt by 
					[equal_to_subset A eqA eqA_total l3 l2 v'] end in

				   abbrev u' = hypjoin (list_seteq eqA l2 l1) tt by
				       [list_seteq_symm A eqA eqA_total l1 l2 u] end in					

				    abbrev V2 = hypjoin (list_subset A eqA l2 l1) tt by 
					[equal_to_subset A eqA eqA_total l2 l1 u'] end in
			
				    trans symm [list_transitivity A eqA eqA_total l3 l2 l1 V1 V2 w eqA_to_equals]

				    trans hypjoin  (list_subset eqA l3 l1) ff by lsp2 end
				clash ff tt
				{ (list_seteq eqA l1 l3) = tt}
				 
			 | tt => hypjoin (list_seteq A eqA l1 l3) tt by lsp lsp2 end
			 end
		end.
		

Define  list_subset_cons_tt_member :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (a:A)(l1 l2:<list A>)
        (u:{ (list_subset eqA (cons a l1) l2) = tt }).
    { (member a l2 eqA) = tt }
  :=
  foralli(A:type)
         (eqA:Fun(a b: A).bool)
         (a:A)(l1 l2:<list A>)
         (u:{ (list_subset eqA (cons a l1) l2) = tt }).
  abbrev f = fun(x:A).(member A x l2 eqA) in
  abbrev f_a = eval (list_subset eqA (cons a l1) l2) in
  abbrev f_a_tot = cinv (f a) trans symm f_a u in
  existse f_a_tot
  foralli(z:bool)(z_pf:{ (f a) = z }).
  case z with
    ff => 
      contra
        abbrev p1 = hypjoin (list_subset eqA (cons a l1) l2) ff
                      by z_pf z_eq end in
        trans symm u
        trans p1
              clash ff tt
        { (member a l2 eqA) = tt }
  | tt =>
      hypjoin (member a l2 eqA) tt by z_pf z_eq end
  end
  .

Define list_subset_cons_tt_head :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (a:A)(l1 l2:<list A>)
        (u:{ (list_subset eqA (cons a l1) l2) = tt }).
    { (list_subset eqA (cons a nil) l2) = tt }
  :=
  foralli(A:type)
         (eqA:Fun(a b: A).bool)
         (a:A)(l1 l2:<list A>)
         (u:{ (list_subset eqA (cons a l1) l2) = tt }).
  abbrev p1 = [list_subset_cons_tt_member A eqA a l1 l2 u] in
  hypjoin (list_subset eqA (cons a nil) l2) tt by p1 u end
  .

Define list_subset_cons_tt_tail :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (a:A)(l1 l2:<list A>)
        (u:{ (list_subset eqA (cons a l1) l2) = tt }).
    { (list_subset eqA l1 l2) = tt }
  :=
  foralli(A:type)
         (eqA:Fun(a b: A).bool)
         (a:A)(l1 l2:<list A>)
         (u:{ (list_subset eqA (cons a l1) l2) = tt }).
  abbrev p1 = [list_subset_cons_tt_member A eqA a l1 l2 u] in
  hypjoin (list_subset eqA l1 l2) tt by u p1 end
  .

Define list_subset_refl :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (eqA_refl:Forall(a:A).{ (eqA a a) = tt })
        (l:<list A>).
    { (list_subset eqA l l) = tt }
  :=
  foralli(A:type)
         (eqA:Fun(a b: A).bool)
         (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
         (eqA_refl:Forall(a:A).{ (eqA a a) = tt }).
  induction(l:<list A>) return { (list_subset eqA l l) = tt }
  with
    nil _ => hypjoin (list_subset eqA l l) tt by l_eq end
  | cons _ a l' =>
      abbrev f = fun(x:A).(member A x l eqA) in
      abbrev f' = fun(x:A).(member A x l' eqA) in
      
      % want: f' implies f
      abbrev p1 =
        foralli(y:A)(u:{ (f' y) = tt}).
        existse [eqA_total y a]
        foralli(z:bool)(z_pf:{ (eqA y a) = z }).
        hypjoin (f y) tt by l_eq u z_pf [or_tt z] end in
        
      % want: (list_all f l') = tt
      abbrev p2 = hypjoin (list_all A f' l') tt by [l_IH l'] end in
      abbrev p3 = [list_all_implies A f' f p1 l' p2] in
      
      % want: (list_all f l)
      hypjoin (list_subset eqA l l) tt by l_eq [eqA_refl a] p3 end
  end.

Define list_subset_tt_append :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (l1 l2 l3:<list A>)
        (u:{ (list_subset eqA l1 l2) = tt }).
    { (list_subset eqA l1 (append l2 l3)) = tt }
  :=
  foralli(A:type)
        (eqA:Fun(a b: A).bool)
        (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z }).
  induction(l1:<list A>) return
    Forall(l2 l3:<list A>)
          (u:{ (list_subset eqA l1 l2) = tt }).
      { (list_subset eqA l1 (append l2 l3)) = tt }
  with
    nil _ =>
      foralli(l2 l3:<list A>)
             (u:{ (list_subset eqA l1 l2) = tt }).
      hypjoin (list_subset eqA l1 (append l2 l3)) tt by l1_eq end
  | cons _ a l1' =>
      foralli(l2 l3:<list A>)
             (u:{ (list_subset eqA l1 l2) = tt }).
      existse [appendTot A l2 l3]
      foralli(z:<list A>)(z_pf:{(append l2 l3) = z}).
      
      abbrev f = fun(a:A).(member A a l2 eqA) in
      abbrev f' = fun(a:A).(member A a z eqA) in
      
      % f implies f'
      abbrev p' =
        foralli(a:A)(u':{ (f a) = tt }).
        abbrev p' = hypjoin (member a l2 eqA) tt by u' end in
        hypjoin (f' a) tt by [member_tt_append A eqA eqA_total a l2 l3 p'] z_pf end in
        
      % want: (list_all f l1) = tt
      abbrev p1 = hypjoin (list_all f l1) tt by u end in
      
      % want: (list_all f' l1) = tt
      abbrev p2 = [list_all_implies A f f' p' l1 p1] in
            
      hypjoin (list_subset A eqA l1 (append l2 l3)) tt by z_pf p2 end
  end
  .

Define list_subset_tt_cons :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (l1 l2:<list A>)
        (u:{ (list_subset eqA l1 l2) = tt })
        (a:A).
    { (list_subset eqA l1 (cons a l2)) = tt }
  :=
  foralli(A:type)
         (eqA:Fun(a b: A).bool)
         (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z }).
  induction(l1:<list A>) return
    Forall(l2:<list A>)(u:{ (list_subset eqA l1 l2) = tt })(a:A).
      { (list_subset eqA l1 (cons a l2)) = tt }
  with
    nil _ =>
      foralli(l2:<list A>)(u:{ (list_subset eqA l1 l2) = tt })(a:A).
      hypjoin (list_subset eqA l1 (cons a l2)) tt by l1_eq end
  | cons _ a' l1' =>
      foralli(l2:<list A>)(u:{ (list_subset eqA l1 l2) = tt })(a:A).

      % want: 
      abbrev u_h = hypjoin (list_subset eqA (cons a' l1') l2) tt by u l1_eq end in

      % want: (list_subset eqA l1' (cons a l2)) = tt
      % need: (list_subset eqA l1' l2) = tt
      abbrev u' = [list_subset_cons_tt_tail A eqA a' l1' l2 u_h] in
      abbrev p1 = [l1_IH l1' l2 u' a] in

      % want: (member eqA a' (cons a l2)) = tt
      % need: (member eqA a' l2) = tt
      abbrev p2 = [list_subset_cons_tt_member A eqA a' l1' l2 u_h] in
      abbrev p3 = [member_tt_cons A eqA eqA_total a' l2 a p2] in
      
      % goal: (list_subset eqA l1 (cons a l2)) = tt
      abbrev f = fun(x:A).(member A x (cons a l2) eqA) in
      hypjoin (list_subset eqA l1 (cons a l2))
              tt by l1_eq p3 p1 end
  end.

Define trusted list_subset_tt_append_front:
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (l1 l2:<list A>)
        (u:{ (list_subset eqA l1 l2) = tt })
        (l3:<list A>).
    { (list_subset eqA l1 (append l3 l2)) = tt }
  :=
  truei.
