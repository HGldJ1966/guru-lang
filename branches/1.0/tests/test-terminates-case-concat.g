Include  trusted "../lib/list.g".

%-
Define concat_concat_map1 :
-%


Define concat_concat_map_termcase
  : Forall(A B:type)(f:Fun(x:A).<list <list B>>)
	  (l:<list A>).
	  { (concat (concat (map1 f l))) = (concat (map1 fun(x).(concat (f x)) l)) } :=
  foralli(A B:type)(f:Fun(x:A).<list <list B>>).
  induction(l:<list A>) return { (concat (concat (map1 f l))) = (concat (map1 fun(x).(concat (f x)) l)) }
  with
    nil _ => 
	     hypjoin (concat (concat (map1 f l))) (concat (map1 fun(x).(concat (f x)) l))
                     by l_eq end
  | cons _ x l' => transs
	     hypjoin (concat (concat (map1 f l))) (concat (append (f x) (concat (map1 f l'))))
                     by l_eq end
	      terminates-case (f x) by u with		
		     y => 
                       transs
			[concat_append B terminates (f x) by u
                         (concat <list B> (map1 A <list <list B>> f l'))]
                         cong (append (concat (f x)) *) [l_IH l']
                         hypjoin (append (concat (f x)) (concat (map1 fun(x). (concat (f x)) l')))
                           (concat (map1 fun(x).(concat (f x)) l))
                         by l_eq end end
		   | abort => 
			transs cong (concat (append * (concat (map1 f l')))) u
                             join (concat (append abort ! (concat (map1 f l')))) 
                                  (append (concat abort !) (concat (map1 fun(x). (concat (f x)) l')))
                             cong (append (concat *) (concat (map1 fun(x). (concat (f x)) l'))) symm u
                             hypjoin (append (concat (f x)) (concat (map1 fun(x). (concat (f x)) l')))
                                     (concat (map1 fun(x).(concat (f x)) l))
                             by l_eq end
	
                        end                
		   end
	      end
  end.

%-
Define foldr_ext :
-%

Define foldr_ext_termcase : Forall(A B C : type)
                         	    (cookie1 cookie2:C)(f1 f2:Fun(cookie:C)(x:A)(y:B).B)
                         	    (feq:Forall(x:A)(y:B).
                                 {(f1 cookie1 x y) = (f2 cookie2 x y)})
                          	    (b:B)(l:<list A>).
                    { (foldr cookie1 f1 b l) = (foldr cookie2 f2 b l) } :=
  foralli(A B C : type)
         (cookie1 cookie2:C)(f1 f2:Fun(cookie:C)(x:A)(y:B).B)
         (feq:Forall(x:A)(y:B).
               {(f1 cookie1 x y) = (f2 cookie2 x y)})
         (b:B).
 induction(l:<list A>) return { (foldr cookie1 f1 b l) = (foldr cookie2 f2 b l) } 
  with
    nil _ => hypjoin (foldr cookie1 f1 b l) (foldr cookie2 f2 b l) by l_eq end
  | cons _ a l' => 
	          terminates-case (foldr A B C cookie1 f1 b l') by u with
			w => 
				 hypjoin (foldr cookie1 f1 b l) (foldr cookie2 f2 b l) 
                                 by l_eq [l_IH l'] 
				  [feq a terminates (foldr A B C cookie1 f1 b l') by u] end
		      | abort => 
		          transs 
				cong (foldr cookie1 f1 b *)  l_eq
				symm join (f1 cookie1 a (foldr cookie1 f1 b l')) (foldr cookie1 f1 b (cons a l')) 
				cong (f1 cookie1 a *) u 
				join (f1 cookie1 a abort !) abort !
				join abort !  (f2 cookie2 a abort ! )
				cong (f2 cookie2 a * ) symm u	
				hypjoin	 (f2 cookie2 a (foldr cookie1 f1 b l')) (f2 cookie2 a (foldr cookie2 f2 b l'))
					by [l_IH l'] end
				join (f2 cookie2 a (foldr cookie2 f2 b l')) (foldr cookie2 f2 b (cons a l')) 
				cong (foldr cookie2 f2 b * ) symm l_eq
			  
		          end
		    end
  end.

%-

Define map_ext : Forall(A B C:type)(f1 f2:Fun(c:C)(a:A).B)(cookie1 cookie2:C)
                       (fTot : Forall(a:A). Exists(b:B). { (f1 cookie1 a) = b })
                       (feq : Forall(a:A). {(f1 cookie1 a) = (f2 cookie2 a)})
                       (l:<list A>).
                  { (map cookie1 f1 l) = (map cookie2 f2 l) } :=
  foralli(A B C:type)(f1 f2:Fun(c:C)(a:A).B)(cookie1 cookie2:C)
         (fTot : Forall(a:A). Exists(b:B). { (f1 cookie1 a) = b })
         (feq : Forall(a:A). {(f1 cookie1 a) = (f2 cookie2 a)})
         (l:<list A>).
    transs join (map cookie1 f1 l) (foldr (mk_map_i f1 cookie1) map_h nil l)
           [foldr_ext A <list B> <map_i A B> (mk_map_i A B C f1 cookie1)
             (mk_map_i A B C f2 cookie2) (map_h A B) (map_h A B)
             foralli(x:A)(y:<list B>). 
               existsi (cons B terminates (f1 cookie1 x) by fTot y)
                 { (map_h (mk_map_i f1 cookie1) x y) = *}
                 join (map_h (mk_map_i f1 cookie1) x y) (cons (f1 cookie1 x) y)
             foralli(x:A)(y:<list B>). 
               hypjoin (map_h (mk_map_i f1 cookie1) x y) (map_h (mk_map_i f2 cookie2) x y) 
               by [feq x] end
             (nil B) l]
           join (foldr (mk_map_i f2 cookie2) map_h nil l) (map cookie2 f2 l)
    end.
-%

Define map_ext_termcase : Forall(A B C:type)(f1 f2:Fun(c:C)(a:A).B)(cookie1 cookie2:C)
				(feq : Forall(a:A). {(f1 cookie1 a) = (f2 cookie2 a)})
                       		(l:<list A>).
                  		{ (map cookie1 f1 l) = (map cookie2 f2 l) } :=
  foralli(A B C:type)(f1 f2:Fun(c:C)(a:A).B)(cookie1 cookie2:C)
	 (feq : Forall(a:A). {(f1 cookie1 a) = (f2 cookie2 a)})
         (l:<list A>).
truei.



























%-
Define map1_ext : Forall(A B:type)(f1 f2:Fun(a:A).B)
                        (fTot : Forall(a:A). Exists(b:B). { (f1 a) = b })
                        (feq : Forall(a:A). {(f1 a) = (f2 a)})
                        (l:<list A>).
                   { (map1 f1 l) = (map1 f2 l) } :=
   foralli(A B:type)(f1 f2:Fun(a:A).B)
          (fTot : Forall(a:A). Exists(b:B). { (f1 a) = b })
          (feq : Forall(a:A). {(f1 a) = (f2 a)})
          (l:<list A>).
   transs join (map1 f1 l) (map Z fun(u)(a).(f1 a) l)
          [map_ext A B nat fun(u:nat)(a:A).(f1 a) 
             fun(u:nat)(a:A).(f2 a) 
             Z Z
             foralli(x:A).existsi terminates (f1 x) by fTot
                            { (fun(u)(a).(f1 a) Z x) = *} 
                            join (fun(u)(a).(f1 a) Z x) (f1 x)
             foralli(x:A). hypjoin (fun(u)(a).(f1 a) Z x) (fun(u)(a).(f2 a) Z x)
                           by [feq x] end
             l]
         join (map Z fun(u)(a).(f2 a) l) (map1 f2 l)
   end.

-%


