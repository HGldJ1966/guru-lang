Include "rheaplet.g".

Define rheaplet_get_set : Forall(A:type)(I:rheaplet_id)(h:<rheaplet A I>)
                                (p1 p2:<alias I>)(a:A)(u:{ p1 != p2 }).
                            { (rheaplet_get p1 (rheaplet_set p2 h a)) = (rheaplet_get p1 h) } :=
  foralli(A:type)(I:rheaplet_id)(h:<rheaplet A I>)
         (p1 p2:<alias I>)(a:A)(u:{ p1 != p2 }).
    transs join (rheaplet_get p1 (rheaplet_set p2 h a)) (nth p1 (set_nth p2 h a)) 
           [set_nth_other A h p1 p2 a u]
           join (nth p1 h) (rheaplet_get p1 h)
    end.

Set "trust_hypjoins".  % the hypjoins below take about 8 seconds.

Define rheaplet_in_length : 
  Forall(A:type)(I:rheaplet_id)(h h':<rheaplet A I>)(a:A)(p:<alias I>)
        (u:{ (rheaplet_in h a) = (return_rheaplet_in h' p) }).
        { (lt p (length h')) = tt } :=
  foralli(A:type)(I:rheaplet_id)(h h':<rheaplet A I>)(a:A)(p:<alias I>)
         (u:{ (rheaplet_in h a) = (return_rheaplet_in h' p) }).
    abbrev P = trans symm u eval (rheaplet_in h a) in

    % this hypjoin takes much longer if we don't break it into two as done here.

    hypjoin (lt p (length h')) tt
      by inj (return_rheaplet_in ** *) P
         inj (return_rheaplet_in * **) P 
         [length_append A h (cons A a (nil A))]
         hypjoin (lt (length h) (plus (length h) (length (cons a nil)))) tt
          by [plusS (length A h) Z] [lt_Splus (length A h) Z] end
      end.

Unset "trust_hypjoins".

Define rheaplet_in_list_all : 
  Forall(A:type)(f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
        (I:rheaplet_id)(h h':<rheaplet A I>)(a:A)(p:<alias I>)
        (u1 : { (list_all f h) = tt })
        (u2 : { (f a) = tt })
        (u3 : { (rheaplet_in h a) = (return_rheaplet_in h' p) }).
     { (list_all f h') = tt } := 
  foralli(A:type)(f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
         (I:rheaplet_id)(h h':<rheaplet A I>)(a:A)(p:<alias I>)
         (u1 : { (list_all f h) = tt })
         (u2 : { (f a) = tt })
         (u3 : { (rheaplet_in h a) = (return_rheaplet_in h' p) }).
    transs cong (list_all f *) inj (return_rheaplet_in * **)
                                 trans symm u3 join (rheaplet_in h a) 
                                                    (return_rheaplet_in (append h (cons a nil)) (length h))
           [list_all_append A f ftot h (cons A a (nil A)) u1]
           hypjoin (list_all f (cons a nil)) tt by u2 end
    end.          

Define rheaplet_set_list_all : 
  Forall(A:type)(f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
        (I:rheaplet_id)(h:<rheaplet A I>)(a:A)(p:<alias I>)
        (u1 : { (list_all f h) = tt })
        (u2 : { (f a) = tt })
        (u3 : { (lt p (length h)) = tt }).
     { (list_all f (rheaplet_set p h a)) = tt } := 
  foralli(A:type)(f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
         (I:rheaplet_id)(h:<rheaplet A I>)(a:A)(p:<alias I>)
         (u1 : { (list_all f h) = tt })
         (u2 : { (f a) = tt })
         (u3 : { (lt p (length h)) = tt }).
  trans cong (list_all f *) join (rheaplet_set p h a) (set_nth p h a)
        [list_all_set_nth A p h a f ftot u3 u1 u2].


