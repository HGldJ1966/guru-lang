Include "rheaplet.g".

Define rheaplet_set_get : Forall(A:type)(I:rheaplet_id)(h:<rheaplet A I>)
                                (p1 p2:<alias I>)(a:A)(u:{ p1 != p2 }).
                            { (rheaplet_get p1 (rheaplet_set p2 h a)) = (rheaplet_get p1 h) } :=
  foralli(A:type)(I:rheaplet_id)(h:<rheaplet A I>)
         (p1 p2:<alias I>)(a:A)(u:{ p1 != p2 }).
    transs join (rheaplet_get p1 (rheaplet_set p2 h a)) (nth p1 (set_nth p2 h a)) 
           [set_nth_other A h p1 p2 a u]
           join (nth p1 h) (rheaplet_get p1 h)
    end.

Define trusted rheaplet_in_get : Forall(A:type)(I:rheaplet_id)(h:<rheaplet A I>)
                                (p:<alias I>)(a:A)
                                (u:{ (rheaplet_in h a) = (return_rheaplet_in h' p) }).
                            { (rheaplet_get p h') = a } :=
  foralli(A:type)(I:rheaplet_id)(h:<rheaplet A I>)
         (p:<alias I>)(a:A)
         (u:{ (rheaplet_in h a) = (return_rheaplet_in h' p) }).
    truei.

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

Define rheaplet_in_length2 :
  Forall(A:type)(I:rheaplet_id)(h h':<rheaplet A I>)(a:A)(p:<alias I>)
        (u : { (rheaplet_in h a) = (return_rheaplet_in h' p) }).
    { (length h') = (S (length h)) } :=
  foralli(A:type)(I:rheaplet_id)(h h':<rheaplet A I>)(a:A)(p:<alias I>)
         (u : { (rheaplet_in h a) = (return_rheaplet_in h' p) }).
    transs cong (length *)
             inj (return_rheaplet_in * **)
             trans symm u
                   join (rheaplet_in h a) 
                        (return_rheaplet_in (append h (cons a nil)) (length h)) 
           [length_append A h (cons A a (nil A))]
           hypjoin (plus (length h) (length (cons a nil)))
                   (S (length h))
           by [plusS (length A h) Z] [plusZ (length A h)] end
    end.

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
  Forall(A:type)(f:Fun(a:A).bool)
        (I:rheaplet_id)(h:<rheaplet A I>)(a:A)(p:<alias I>)
        (u1 : { (list_all f h) = tt })
        (u2 : { (f a) = tt })
        (u3 : { (lt p (length h)) = tt }).
     { (list_all f (rheaplet_set p h a)) = tt } := 
  foralli(A:type)(f:Fun(a:A).bool)
         (I:rheaplet_id)(h:<rheaplet A I>)(a:A)(p:<alias I>)
         (u1 : { (list_all f h) = tt })
         (u2 : { (f a) = tt })
         (u3 : { (lt p (length h)) = tt }).
  trans cong (list_all f *) join (rheaplet_set p h a) (set_nth p h a)
        [list_all_set_nth A p h a f u3 u1 u2].

Define rheaplet_set_length : 
  Forall(A:type)(I:rheaplet_id)(h:<rheaplet A I>)(a:A)(p:<alias I>)
        (u:{(lt p (length h)) = tt }).
     { (length (rheaplet_set p h a)) = (length h) } :=
  foralli(A:type)(I:rheaplet_id)(h:<rheaplet A I>)(a:A)(p:<alias I>)
         (u:{(lt p (length h)) = tt }).
    trans cong (length *)
            join (rheaplet_set p h a)
                 (set_nth p h a)
          [set_nth_length A p h a u].
  
