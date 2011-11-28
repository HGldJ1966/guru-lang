Include "list.g".
Include "word.g".
Include "owned.g".

%=============================================================================
% Compute the length of a list as a word.
%=============================================================================

Define length_word_h : Fun(A: type)(^#owned l : <list A>)(i:word).word :=
  fun length_word_h(A:type)(^#owned l : <list A>)(i:word) : word.
  match l with
    nil _ => i
  | cons _ _ l' =>
      (length_word_h A l' (word_inc2 i))
  end.

Define length_word : Fun(A: type)(^#owned l : <list A>).word :=
  fun(A:type)(^#owned l : <list A>).
  (length_word_h A l word0).

%=============================================================================
% lemmas about length_word
%=============================================================================

% Note that length_word is not total, since word_inc2 (called from
% length_word_h) can abort.

Define length_word_h_inc2 :
  Forall(A:type)(c : <list A>)
        (w : word).
    { (length_word_h c (word_inc2 w)) = (word_inc2 (length_word_h c w)) } :=
  foralli(A:type).
  induction(c : <list A>)
  return
  Forall(w : word).
    { (length_word_h c (word_inc2 w)) = (word_inc2 (length_word_h c w)) }
  with
    nil _ => 
    foralli(w : word).
      hypjoin (length_word_h c (word_inc2 w)) (word_inc2 (length_word_h c w))  by c_eq end
  | cons _ x c' => 
    foralli(w : word).
    terminates-case (word_inc2 w) by v with
      iw =>
      transs
        hypjoin (length_word_h c (word_inc2 w)) (length_word_h c' (word_inc2 (word_inc2 w))) by c_eq end
        [c_IH c' terminates (word_inc2 w) by v]
        cong (word_inc2 *) hypjoin (length_word_h c' (word_inc2 w)) (length_word_h c w) by c_eq end
      end
    | abort => 
        trans
          hypjoin (length_word_h c (word_inc2 w)) abort ! by c_eq v end
          symm transs
                 cong (word_inc2 *) hypjoin (length_word_h c w) (length_word_h c' (word_inc2 w)) by c_eq end
                 cong (word_inc2 (length_word_h c' *)) v
                 join (word_inc2 (length_word_h c' abort !)) abort !
               end
    end
  end.

Define length_word_cons :
  Forall(A:type)
        (c : <list A>)
        (x : A)
        (c' : <list A>)
        (c_eq : { c = (cons x c') }).
    { (length_word c) = (word_inc2 (length_word c')) } :=
  foralli(A:type)
         (c : <list A>)
         (x : A)
         (c' : <list A>)
         (c_eq : { c = (cons x c') }).
   transs
     hypjoin (length_word c) (length_word_h c' (word_inc2 word0)) by c_eq end
     [length_word_h_inc2 A c' word0]
     cong (word_inc2 *) join (length_word_h c' word0) (length_word c') 
   end.
        
Define length_word_implies_eq_length :
  Forall(A:type)(c:<list A>)
        (n:word)
        (u:{ (length_word c) = n }).
    { (to_nat n) = (length c) }
  := 
 foralli(A:type).
 induction(c:<list A>) return Forall(n:word)
        (u:{ (length_word c) = n }).
    { (to_nat n) = (length c) }
 with
   nil _ => 
   foralli(n:word)
          (u:{ (length_word c) = n }).
     hypjoin (to_nat n) (length c) by u c_eq end
 | cons _ x c' => 
   foralli(n:word)
          (u:{ (length_word c) = n }).
     abbrev n_eq = trans symm u [length_word_cons A c x c' c_eq] in
     terminates-case (length_word A c') by u with
       n' =>
       transs cong (to_nat *)
                 n_eq
              symm [word_inc2_word_to_nat terminates (length_word A c') by u 
                     terminates (word_inc2 (length_word A c')) by symm n_eq 
                     join (word_inc2 (length_word c')) (word_inc2 (length_word c'))]
              cong (S *)
                [c_IH c' terminates (length_word A c') by u 
                  join (length_word c') (length_word c')]
              hypjoin (S (length c')) (length c) by c_eq end
       end
     | abort => 
       contra
         transs n_eq
                cong (word_inc2 *) u
                join (word_inc2 abort !) abort !
                aclash n
         end
       { (to_nat n) = (length c) }
     end
 end.

Define length_word_append :
  Forall(A:type)(c1 c2 : <list A>)(w:word).
    { (length_word_h (append c1 c2) w) = (length_word_h c2 (length_word_h c1 w)) } := 
  foralli(A:type).
  induction(c1: <list A>) 
  return Forall(c2:<list A>)(w:word).
          { (length_word_h (append c1 c2) w) = (length_word_h c2 (length_word_h c1 w)) }
  with
    nil _ => 
    foralli(c2:<list A>)(w:word). 
      hypjoin (length_word_h (append c1 c2) w) (length_word_h c2 (length_word_h c1 w)) by c1_eq end
  | cons _ x c1' => 
    foralli(c2:<list A>)(w:word). 
     abbrev P = 
      transs hypjoin (length_word_h (append c1 c2) w) (length_word_h (append c1' c2) (word_inc2 w))
               by c1_eq end
             [length_word_h_inc2 A (append A c1' c2) w]
             cong (word_inc2 *) [c1_IH c1' c2 w]
      end in
     terminates-case (length_word_h A c1' w) by u with
       w' =>
        transs P
             symm [length_word_h_inc2 A c2 terminates (length_word_h A c1' w) by u]
             cong (length_word_h c2 *) 
               trans symm [length_word_h_inc2 A c1' w]
                     hypjoin (length_word_h c1' (word_inc2 w)) (length_word_h c1 w) by c1_eq end
        end
     | abort =>
        transs P
               cong (word_inc2 (length_word_h c2 *)) u
               join (word_inc2 (length_word_h c2 abort !)) (length_word_h c2 (word_inc2 abort !))
               cong (length_word_h c2 *)
                 transs cong (word_inc2 *) symm u
                        symm [length_word_h_inc2 A c1' w] 
                        hypjoin (length_word_h c1' (word_inc2 w)) (length_word_h c1 w) by c1_eq end
                 end
        end
     end
  end.

Define length_word_append_defined :
  Forall(A:type)(c1 c2 : <list A>)
        (wb : word)
        (wb_eq : { (length_word (append c1 c2)) = wb }).
   Exists(w1 : word). { (length_word c1) = w1 } := 
 foralli(A:type)(c1 c2 : <list A>)
        (wb : word)
        (wb_eq : { (length_word (append c1 c2)) = wb }).
 terminates-case (length_word A c1) by u with
   w1 => existsi w1 { (length_word c1) = * } u
 | abort => 
   contra 
     transs symm wb_eq
            join (length_word (append c1 c2)) (length_word_h (append c1 c2) 0x00000000)
            [length_word_append A c1 c2 0x00000000]
            cong (length_word_h c2 *)
                trans join (length_word_h c1 0x00000000) (length_word c1)
                      u
            join (length_word_h c2 abort !) abort !
            aclash wb
     end
   Exists(w1 : word). { (length_word c1) = w1 }
 end.

Define length_word_cons_end :
  Forall(A:type)
        (x : A)
        (c : <list A>). 
      { (length_word (append c (cons x nil))) = (word_inc2 (length_word c)) } :=
  foralli(A:type)(x:A).
  induction(c:<list A>) 
  return { (length_word (append c (cons x nil))) = (word_inc2 (length_word c)) } with
    nil => hypjoin (length_word (append c (cons x nil))) (word_inc2 (length_word c)) by c_eq end
  | cons _ x' c' => 
      transs
        hypjoin (length_word (append c (cons x nil))) (length_word_h (append c' (cons x nil)) (word_inc2 word0)) by c_eq end
        [length_word_h_inc2 A (append A c' (cons A x (nil A))) word0]
        cong (word_inc2 *) 
          transs join (length_word_h (append c' (cons x nil)) word0) (length_word (append c' (cons x nil)))
                 [c_IH c']
                 cong (word_inc2 *) join (length_word c') (length_word_h c' word0)
                 symm [length_word_h_inc2 A c' word0]
                 hypjoin (length_word_h c' (word_inc2 word0)) (length_word c) by c_eq end
          end
      end 
  end. 

