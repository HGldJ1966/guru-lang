%=============================================================================
% two isomorphic data types with identical functions
% want:
%  theorems about one type are also applicable to another isomorphic type
%  (for example, list and ulist)
%  You may easily prove theorems about a type using lemmas proved for 
%  another isomorphic type.
%  It may be desirable there is a way to automate it.
% need:
%  1) transform functions that are total: A -> B, B -> A
%  2) a proof of isomorphism: A -> B -> A
%  3) identical functions: (f a) = (BtoA (f' (AtoB a)))
%=============================================================================

Include trusted "../lib/list.g".
Include trusted "../lib/ulist.g".

Define spec list_to_ulist :=
  fun list_to_ulist(A:type)(l:<list A>) : <ulist A>.
  match l with
    nil _ => (unil A)
  | cons _ a l' => (ucons A a (list_to_ulist A l'))
  end.

Define trusted list_to_ulist_total :
  Forall(A:type)(l:<list A>).
  Exists(z:<ulist A>). { (list_to_ulist l) = z } := truei.
  
Total list_to_ulist list_to_ulist_total.

Define spec ulist_to_list :=
  fun ulist_to_list(A:type)(l:<ulist A>) : <list A>.
  match l with
    unil _ => (nil A)
  | ucons _ a l' => (cons A a (ulist_to_list A l'))
  end.
  
Define ulist_to_list_total :=
  foralli(A:type).
  induction(l:<ulist A>) return Exists(z:<list A>).{ (ulist_to_list l) = z }
  with
    unil _ =>
      existsi (nil A) { (ulist_to_list l) = * }
      hypjoin (ulist_to_list l) nil by l_eq end
  | ucons _ a l' =>
      existse [l_IH l']
      foralli(y:<list A>)(y_pf:{ (ulist_to_list l') = y }).
      existsi (cons A a y) { (ulist_to_list l) = * }
      hypjoin (ulist_to_list l) (cons a y) by y_pf l_eq end
  end
  .

Total ulist_to_list ulist_to_list_total.

Define trusted ulist_to_list_to_ulist :
  Forall(A:type)(l:<ulist A>).
  { (list_to_ulist (ulist_to_list l)) = l } := truei.
  
Define trusted uappend_eq_append :
  Forall(A:type)(l1 l2:<ulist A>).
    { (uappend l1 l2) = (list_to_ulist (append (ulist_to_list l1) (ulist_to_list l2))) }
  :=
  truei
  .
  
% Using append_nil : Forall(A:type)(l:<list A>).{ (append l nil) = l }
Define uappend_nil : Forall(A:type)(l:<ulist A>).{ (uappend l unil) = l } :=
  foralli(A:type)(l:<ulist A>).
  % have: (uappend l unil) (append (ulist_to_list l) (ulist_to_list unil))
  trans [uappend_eq_append A l (unil A)]
  trans cong (list_to_ulist (append (ulist_to_list l) *))
             join (ulist_to_list unil) nil
  trans cong (list_to_ulist *)
             [append_nil A (ulist_to_list A l)]
        [ulist_to_list_to_ulist A l]
  .
