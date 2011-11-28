%=============================================================================
% things that we can do with an ordering between items of a list
% - "lt" functions are assumed transitive
%=============================================================================

Include trusted "../lib/list.g".

Define list_min_h : Fun(A:type)
                       (lt:Fun(a b:A).bool)
                       (l:<list A>)
                       (curr:A).
                       A :=
  fun list_min_h(A:type)
                 (lt:Fun(a b:A).bool)
                 (l:<list A>)
                 (curr:A) : A.
  match l with
    nil _ => curr
  | cons _ a l' =>
      match (lt a curr) with
        ff => (list_min_h A lt l' curr)
      | tt => (list_min_h A lt l' a)
      end
  end.

Define list_min : Fun(A:type)
                     (lt:Fun(a b:A).bool)
                     (l:<list A>)
                     (u:{ (length A l) != Z }).
                     A :=
  fun(A:type)
     (lt:Fun(a b:A).bool)
     (l:<list A>)
     (u:{ (length A l) != Z }).
  match l with
    nil _ => abort A
  | cons _ a l' => (list_min_h A lt l a)
  end.

Define list_max : Fun(A:type)
                     (lt:Fun(a b:A).bool)
                     (l:<list A>)
                     (u:{ (length A l) != Z }).
                     A :=
  fun(A:type)
     (lt:Fun(a b:A).bool)
     (l:<list A>)
     (u:{ (length A l) != Z }).
  let gte = fun(a b:A).(not (lt a b)) in
  (list_min A gte l u).

Define sort : Fun(A:type)
                 (lt:Fun(a b:A).bool)
                 (l: <list A>). <list A> :=
  fun sort(A:type)
          (lt:Fun(a b:A).bool)
          (l: <list A>) : <list A>.
  match l with
    nil _ => l
  | cons _ x xs =>
      let lt_x = fun(y:A).(lt y x) in
      let gte_x = fun(y:A).(not (lt y x)) in
      (append A
        (sort A lt (filter A lt_x xs))
        (cons A x
          (sort A lt (filter A gte_x xs))))
  end.

Define monotone_h : Fun(A:type)
                       (lt:Fun(a b:A).bool)
                       (x:A)(xs: <list A>). bool :=
  fun monotone_h(A:type)
                (lt:Fun(a b:A).bool)
                (x:A)(xs: <list A>) : bool.
  match xs with
    nil _ => tt
  | cons _ x' xs' =>
      match (lt x x') with
        ff => ff
      | tt => (monotone_h A lt x' xs')
      end
  end.

Define monotone : Fun(A:type)
                     (lt:Fun(a b:A).bool)
                     (l: <list A>). bool :=
  fun(A:type)
     (lt:Fun(a b:A).bool)
     (l: <list A>).
  match l with
    nil _ => tt
  | cons _ x xs => (monotone_h A lt x xs)
  end.


%=============================================================================
% tests
%=============================================================================
%- 
Define a_list := (cons nat three (cons nat one (cons nat two (nil nat)))).
Define p := trans join (length nat a_list) three
                  clash three Z.
Define p2 := [lt_implies_not_zero Z (length nat a_list)
                                  join (lt Z (length nat a_list)) tt].

Interpret (list_min nat lt a_list p2).
Interpret (list_max nat lt a_list p2).

Interpret (sort nat lt a_list).

Interpret (monotone nat lt a_list).
Interpret (monotone nat lt (sort nat lt a_list)).
-%
