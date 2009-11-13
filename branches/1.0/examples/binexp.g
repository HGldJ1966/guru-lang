%=============================================================================
% binexp.g
% by Duckki Oe
% The termination of binexp function proposed by Kiyung Ahn is proved.
%=============================================================================
Include trusted "../lib/nat.g".
Include trusted "../lib/list.g".

%=============================================================================
% definition of the function
% function g below is the binexp function
%=============================================================================

Define f :=
  fun f(n:nat)(l:<list nat>) : nat.
  match n with
    Z =>
      match l with
        nil _ => Z
      | cons _ x xs => (S (f x xs))
      end
  | S n' => (f n' (cons nat n' l))
  end.

Define g := fun(n:nat).(S (f n (nil nat))).


%=============================================================================
% some evauations
%=============================================================================

%-
Interpret (g Z).
Interpret (g (S Z)).
Interpret (g (S (S Z))).
Interpret (g (S (S (S Z)))).
-%

%=============================================================================
% proof of termination
%=============================================================================

% a helper function h
% h defines the second argument of the function f
% it also allows the same argument with multiset-ordering-based proof
% because it generates a set of numbers in an increasing order

Define h := 
  fun h(n:nat)(l:<list nat>) : <list nat>.
  match n with
    Z => l
  | S n' =>  (h n' (cons nat n' l))
  end.


% lem1 findes f in terms of h and simplifies f

Define lem1 :
  Forall(n:nat)(l:<list nat>).
    { (f n l) = (f Z (h n l)) }
  :=
  induction(n:nat) return Forall(l:<list nat>).{ (f n l) = (f Z (h n l)) }
  with
    Z =>
      foralli(l:<list nat>).
      hypjoin (f n l) (f Z (h n l)) by n_eq end
  | S n' =>
      foralli(l:<list nat>).
      % have: (f n' (cons n' l)) = (f Z (h n' (cons n' l)))
      abbrev p1 = [n_IH n' (cons nat n' l)] in
      hypjoin (f n l) (f Z (h n l)) by n_eq p1 end
  end.


% lem2 proves (f Z (h n l)) terminates
% assuming (f Z l) is terminating

Define lem2 :
  Forall(n:nat)(l:<list nat>)
        (z:nat)(u:{ (f Z l) = z }).
  Exists(y:nat). { (f Z (h n l)) = y }
  :=
  induction(n:nat) return
    Forall(l:<list nat>)
          (z:nat)
          (u:{ (f Z l) = z }).
    Exists(y:nat).
      { (f Z (h n l)) = y }
  with
    Z =>
      foralli(l:<list nat>)
             (z:nat)(u:{ (f Z l) = z }).
      existsi z { (f Z (h n l)) = * }
      hypjoin (f Z (h n l)) z by n_eq u end
  | S n' =>
      foralli(l:<list nat>)
             (z:nat)
             (u:{ (f Z l) = z }).

      % goal: (f Z (h n l)) =
      %       (f Z (h n' (cons n' l))) = ?
      
      % have: (f Z (h n' l)) = z'
      existse [n_IH n' l z u]
      foralli(z':nat)(z'_pf:{ (f Z (h n' l)) = z' }).
      
      % subgoal: (f Z (cons n' l)) = (S z')
      abbrev p1 = hypjoin (f Z (cons n' l)) (S z')
                    by [lem1 n' l] z'_pf end in

      % want: (f Z (h n' (cons n' l))) = z''
      existse [n_IH n' (cons nat n' l) (S z') p1]
      foralli(z'':nat)(z''_pf:{ (f Z (h n' (cons n' l))) = z'' }).

      existsi z'' { (f Z (h n l)) = * }
      hypjoin (f Z (h n l)) z'' by n_eq z''_pf end
  end
  .


% g only uses the base case of f, where l is nil.
% so, it does not depend on the totalness of f.

Define g_total :
  Forall(n:nat).
  Exists(m:nat).
    { (g n) = m }
  :=
  foralli(n:nat).
  existse [lem2 n (nil nat) Z join (f Z nil) Z]
  foralli(y:nat)(y_pf:{ (f Z (h n (nil))) = y }).
  existsi (S y) { (g n) = * }
  abbrev p = trans [lem1 n (nil nat)]
                   y_pf
  in
  trans join (g n) (S (f n nil))
        cong (S *) p
  .

Total g g_total.


% f also can be proven to be total.

Define f_total :
  Forall(n:nat)(l:<list nat>).
  Exists(m:nat).
    { (f n l) = m }
  :=
  induction(n:nat)(l:<list nat>) return Exists(m:nat).{ (f n l) = m }
  with
    nil _ =>
      existse [lem2 n (nil nat) Z join (f Z nil) Z]
      foralli(y:nat)(y_pf:{ (f Z (h n (nil))) = y }).
      existsi y { (f n l) = * }
      abbrev p = trans [lem1 n (nil nat)]
                       y_pf
      in
      trans cong (f n *) l_eq
            p
  | cons _ a l' =>
      % want p1: (f Z l) = y
      % have: (f a l') = m'
      existse [l_IH a l']
      foralli(m':nat)(m'_pf:{ (f a l') = m' }).
      abbrev p1 = hypjoin (f Z l) (S m') by l_eq m'_pf end in
      
      existse [lem2 n l (S m') p1]
      foralli(z:nat)(z_pf:{ (f Z (h n l)) = z }).
      
      existsi z { (f n l) = * }
      hypjoin (f n l) z by [lem1 n l] z_pf end
  end
  .

Total f f_total.

