Include "../lib/plus.g".

%-

Refining a proof a step at a time:

Step 1
 
Classify
induction(n:nat) 
  return Forall(m : nat). { (plus n (S m)) = (S (plus n m))}
with
  Z => truei
| S n' => truei
end.
-%

%- 

Step 2

Classify
induction(n:nat) 
  return Forall(m : nat). { (plus n (S m)) = (S (plus n m))}
with
  Z => 
  foralli(m:nat).
  trans cong (plus * (S m)) n_eq
       trans join (plus Z (S m)) (S (plus Z m))
             cong (S (plus * m)) symm n_eq
| S n' => truei
end.
-%

% last step: this one checks.

Classify
induction(n:nat) 
  return Forall(m : nat). { (plus n (S m)) = (S (plus n m))}
with
  Z => 
  foralli(m:nat).
  trans cong (plus * (S m)) n_eq
       trans join (plus Z (S m)) (S (plus Z m))
             cong (S (plus * m)) symm n_eq
| S n' => 
  foralli(m : nat).
  trans cong (plus * (S m)) n_eq
  trans join (plus (S n') (S m)) (S (plus n' (S m)))
  trans cong (S *) [n_IH n' m]
  trans join (S (S (plus n' m))) (S (plus (S n') m))
        cong (S (plus * m)) symm n_eq
end.