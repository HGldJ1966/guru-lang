%- Problem 1 -%

%- P gives the predecessor of a non-zero nat.
   minus substracts nats.
   mult multiplies nats.
   pow exponentiates nats.
   div2 divides a nat by 2.
-%

%- Problem 2 -%

Include "../guru-lang/lib/plus.g".

Define plus' :=
  fun plus'(x y:nat):nat. 
    match y with
      Z => x
    | S y' => (S (plus' x y'))
    end.

Interpret (plus' (S (S Z)) (S (S (S Z)))).

%- Problem 3 -%

Inductive day : type :=
  sunday : day
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day.

Define next_day := 
  fun(d:day).
    match d with
      sunday => monday
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => saturday
    | saturday => sunday
    end.

Interpret (next_day saturday).

%- Problem 4 -%

Define nth_day :=
  fun nth_day(d:day)(n:nat):day.
    match n with
      Z => d
    | S n' => (next_day (nth_day d n'))
    end.

Interpret (nth_day monday (S (S Z))).

%- Problem 5 -%

%- 

0 * m = 0
(1+n') * m = m + (n' * m)

The first equation is a basic property of multiplication.  The second
follows by distributing the multiplication over the addition.
-%

%- Problem 6 -%

Define diff := 
  fun diff(x y : nat):bool.
    match x with
      Z => match y with
             Z => ff
           | S y' => tt
           end
   | S x' => match y with
               Z => tt
             | S y' => (diff x' y')
             end
   end.

Interpret (diff (S (S Z)) (S (S (S Z)))).

%- Problem 7 -%

Define iter :=
  fun iter(n:nat)(f:Fun(x:nat).nat)(a:nat):nat.
   match n with
     Z => a
   | S n' => (f (iter n' f a))
   end.

Define double := fun(x:nat). (plus x x).

Interpret (iter (S (S (S Z))) double (S Z)).

Define first_h :=
  fun first_h(n:nat)(P:Fun(x:nat).bool):nat.
    match (P n) with
      ff => (first_h (S n) P)
    | tt => n
    end.

Define first := fun(P:Fun(x:nat).bool).(first_h Z P).

Include "../guru-lang/lib/mult.g".

Interpret (first fun(x:nat). (eqnat (mult x x) nine)).

