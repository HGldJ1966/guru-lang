%% FIXME parser probably still needs work
%% so that e.g. "cast...by" can take any terminating term instead of
%% just an injective one

Include "../lib/nat.g".
Include "../lib/list.g".

Set "print_parsed".
Set "debug_terminates".

Define ident : Fun(n:nat).nat :=
  fun(n:nat).
  n.

% nullary function for testing
%% interestingly, this doesn't work
%Define zero : Fun.nat :=
%  fun zero:nat.Z.

Define ident_total : Forall(n:nat).Exists(m:nat).{ (ident n) = m } :=
  foralli(n:nat).
    existsi n { (ident n) = * }
            join (ident n) n.

Inductive Unit : type :=
    unit : Unit.

Define hof : Fun(u:Unit).Fun(w:Unit).nat :=
  fun(u:Unit).
  fun(w:Unit).
  Z.

Define hof_total : Forall(u:Unit).Exists(f:Fun(w:Unit).nat).{ (hof u) = f } :=
  foralli(u:Unit).
    existsi fun(w:Unit).Z { (hof u) = * }
            join (hof u) fun(w:Unit).Z.

Define hof_apps_total : Forall(u:Unit)(w:Unit).Exists(n:nat).{ ((hof u) w) = n } :=
  foralli(u:Unit)(w:Unit).
    existsi Z { ((hof u) w) = * }
            join ((hof u) w) Z.

Define hof_apps_total5 : { (hof unit unit) = Z } :=
  join (hof unit unit) Z.

%% can't define this
%% Define id1 := [ident_total (ident (S Z))].

%% but this works
Define id2 := [ident_total terminates (ident (S Z)) by ident_total].

%% this tests nested terminates
Define id3 := [ident_total (S terminates (ident Z) by ident_total)].

Define id4 := [ident_total (S terminates (ident (S Z)) by ident_total)].

Define id5 := [ident_total terminates ((hof unit) unit) by hof_apps_total].

Define id6 := [ident_total terminates (hof unit unit) by hof_apps_total].

Define ident_list : Fun(A:type)(l:<list A>).<list A> :=
  fun(A:type)(l:<list A>).
  l.

Define ident_list_total : Forall(A:type)(l:<list A>).Exists(l2:<list A>).{ (ident_list A l) = l2 } :=
  foralli(A:type)(l:<list A>).
    existsi l { (ident_list A l) = * }
      join (ident_list A l) l.

Define idl1 := [ident_list_total nat terminates (ident_list nat (nil nat)) by ident_list_total].
