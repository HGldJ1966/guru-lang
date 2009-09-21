%=============================================================================
% Definition of problem
%=============================================================================

Include trusted "../lib/list.g".
Include trusted "order.g".

Inductive Job : type :=
  job : Fun(s e:nat)(u:{ (lt s e) = tt }).Job
.

Define job_start :=
  fun(j:Job).
  match j with
    job s e _ => s
  end.

Define job_end :=
  fun(j:Job).
  match j with
    job s e _ => e
  end.

Define job_compat : Fun(a b:Job).bool :=
  fun(a b:Job).
  match a with
    job a_s a_e _ =>
      match b with
        job b_s b_e _ =>
          (or (le a_e b_s)
              (le b_e a_s))
      end
  end.

Define job_compat_all : Fun(a:Job)(s:<list Job>).bool :=
  fun(a:Job)(s:<list Job>).
  let f = fun(x:Job).(job_compat x a) in
  (list_all Job f s).

Define mutual_compat_h : Fun(done todo:<list Job>).bool :=
  fun mutual_compat_h(done todo:<list Job>) : bool.
  match todo with
    nil _ => tt
  | cons _ x todo' =>
      let b = (job_compat_all x (append Job done todo')) in
      match b with
        ff => ff
      | tt => (mutual_compat_h (cons Job x done) todo')
      end
  end.
  
Define mutual_compat : Fun(s:<list Job>).bool := (mutual_compat_h (nil Job)).


%=============================================================================
% the algorithm
%=============================================================================

Define solve_h :=
  fun solve_h(todo done:<list Job>) : <list Job>.
  match todo with
    nil _ => done
  | cons _ x xs =>
      match (job_compat_all x done) with
        ff => (solve_h xs done)
      | tt => (solve_h xs (cons Job x done))
      end
  end.

Define solve :=
  fun(l:<list Job>).
  let lt' = fun(a b:Job).(lt (job_end a) (job_end b)) in
  (solve_h (sort Job lt' l) (nil Job)).


%=============================================================================
% an example problem
%=============================================================================

Define ten := (S nine).
Define eleven := (S ten).

Define a := (job zero six join (lt zero six) tt).
Define b := (job one four join (lt one four) tt).
Define c := (job three five join (lt three five) tt).
Define d := (job three eight join (lt three eight) tt).
Define e := (job four seven join (lt four seven) tt).
Define f := (job five nine join (lt five nine) tt).
Define g := (job six ten join (lt six ten) tt).
Define h := (job eight eleven join (lt eight eleven) tt).

Define problem1 := (cons Job a
                   (cons Job b
                   (cons Job c
                   (cons Job d
                   (cons Job e
                   (cons Job f
                   (cons Job g
                   (cons Job h
                   (nil Job))))))))).

Define sol1 := (cons Job b
               (cons Job e
               (nil Job))).

Define nonsol1 := (cons Job a
                  (cons Job b
                  (nil Job))).

%Interpret (job_compat b e).
%Interpret (mutual_compat sol1).
%Interpret (mutual_compat nonsol1).

Define sol := (solve problem1).
Interpret problem1.
Interpret sol.
Interpret (mutual_compat sol).


%=============================================================================
% theorems
%=============================================================================

%-
Define solve_total :
  Forall(l:<list Job>).
  Exists(z:<list Job>).
    { (solve l) = z }
  :=
  truei.
-%

%-
Define solve_sound :
  Forall(l:<list Job>).
    { (mutual_compat (solve l)) = tt }
  :=
  truei.
-%

%-
Define solve_optimal :
  Forall(l:<list Job>)
        (sol:<list Job>)
        (u1:{ (list_subset sol l) = tt })
        (u2:{ (mutual_compat sol) = tt })
    { (le (cardinality sol) (cardinality (solve l))) = tt }
  :=
  truei.
-%
