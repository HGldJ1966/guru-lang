%- This file does an example proof from the paper "Asynchronous
   Exceptions as an Effect" by Harrison, Allwein, Gill, and Procter.

   The example is Theorem 1 for the N monad. 

   Note that implementing monad transformers in Guru would not be
   straightforward at the moment, since Guru does not support
   quantification or abstraction over type constructors.  But
   implementing monads directly is not a problem.  And this seems
   to be all that is needed for the theorems of the above-cited 
   paper.

   For information on Guru syntax and semantics, see
   www.guru-lang.org, particularly the textbook "Verified Programming
   in Guru".  I have included a few "small notes" below, on a couple
   features not documented in that book.
   
-%

Include trusted "../lib/list.g".

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Step 1: define the monad types
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Small note: the "type_family_abbrev" is needed for defining type
% constructors.

Define type_family_abbrev N := fun(a:type).<list a>.

Inductive Err : Fun(a:type).type :=
  Ok : Fun(a:type)(x:a).<Err a>
| Error : Fun(a:type).<Err a>.

Define type_family_abbrev E := fun(a:type).<N <Err a>>.

Inductive R : Fun(a:type).type :=
  Done : Fun(a:type)(x:a).<R a>
| Pause : Fun(a:type)(x:<E <R a>>). <R a>.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Step 2: define the monad operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Define etaN : Fun(a:type)(x:a).<N a> := fun(a:type)(x:a). (cons a x (nil a)).

% Small note: the "spec" means that starN cannot be compiled.  This is
% because it is using spec-functions map1 and concat (which at least
% in the case of map1, are more convenient than the versions of those
% functions for use in compiled code).

Define spec starN : Fun(a b:type)(phi:<N a>)(f:Fun(x:a).<N b>).<N b> :=
   fun(a b:type)(phi:<N a>)(f:Fun(x:a).<N b>).
     (concat b (map1 a <N b> f phi)).

Define spec mergeN : Fun(a:type)(x:<N <N a>>).<N a> := concat.

Define etaE : Fun(a:type)(x:a).<E a> := fun(a:type)(x:a).(etaN <Err a> (Ok a x)).

Define spec starE : Fun(a b:type)(phi:<E a>)(f:Fun(x:a).<E b>).<E b> :=
  fun(a b:type)(phi:<E a>)(f:Fun(x:a).<E b>).
    (starN <Err a> <Err b> phi
       fun(v:<Err a>).
         match v with
           Ok _ x => (f x)
         | Error _ => (etaN <Err b> (Error b))
         end).

Define etaR : Fun(a:type)(x:a).<R a> := Done.

Define spec starR : Fun(a b:type)(phi:<R a>)(f:Fun(x:a).<R b>).<R b> :=
  fun starR(a b:type)(phi:<R a>)(f:Fun(x:a).<R b>):<R b>.
    match phi with
      Done _ x => (f x)
    | Pause _ phi => 
        (Pause b (starE <R a> <R b> phi 
                    fun(k:<R a>).(etaE <R b> (starR a b k f))))
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Step 3: prove a monad theorem
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% I wrote test1 and test2 here just to type-check the lhs and rhs of
% the equation to prove (in Guru, equations are not type-checked).

Define spec test1 : Fun(a b:type)(phis:<N <N a>>)(f:Fun(x:a).<N b>).<N b> :=
  fun(a b:type)(phis:<N <N a>>)(f:Fun(x:a).<N b>).
    (starN a b (mergeN a phis) f).

Define spec test2 : Fun(a b:type)(phis:<N <N a>>)(f:Fun(x:a).<N b>).<N b> :=
  fun(a b:type)(phis:<N <N a>>)(f:Fun(x:a).<N b>).
    (mergeN b (map1 <N a> <N b> fun(phi:<N a>).(starN a b phi f) phis)).

Define thm1N : Forall(a b:type)(phis:<N <N a>>)(f:Fun(x:a).<N b>)
                     (fTot:Forall(x:a).Exists(y:<N b>).{ (f x) = y }).
                 { (starN (mergeN phis) f) = (mergeN (map1 fun(phi).(starN phi f) phis)) } :=
  foralli(a b:type)(phis:<N <N a>>)(f:Fun(x:a).<N b>)
         (fTot:Forall(x:a).Exists(y:<N b>).{ (f x) = y }).

  % change "transs" to "show" below to see the equational steps (even
  % nicer printing results if you enclose the whole transs-end proof
  % inside show-end).

  transs
    join (starN (mergeN phis) f) (concat (map1 f (concat phis)))
    cong (concat *) [map1_concat a <list b> f phis]
    [concat_concat_map1 <list a> b fun(x:<list a>).(map1 a <list b> f x)
       foralli(x:<list a>).
         existsi terminates (map1 a <list b> f x) by [map1_total a <list b> f fTot x] 
           { (fun(x).(map1 f x) x) = * }
           join (fun(x).(map1 f x) x) (map1 f x)
       phis]
    cong (concat *) [map1_ext <list a> <list b>
                      fun(phi:<list a>).(concat b (fun(phi:<list a>).(map1 a <list b> f phi) phi))
                      fun(phi:<list a>).(starN a b phi f)
                      foralli(phi:<list a>).
                        existsi (concat b 
                                   terminates (map1 a <list b> f phi)
                                   by [map1_total a <list b> f fTot phi])
                          {(fun(phi).(concat (fun(phi).(map1 f phi) phi)) phi) = *}
                          join (fun(phi).(concat (fun(phi).(map1 f phi) phi)) phi) (concat b (map1 f phi))
                      foralli(phi:<list a>).
                        join (fun(phi:<list a>).(concat b (fun(phi:<list a>).(map1 a <list b> f phi) phi)) phi)
                             (fun(phi:<list a>).(starN a b phi f) phi)
                      phis]
   join (concat (map1 fun(phi). (starN phi f) phis)) (mergeN (map1 fun(phi). (starN phi f) phis))
  end.
