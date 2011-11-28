Include "../lib/charray.g".
Include "../lib/unique_owned.g".

Set "use_malloc".

Inductive foo : type :=
  mk_foo : Fun(#unique x:<charray nat>)(y:nat).#unique foo.

Define free_foo : Fun(#unique x:foo).void :=
  fun(#unique x:foo).
    match x with
      mk_foo x y => do (charray_free nat x) (dec nat y) end
    end.

Define test :=
  let a = Z in
  let arr = (charray_new nat (inspect nat a)) in
  let t = (mk_foo arr a) in
  let b = 
    match (inspect_unique foo t) with
      mk_foo x y => 
      do (consume_unique_owned <charray nat> x)
         (owned_to_unowned nat y)
      end
    end in

  do (dec nat b)
     (free_foo t)
  end.

%Set "debug_to_carraway".
%Set "debug_eta_expand".

%Set "debug_simulate".
%Set "disambiguate_vars".

Compile test to "test-unique-owned.c".
