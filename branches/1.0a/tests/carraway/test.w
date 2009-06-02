%Set "print_parsed".
%Set "debug_primitives".
Set "debug_stages".

Include "nat.w".
Include "owned.w".

Global two := let one = (S Z) in (S one).

Function plus2(^ x:owned)(^ y:owned).unowned :=
  match x with
    Z => (owned_to_unowned y)
  | S x' => (S (plus2 x' y))
  end.

Function pred(! x:owned).<owned x> :=
  match x with
    Z => (clone_owned x)
  | S x' => x'
  end.

Function foo(! pred2:owned).void := abort.

Function subtract(^ x:owned)(^ y:owned).unowned :=
  match x with
    Z => do (consume_owned nat y) Z end
  | S x' => 
    match y with
      Z => do (consume_owned nat x') (inc_owned x) end
    | S y' => (subtract x' y')
    end
  end.

Function subtract2(^ x:owned)(^ y:owned).unowned :=
  match y with
    Z => (owned_to_unowned x)
  | S y' => let ret = (subtract2 (pred x) y') in do (consume_owned nat x) ret end
  end.

Datatype holder := mk_holder : Fun(x:unowned & nat)(y:<owned x> & nat).unowned.

Function pred2(x:unowned).unowned :=
  let y = (inspect x) in
  match $ y with
    Z => (mk_holder x (inspect x))
  | S x' => (mk_holder x (compress_owned2 x y x'))
  end.

%Set "debug_simulate".
%Set "debug_subst".
%Set "debug_refs".

Function test_pred2(x:unowned).void :=
  match (pred2 x) with
    mk_holder x' y => 
      do (consume_owned nat y)
         (dec nat x')
      end
    end.

