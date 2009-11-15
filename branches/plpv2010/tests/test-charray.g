Include "../lib/charray.g".

%Set "debug_eta_expand".
%Set "debug_to_carraway".

Set "use_malloc".

Inductive tmp : type :=
  mk_tmp : Fun(#unique x:<charray nat>).#unique tmp.

Define test :=
  let a = Z in
  let arr = (charray_new nat (inspect nat a)) in
  let val = (charray_get nat arr Cnl) in
  let arr' = (charray_set nat Cnl (S (owned_to_unowned nat val)) arr) in
  let x = (mk_tmp arr') in
  match x with
    mk_tmp arr1 =>
    do (dec nat a)
       (charray_free nat arr1)
    end
  end.

Compile test to "test-charray.c".
