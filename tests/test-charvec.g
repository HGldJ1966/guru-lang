Include "../lib/charvec.g".

%Set "debug_eta_expand".
%Set "debug_to_carraway".

Set "use_malloc".

Inductive tmp : type :=
  mk_tmp : Fun(#unique x:<charvec nat>).#unique tmp.

Define test :=
  let a = Z in
  let arr = (mk_charvec nat (inspect nat a)) in
  let val = (cvget nat arr Cnl) in
  let arr' = (cvupdate nat Cnl (S (owned_to_unowned nat val)) arr) in
  let x = (mk_tmp arr') in
  match x with
    mk_tmp arr1 =>
    do (dec nat a)
       (cvfree nat arr1)
    end
  end.

Compile test to "test-charvec.c".
