Include "../lib/charvec.g".

%Set "debug_eta_expand".
%Set "debug_to_carraway".

Set "use_malloc".

Define test :=
  let a = Z in
  let arr = (mk_charvec nat (inspect nat a)) in
  let val = (cvget nat arr Cnl) in
  let arr' = (cvupdate nat Cnl (S (owned_to_unowned nat val)) arr) in
  do (dec nat a)
     (cvfree nat arr')
  end.

Compile test to "test-charvec.c".