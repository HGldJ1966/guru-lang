Include "../lib/charvec.g".
Include "../lib/ucharvec.g".

%Set "debug_eta_expand".
%Set "debug_to_carraway".
Set "debug_stages".

Set "use_malloc".

Define func := fun(^#owned a:nat):#unique <charvec nat>. (mk_charvec nat a).
Define test :=
  let a = Z in
  let arr = (mk_ucharvec <charvec nat> nat (inspect nat a) func) in
  do (dec nat a)
     (ucvfree <charvec nat> stringn arr)
  end.

Compile test to "test-ucharvec.c".