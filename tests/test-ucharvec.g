Include "../lib/charvec.g".
Include "../lib/ucharvec.g".
Include "../lib/tholder.g".

%Set "debug_eta_expand".
%Set "debug_to_carraway".
Set "debug_stages".

Set "use_malloc".

Define cvfree2 := fun(spec A:type)(^#owned t:<tholder A>)(^#unique a:<charvec A>).
                     match t with mk_tholder A' => (cvfree A' a) end.
Define func := fun(^#owned a:nat):#unique <charvec nat>. (mk_charvec nat a).
Define test :=
  let a = Z in
  let arr = (mk_ucharvec <charvec nat> nat (inspect nat a) func) in
  let cookie = (mk_tholder nat) in
  do (dec nat a)
     (ucvfree <charvec nat> <tholder nat> arr (inspect <tholder nat> cookie) (cvfree2 nat))
     (dec <tholder nat> cookie)
  end.

Compile test to "test-ucharvec.c".
