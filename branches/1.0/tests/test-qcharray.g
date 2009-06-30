Include "../lib/charray.g".
Include "../lib/qcharray.g".
Include "../lib/tholder.g".

%Set "debug_eta_expand".
%Set "debug_to_carraway".
Set "debug_stages".

Set "use_malloc".

Define charray_free2 := fun(spec A:type)(^#owned t:<tholder A>)(^#unique a:<charray A>).
                          match t with mk_tholder A' => (charray_free A' a) end.
Define func := fun(^#owned a:nat):#unique <charray nat>. (charray_new nat a).
Define test :=
  let a = Z in
  let arr = (qcharray_new <charray nat> nat (inspect nat a) func) in
  let cookie = (mk_tholder nat) in
  do (dec nat a)
     (qcharray_free <charray nat> <tholder nat> arr (inspect <tholder nat> cookie) (charray_free2 nat))
     (dec <tholder nat> cookie)
  end.

Compile test to "test-qcharray.c".
