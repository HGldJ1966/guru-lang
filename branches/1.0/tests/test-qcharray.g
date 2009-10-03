Include "../lib/charray.g".
Include "../lib/qcharray.g".
Include "../lib/tholder.g".

Define charray_free2 := fun(spec A:type)(^#owned t:<tholder A>)(^#unique a:<charray A>).
                          match t with mk_tholder A' => (charray_free A' a) end.
Define func := fun(^#owned a:nat):#unique <charray nat>. (charray_new nat a).
Define test :=
  let a = Z in
  let arr = (qcharray_new <charray nat> nat (inspect nat a) func) in
  let cookie = (mk_tholder nat) in
  let iarr = (inspect_unique <qcharray <charray nat> stringn> arr) in
  do (consume_unique_owned <charray nat>
         (qcharray_read <charray nat> 'a' iarr))
     (consume_unique_owned <qcharray <charray nat> stringn> iarr)
    match (qcharray_out <charray nat> 'a' stringn arr join (string_mem 'a' stringn) ff) with
      mk_qcharray_mod _ b _ _ arr' =>
      do (charray_free nat b)
         let arr = (qcharray_in <charray nat> 'a' (charray_new nat (inspect nat a)) stringn stringn
                     cast arr' by cong <qcharray <charray nat> *>
                                   join (stringc 'a' stringn) (string_app stringn (stringc 'a' stringn))) in
         do
          (dec nat a)
          (qcharray_free <charray nat> <tholder nat> 
             cast arr by cong <qcharray <charray nat> *> join (string_app stringn stringn) stringn
             (inspect <tholder nat> cookie) (charray_free2 nat))
          (dec <tholder nat> cookie)
         end
      end
    end
  end.

%Set "debug_eta_expand".
%Set "debug_to_carraway".
%Set "debug_stages".

Compile test to "test-qcharray.c".
