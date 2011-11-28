Include "qcharray.g".
Include "string.g".
Include "option.g".
Include "unique_owned.g".
Include "pair.g".

%- <trie A> is the type for tries storing elts of type A. 

   trie_next holds data in "o" if the empty string maps to
   that data. -%
Inductive trie : Fun(A:type).type :=
  trie_none : Fun(spec A:type).#unique <trie A>
| trie_exact : Fun(A:type)(s:string)(a:A).#unique <trie A>
| trie_next : Fun(A:type)(o:<option A>)
                 (#unique l:<qcharray <trie A> stringn>). 
              #unique <trie A>.

Inductive trie_insert_i : Fun(A:type).type :=
  mk_trie_insert_i : Fun(A:type).<trie_insert_i A>.

% insert (s,a) into t, discarding any previous value stored for s.
Define trie_insert : Fun(A:type)(s:string)(a:A)(#unique t:<trie A>).
                         #unique <trie A> :=
  fun trie_insert(A:type)(s:string)(a:A)(#unique t:<trie A>) : #unique <trie A> .
    match t with
      trie_none _ => (trie_exact A s a)
    | trie_exact _ s' a' =>
  
      %- insert (s',a') into a new blank trie_next, then
         insert (s,a) into the result. -%

      let cookie = Z in
      let v = (qcharray_new <trie A> nat (inspect nat cookie)
                 fun(^#owned cookie:nat) : #unique <trie A>.
                     (trie_none A)) in
      do 
        (dec nat cookie)
        (trie_insert A s a
        (trie_insert A s' a' (trie_next A (nothing A) v)))
      end
    | trie_next _ o l' => 
        match s with
          unil _ => do (dec <option A> o) 
                      (trie_next A (something A a) l')
                   end
        | ucons _ c s' => 
          match (qcharray_out <trie A> c stringn l' join (string_mem c stringn) ff) with
            mk_qcharray_mod _ a' _ _ l'' =>
              let r = (trie_insert A s' a a') in 
                (trie_next A o 
                   (qcharray_in1 <trie A> c r l''))
          end
        end
    end.
          
Define trie_remove : Fun(spec A:type)(^#owned s:string)(#unique t:<trie A>).
                         #unique <trie A> :=
  fun trie_remove(spec A:type)(^#owned s:string)(#unique t:<trie A>) : #unique <trie A>.
    match t with
      trie_none _ => (trie_none A)
    | trie_exact A' s' a' =>
        match (stringeq s (inspect string s')) with
          ff => (trie_exact A' s' a')
        | tt => do (dec A' a')
                   (dec string s')
                   (trie_none A)
                end
        end
    | trie_next A' o l' => 
        match s with
          unil _ => do (dec <option A> o) 
                      (trie_next A' (nothing A) l')
                   end
        | ucons _ c s' => 
          match (qcharray_out1 <trie A> c l') with
            mk_qcharray_mod _ a' _ _ l'' =>
              let r = (trie_remove A s' a') in 
                (trie_next A' o 
                   (qcharray_in1 <trie A> c r l''))
          end
        end
    end.

Define trie_lookup : Fun(A:type)(^#unique_owned t:<trie A>)(^#owned s:string).
                        <option A> :=
  fun trie_lookup(A:type)(^#unique_owned t:<trie A>)(^#owned s:string)
      : <option A> .
    match ! t with
      trie_none _ => (nothing A)
    | trie_exact _ s' a' => 
        match (stringeq s s') with
          ff => (nothing A)
        | tt => (something A (owned_to_unowned A a'))
        end
    | trie_next _ o' l' =>
        match ! s with
          unil _ => (owned_to_unowned <option A> o')
        | ucons _ c s' => 
          (trie_lookup A (qcharray_read <trie A> c l') s') 
        end
    end.

