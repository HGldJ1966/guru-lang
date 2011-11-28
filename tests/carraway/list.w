Set "debug_stages".

Include "owned.w".
Include "nat.w".

Datatype list := nil : unowned | cons : Fun(A:type)(x:unowned & A)(l:unowned & list).unowned.

Datatype ulist := unil : unowned | ucons : Fun(x:untracked)(l:unowned & ulist).unowned.

Function append(l1:unowned)(l2:unowned).unowned :=
  match l1 with
    nil => l2
  | cons A a l1' => (cons A a (append l1' l2))
  end.

Function length(l1:unowned).unowned :=
  match l1 with
    nil => Z
  | cons A a l1' => do (dec A a) (S (length l1')) end
  end.

%Set "disambiguate_vars".
%Set "debug_refs".
%Set "debug_simulate".

Function get(^n:owned)(!l:owned).<owned l> :=
 match l with
    nil => abort
 | cons A a l' =>
   let ret = 
     match n with
       Z => a
     | S n' => do (consume_owned A a) @ (get n' l') end
     end
   in
     do (consume_owned list l')
        ret
     end
 end.
