Include trusted "list.g".
Include "unit.g".
Include "holder.g".
Include "unique_owned.g".

% the functional model for heaplets.

Define primitive heaplet_id := nat <<END
  #define gdelete_heaplet_id(x)
END.

Define primitive heaplet_id0 : #unique heaplet_id := Z <<END
  #define gheaplet_id0 1
END.

% call this once per compiled program, just to have the compiler pull in functions
% we need in our C code.
Define init_heaplets : Fun(u:Unit).Unit :=
  fun(u:Unit).
    let x = mk_holder in unit.


<heaplet A I n> -- type for heaplets of As with id I and n aliases.
Define primitive type_family_abbrev heaplet := fun(A:type)(I:heaplet_id)(n:nat).<list A> <<END
  #define gdelete_heaplet(x)
END.

Inductive new_heaplet_t : Fun(A:type)(I:heaplet_id).type :=
  return_new_heaplet : Fun(spec A:type)(spec I : heaplet_id)
                          (#unique nextI:heaplet_id)
                          (#unique h:<heaplet A I Z>).#unique <new_heaplet_t A I>.

Define primitive new_heaplet : Fun(spec A:type)(#unique I:heaplet_id).#unique <new_heaplet_t A I> :=
  fun(A:type)(I:heaplet_id). (return_new_heaplet A I (S I) (nil A)) <<END
void *gnew_heaplet(int I) {
  return greturn_new_heaplet(I,0);
}
END.

Define primitive type_family_abbrev alias := fun(I:rheaplet_id).nat <<END
void gdelete_alias(void *x) {
     release(gholder,x,1); // this will decrement the refcount for the data pointed to.
}
END.

Inductive heaplet_in_t : Fun(A:type)(I:heaplet_id)(n:nat).type :=
  return_heaplet_in : Fun(spec A:type)(spec I:heaplet_id)
                         (spec n:nat)
                         (#unique h:<heaplet A I (S n)>)
                         (#unique p:<alias I>).
                        #unique <heaplet_in_t A I n>.

Define primitive heaplet_in : Fun(A:type)(spec I:heaplet_id)(spec n:nat)
                                 (#unique h:<heaplet A I n>)(a:A).
                               #unique <heaplet_in_t A I n> :=
  fun (A:type)(spec I:heaplet_id)(h:<heaplet A I>)(a:A).
   (return_heaplet_in A I (append A h (cons A a (nil A))) (length A h)) <<END
void *gheaplet_in(int A, int h, void *a) {
  return greturn_heaplet_in(1,a);
}
END.

Inductive heaplet_dup_t : Fun(A:type)(I:rheaplet_id)(n:nat).type :=
  return_heaplet_dup : Fun(A:type)(spec I:rheaplet_id)(spec n:nat)
                          (#unique h:<heaplet A I (S n)>)
                          (#unique p:<alias I>).<heaplet_dup_t A I n>.

Define primitive heaplet_dup : Fun(spec A:type)(spec I:rheaplet_id)(spec n:nat)
                                  (#unique h:<rheaplet A I n>)
                                  (!#unique_owned p:<alias I>).
                                <heaplet_dup_t A I n> :=
  fun(spec A:type)(spec I:rheaplet_id)(spec n:nat)
     (h:<rheaplet A I n>)
     (p:<alias I>). p <<END

inline void *gheaplet_dup(int h, void *p) {
  return p;
}
END.
                               

Define primitive rheaplet_get : Fun(spec A:type)(spec I:rheaplet_id)(spec n:nat)(#unique_owned p:<alias I>)
                                   (!#unique_owned h:<rheaplet A I>).
                               #<owned h> A :=
  fun (A:type)(spec I:rheaplet_id)(spec n:nat)(p:<alias I>)(h:<rheaplet A I>). (nth A p h) <<END
#define grheaplet_get(p, h) select_holder_mk_holder_a(p)
END.

