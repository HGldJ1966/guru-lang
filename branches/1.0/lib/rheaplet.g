% A rheaplet models a portion of heap-allocated memory using run-time 
% reference counting of aliases.
%
% Rheaplets are just specificational data, and do not
% exist at runtime (we must just pass a dummy value
% through for them everywhere).  
%
% But: we must allocate 3-word "holder" cells to store the reference
% to each aliased value.  This is necessary to keep track
% dynamically of the number of aliases, and to enable replacement
% of the aliased value (while preserving the fact that aliases
% point to it -- via the holder cells).

Include trusted "list.g".
Include "holder.g".
Include "unique_owned.g".

% the functional model for rheaplets.

% <rheaplet A I> is the type for rheaplets holding objects of type A, with rheaplet_id I.  
%
% rheaplet_ids are used to connect aliases to the rheaplet with which they are associated.
% rheaplet_ids do not exist at runtime (again, a dummy value is passed through for them).

Define primitive rheaplet_id := nat <<END
  #define gconsume_rheaplet_id(x)
END.

Define primitive rheaplet_id0 : #unique rheaplet_id := Z <<END
  #define grheaplet_id0 1
END.

Define primitive type_family_abbrev rheaplet := fun(A:type)(I:rheaplet_id).<list A> <<END
  #define gconsume_rheaplet(x)
END.

Inductive new_rheaplet_t : Fun(A:type)(I:rheaplet_id).type :=
  return_new_rheaplet : Fun(spec A:type)(spec I : rheaplet_id)
                          (#unique nextI:rheaplet_id)
                          (#unique h:<rheaplet A I>).#unique <new_rheaplet_t A I>.

Define primitive new_rheaplet : Fun(spec A:type)(#unique I:rheaplet_id).#unique <new_rheaplet_t A I> :=
  fun(A:type)(I:rheaplet_id). (return_new_rheaplet A I (S I) (nil A)) <<END
void *gnew_rheaplet(int I) {
  return greturn_new_rheaplet(I,0);
}
END.

% <alias I> is the type for a pointer into the (unique) rheaplet with rheaplet id I.
%
% In the functional model, p:<alias I> is the position in the rheaplet, starting from
% the end, where the data pointed to by the pointer is stored.
%
% In the actual implementation, p:<alias I> is a "holder", which allows us to
% use refcounts to count the number of aliases.

Define primitive type_family_abbrev alias := fun(I:rheaplet_id).nat <<END
#define gconsume_alias(x) x
END.

Inductive rheaplet_in_t : Fun(A:type)(I:rheaplet_id).type :=
  return_rheaplet_in : Fun(spec A:type)(spec I:rheaplet_id)
                             (#unique h:<rheaplet A I>)
                             (#unique p:<alias I>).
                          #unique <rheaplet_in_t A I>.

Define primitive rheaplet_in : Fun(spec A:type)(spec I:rheaplet_id)
                                  (#unique h:<rheaplet A I>)(a:A).
                               #unique <rheaplet_in_t A I> :=
  fun (A:type)(spec I:rheaplet_id)(h:<rheaplet A I>)(a:A).
   (return_rheaplet_in A I (append A h (cons A a (nil A))) (length A h)) <<END
void *grheaplet_in(int h, void *a) {
  return greturn_rheaplet_in(1,gmk_holder(A,a));
}
END.

Define primitive rheaplet_alias : Fun(spec A:type)(spec I:rheaplet_id)(!#unique p:<alias I>).
                                  #unique <alias I> :=
  fun (A:type)(spec I:rheaplet_id)(p:<alias I>). p <<END
#define grheaplet_alias(h,a) ginc(a)
END.

Define primitive rheaplet_drop : Fun(A:type)(spec I:rheaplet_id)(#unique p:<alias I>).
                                   void :=
  fun (A:type)(spec I:rheaplet_id)(p:<alias I>). voidi <<END
#define grheaplet_drop(A,h,a) gdec(A,a)
END.

Define primitive rheaplet_get : Fun(spec A:type)(spec I:rheaplet_id)
                                   (!#unique h:<rheaplet A I>)(^#unique_owned p:<alias I>).
                               #<owned h> A :=
  fun (A:type)(spec I:rheaplet_id)(h:<rheaplet A I>)(p:<alias I>). (nth A p h) <<END
#define grheaplet_get(h, p) select_holder_mk_holder_a(p)
}
END.

Define primitive rheaplet_set : Fun(A:type)(spec I:rheaplet_id)
                                   (#unique h:<rheaplet A I>)(!#unique p:<alias I>)(a:A).
                               #unique <rheaplet A I> :=
  fun (A:type)(spec I:rheaplet_id)(h:<rheaplet A I>)(p:<alias I>)(a:A). (set_nth A p h a) <<END
int grheaplet_get(int A, int h, void *p, void *a) {
    gdec(A,select_holder_mk_holder_a(p));
    select_holder_mk_holder_a(p) = a;
    return 1;
}
END.

