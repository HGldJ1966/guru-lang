% A heaplet models a portion of heap-allocated memory.
%
% Heaplets are just specificational data, and do not
% exist at runtime (we must just pass a dummy value
% through for them everywhere).  
%
% We statically reference count the data stored in the
% heaplet, and deallocate data only when the reference
% count is known (statically) to be zero.

Include trusted "list.g".
Include "unique.g".

Define natlist := <list nat>.
Define natlistn := (nil nat).
Define natlistc := (cons nat).

% the functional model for heaplets.
%
% L is the list of static reference counts.  An entry of Z there means the corresponding entry
% has been removed from the heaplet.  An entry of (S n) means there are n outstanding aliases.

Inductive heaplist : Fun(A:type)(L:natlist).type :=
  heaplistn : Fun(A:type).<heaplist A natlistn>
| heaplistc : Fun(A:type)(n:nat)(a:A)(L:natlist)(h:<heaplist A L>).<heaplist A (natlistc (S n) L)>
| heaplistg : Fun(A:type)(L:natlist)(h:<heaplist A L>).<heaplist A (natlistc Z L)>.

% <heaplet A I L> is the type for heaplets holding objects of type A, with heaplet_id I,
% and list of static reference counts L.  
%
% heaplet_ids are used to connect aliases to the heaplet with which they are associated.
% heaplet_ids do not exist at runtime (again, a dummy value is passed through for them).

Define primitive type_family_abbrev heaplet := fun(A:type)(I:nat)(L:natlist).<heaplist A L> <<END
  #define gconsume_heaplet(x)
END.

Define primitive heaplet_id := nat <<END
  #define gconsume_heaplet_id(x)
END.

Define primitive heaplet_id0 := Z <<END
  #define gheaplet_id0 1
END.

Inductive new_heaplet_t : Fun(A:type)(I:heaplet_id).type :=
  return_new_heaplet : Fun(spec A:type)(spec I : heaplet_id)
                          (#unique nextI:heaplet_id)
                          (#unique h:<heaplet A I natlistn>).<new_heaplet_t A I>.

Define primitive new_heaplet : Fun(spec A:type)(#unique I:heaplet_id).<new_heaplet_t A I> :=
  fun(A:type)(I:heaplet_id). (return_new_heaplet A I (S I) (heaplistn A)) <<END
void *gnew_heaplet(int I) {
  return greturn_new_heaplet(I,0);
}
END.

% <alias I> is the type for a pointer into the (unique) heaplet with heaplet id I.
%
% In the functional model, p:<alias I> is the position in the heaplet, starting from
% the end, where the data pointed to by the pointer is stored.
%
% In the actual implementation, p:<alias I> is pointer directly to the data.

Define primitive type_family_abbrev alias := fun(I:heaplet_id).nat <<END
#define gconsume_alias(x)
END.

Inductive heaplet_alias_t : Fun(A:type)(I:heaplet_id)(L:natlist).type :=
  return_heaplet_alias : Fun(spec A:type)(spec I:heaplet_id)(spec L:natlist)
                            (#unique h:<heaplet A I L>)(#unique p:<alias I>).<heaplet_in_t A I L>.

Define primitive heaplet_in : Fun(spec A:type)(spec I:heaplet_id)(spec L:natlist)
                                 (h:<heaplet A I L>)(a:A).
                              <heaplet_alias_t A I (append nat L (natlistc (S Z) natlistn))> :=
  fun r(A:type)(spec I:heaplet_id)(spec L:natlist)
       (h:<heaplet A I L>)(a:A):
    <heaplet_alias_t A I (append nat L (natlistc (S Z) natlistn))>.
    match h with
      heaplistn _ => cast (heaplistc A n a natlistn (heaplistn A))
                     by cong <heaplist A *> join (natlist (S Z) natlistn

void *gheaplet_in(void *h, void *a) {
  return greturn_heaplet_alias(h,a);
}
END.

