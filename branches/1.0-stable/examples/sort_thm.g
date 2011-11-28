Include "sort.g".

%=============================================================================
% ordered predicate (ulist)
% true if the list is (total-)ordered
% the input predicate "lt" means "less than", but can be reflecxive.
% note that "lt" does not have to be globally transitive
% but, considered ordered only if it is transitive for all items in the list
%=============================================================================

% x is less than each element of l
Define ulist_lt_each := fun ulist_lt_each
	(A:type)
	(lt:Fun(a b:A).bool)
	(x:A)(l:<ulist A>)
	: bool.
  match l with
    unil _ => tt
  | ucons _ a l' =>
      match (lt x a) with
        ff => ff
      | tt => (ulist_lt_each A lt x l')
      end
  end.

Define ulist_ordered := fun ulist_ordered
	(A:type)
	(lt:Fun(a b:A).bool)
	(l:<ulist A>)
	: bool.
  match l with
    unil _ => tt		% empty list is always ordered
  | ucons _ a l' =>
      match (ulist_lt_each A lt a l') with
        ff => ff
      | tt => (ulist_ordered A lt l')
      end
  end.

%=============================================================================
% lemmas
%=============================================================================

%=============================================================================
% Thm: usort is correct
%=============================================================================
Define usort_orderd : Forall
	(A:type)
	(lt:Fun(a b:A).bool)
	(lt_trans:Forall(a b c:A)(u1:{ (lt a b) = tt })(u2:{ (lt b c) = tt }).{ (lt a c) = tt })
	(l:<ulist A>)
	.{ (ulist_ordered lt (usort lt l)) = tt }
  := truei.
