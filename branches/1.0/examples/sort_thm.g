Include "sort.g".

%=============================================================================
% monotone predicate (ulist)
% true if the list is (partial-)ordered
% e.g: 0 < 1 < 3 < 9
% the input predicate "lt" means "less than", but can be reflecxive.
% note that "lt" does not have to be globally transitive
% but, monotone only if it is transitive for those items in the list
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

Define ulist_monotone := fun ulist_monotone
	(A:type)
	(lt:Fun(a b:A).bool)
	(l:<ulist A>)
	: bool.
  match l with
    unil _ => tt		% empty list is always monotone
  | ucons _ a l' =>
      match (ulist_lt_each A lt a l') with
        ff => ff
      | tt => (ulist_monotone A lt l')
      end
  end.
