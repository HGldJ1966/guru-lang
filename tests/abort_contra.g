Include "../lib/bool.g".

% "assert" is a partial function that may abort
Define assert :=
	fun(b:bool).
	match b with
		ff => abort bool
	| tt => tt
	end.

% this lemma is to say when you observe "assert" is true, the argument
% must be true.
Define assert_tt :
  Forall(b:bool)(u:{ (assert b) = tt }).
  	{ b = tt }
  :=
  foralli(b:bool)(u:{ (assert b) = tt }).
  case b with
  	ff =>
  		contra
				trans symm u
				trans	hypjoin (assert b) abort ! by b_eq end
							clash abort ! tt
				{ b = tt }
  | tt => b_eq
  end
  .

% more general form might not care about the return value
% this could be proved by induction when we have the one above
% but, native support would save some efforts of users
Define assert_terminates :
  Forall(b b':bool)(u:{ (assert b) = b' }).
  	{ b = tt }
  :=
  foralli(b:bool)(u:{ (assert b) = tt }).
  case b with
  	ff =>
  		contra
				trans symm u
				trans	hypjoin (assert b) abort ! by b_eq end
							clash abort ! b'
				{ b = tt }
  | tt => b_eq
  end
  .
