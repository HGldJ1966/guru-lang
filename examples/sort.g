Include trusted "../lib/ulist.g".

%=============================================================================
% ulist helpers
%=============================================================================

Define ufilter := fun ufilter
	(A C:type)
	(^#owned c:C)
	(f:Fun(^#owned c:C)(#untracked a:A).bool)
	(^#owned l:<ulist A>)
	: <ulist A> .
    match l with
       unil _ => (unil A)
    | ucons _ a l' => match (f (clone_owned C c) a) with 
                       ff => (ufilter A C c f l')
                     | tt => (ucons A a (ufilter A C c f l'))
                     end
    end.


%=============================================================================
% merge sort (ulist)
%=============================================================================

Inductive usort_ctxt_t : Fun(A:type).type :=
	usort_ctxt : Fun(A:type)(f:Fun(#untracked a b:A).bool)(#untracked p:A).<usort_ctxt_t A>.

Define usort := fun usort
	(A:type)
	(lt:Fun(#untracked a b:A).bool)
	(^#owned l:<ulist A>)
	: <ulist A>.
  match l with
    unil _ =>
    	do
    	(consume_owned <ulist A> l)
    	(unil A)
    	end
  | ucons _ p xs =>
  		abbrev C = <usort_ctxt_t A> in
			abbrev lte_p = fun(^#owned c:C)(#untracked x:A).
				match c with usort_ctxt _ lt p => (not (lt p x)) end in
			abbrev gt_p = fun(^#owned c:C)(#untracked x:A).
				match c with usort_ctxt _ lt p => (lt p x) end in
			
			let c = (usort_ctxt A lt p) in
      let	l1 = (ufilter A C (inspect C c) lte_p (clone_owned <ulist A> xs)) in
      let l2 = (ufilter A C (inspect C c) gt_p xs) in
      let l1' = (usort A lt (inspect <ulist A> l1)) in
      let l2' = (usort A lt (inspect <ulist A> l2)) in
      let rval = (uappend A (inspect <ulist A> l1') (ucons A p l2')) in
      do
      (consume_unowned C c)
      (consume_unowned <ulist A> l1)
      (consume_unowned <ulist A> l2)
      (consume_unowned <ulist A> l1')
      rval
      end
  end.
