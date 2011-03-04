Include trusted "../lib/stdio.g".
Include trusted "../lib/uwarray.g".
Include "sort.g".

%=============================================================================
% ulist helpers
%=============================================================================

Define ufilter2 := fun ufilter2
	(A C D:type)
	(f:Fun(^#owned c:C)(!#unique_owned d:D)(#untracked a:A).bool)
	(^#owned c:C)
	(!#unique_owned d:D)
	(^#owned l:<ulist A>)
	: <ulist A> .
    match l with
       unil _ => (unil A)
    | ucons _ a l' => match (f (clone_owned C c) d a) with 
                       ff => (ufilter2 A C D f c d l')
                     | tt => (ucons A a (ufilter2 A C D f c d l'))
                     end
    end.

Define ufilter_qu := fun ufilter_qu
	(A C D:type)
	(f:Fun(!#unique_owned c:C)(#untracked d:D)(#untracked a:A).bool)
	(!#unique_owned c:C)
	(#untracked d:D)
	(^#owned l:<ulist A>)
	: <ulist A> .
    match l with
       unil _ => (unil A)
    | ucons _ a l' => match (f c d a) with 
                       ff => (ufilter_qu A C D f c d l')
                     | tt => (ucons A a (ufilter_qu A C D f c d l'))
                     end
    end.


%=============================================================================
% merge sort (ulist) by comparison with additional context information
%=============================================================================

Inductive usort2_ctxt_t : Fun(A C D:type).type :=
	usort2_ctxt : Fun(A C D:type)(f:Fun(^#owned c:C)(!#unique_owned d:D)(#untracked x y:A).bool)
									 (^#owned c:C)(#untracked p:A). <usort2_ctxt_t A C D>.

Define usort2 := fun usort2
	(A C D:type)
	(lt:Fun(^#owned c:C)(!#unique_owned d:D)(#untracked a b:A).bool)
	(^#owned c:C)
	(^#unique_owned d:D)
	(^#owned l:<ulist A>)
	: <ulist A>.
  match l with
    unil _ =>
    	do
    	(consume_owned <ulist A> l)
    	(unil A)
    	end
  | ucons _ p xs =>
  		abbrev C' = <usort2_ctxt_t A C D> in
			abbrev lte_p = fun(^#owned c':C')(!#unique_owned d:D)(#untracked x:A).
				match c' with usort2_ctxt _ _ _ lt c p => (not (lt c d p x)) end in
			abbrev gt_p = fun(^#owned c':C')(!#unique_owned d:D)(#untracked x:A).
				match c' with usort2_ctxt _ _ _ lt c p => (lt c d p x) end in
			
			let c' = (usort2_ctxt A C D lt c p) in
      let	l1 = (ufilter2 A C' D lte_p (inspect C' c') d (clone_owned <ulist A> xs)) in
      let l2 = (ufilter2 A C' D gt_p (inspect C' c') d xs) in
      let l1' = (usort2 A C D lt c d (inspect <ulist A> l1)) in
      let l2' = (usort2 A C D lt c d (inspect <ulist A> l2)) in
      let rval = (uappend A (inspect <ulist A> l1') (ucons A p l2')) in
      do
      (consume_unowned C c)
      (consume_unowned <ulist A> l1)
      (consume_unowned <ulist A> l2)
      (consume_unowned <ulist A> l1')
      rval
      end
  end.

Inductive usort_u_ctxt_t : Fun(A C:type).type :=
	usort_u_ctxt : Fun(A C:type)(f:Fun(!#unique_owned c:C)(#untracked x y:A).bool)
									 (#untracked p:A). <usort_u_ctxt_t A C>.

Define usort_q := fun usort_q
	(A C:type)
	(lt:Fun(!#unique_owned c:C)(#untracked a b:A).bool)
	(^#unique_owned c:C)
	(^#owned l:<ulist A>)
	: <ulist A>.
  match l with
    unil _ =>
    	do
    	(consume_owned <ulist A> l)
    	(unil A)
    	end
  | ucons _ p xs =>
  		abbrev C' = <usort_u_ctxt_t A C>  in
			abbrev lte_p = fun(^#owned c':C')(!#unique_owned c:C)(#untracked x:A).
				match c' with usort_u_ctxt _ _ lt p => (not (lt c p x)) end in
			abbrev gt_p = fun(^#owned c':C')(!#unique_owned c:C)(#untracked x:A).
				match c' with usort_u_ctxt _ _ lt p => (lt c p x) end in
			
			let c' = (usort_u_ctxt A C lt p) in
      let	l1 = (ufilter2 A C' C lte_p (inspect C' c') c (clone_owned <ulist A> xs)) in
      let rval = l1 in
      let l2 = (ufilter2 A C' C gt_p (inspect C' c') c xs) in
      let l1' = (usort_q A C lt (clone_unique_owned C c) (inspect <ulist A> l1)) in
      let l2' = (usort_q A C lt c (inspect <ulist A> l2)) in
      let rval = (uappend A (inspect <ulist A> l1') (ucons A p l2')) in
      do
      (consume_unowned C' c')
      (consume_unowned <ulist A> l1)
      (consume_unowned <ulist A> l2)
      (consume_unowned <ulist A> l1')
      rval
      end
  end.

%=============================================================================
% The main function
%=============================================================================

Define print_space := fun
  fun(#unique_point io:stdio_t) : #unique_point stdio_t.
  (print_char io ' ').

% a little helper function
Define _set_val := fun
  (n:word)(#unique a:<uwarray word n>)
  (i:word)(w:word)
  :#unique <uwarray word n>.
  % [assert] (ltword i n)
  match (ltword i n) by q1 _ with ff => abort <uwarray word n> | tt =>
  (uwarray_set word n a i w q1)
  end.

Define sample_list :=
  % some random values
  (ucons word 0x3
	(ucons word 0x1
	(ucons word 0x0
	(ucons word 0x2
	(ucons word 0x4
		(unil word)))))).

Define sample_array_len := 0x5.
Define sample_array :=
  abbrev len = sample_array_len in
  
  % create an array (initialized with zeros)
  let a = (uwarray_new word len 0x0) in
  
  % set some random values
  %                       idx val
  % ----------------------------------------------------------------
  let a = (_set_val len a 0x0 0x4) in
  let a = (_set_val len a 0x1 0x2) in
  let a = (_set_val len a 0x2 0x3) in
  let a = (_set_val len a 0x3 0x1) in
  let a = (_set_val len a 0x4 0x5) in
  a.

Define lookup := fun(!#unique_owned a:<uwarray word sample_array_len>)(w:word).
	match (ltword w sample_array_len) by q1 _ with ff => abort word | tt =>
	(uwarray_get word sample_array_len a w q1)
	end.

Define main :=
  abbrev l = sample_list in
  abbrev D = <uwarray word sample_array_len> in
  abbrev d = sample_array in
	abbrev comp = fun(!#unique_owned t:D)(a b:word).
		let va = (lookup t a) in
		let vb = (lookup t b) in
		(ltword va vb)
		in
  let l' = (usort_q word D comp (inspect_unique D d) (inspect <ulist word> l)) in
  
  let stdio = (print_string stdio "Vars: ") in
  let stdio = (print_ulist stdio word print_word print_space l) in
  let stdio = (print_char stdio '\n') in

  let stdio = (print_string stdio "Vals: ") in
  let stdio = (print_uwarray stdio word print_word print_space sample_array_len d) in
  let stdio = (print_string stdio " (array indexed by variable number)\n") in
  
  let stdio = (print_string stdio "--- sorted by value ---\n") in

  let stdio = (print_ulist stdio word print_word print_space l') in
  let stdio = (print_char stdio '\n') in
  
  (consume_unique_point stdio_t stdio)
  .

Compile main to "sort_example2.c".
