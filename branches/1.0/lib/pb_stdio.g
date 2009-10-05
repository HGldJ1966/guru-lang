Include trusted "stdio.g".

% define a type for "pushback stdio"
Define pb_in_t : type := <ulist <pair char stdio_t>>.

Define pb_inn := (unil <pair char stdio_t>).
Define pb_inc := (ucons <pair char stdio_t>).

Define primitive pb_in : #unique_point pb_in_t <<END
  #define gpb_in 0
END.

Define pb_in_app : Fun(! #unique_point l : pb_in_t)(! #unique_point sin : stdio_t)(c : char) . pb_in_t :=
	fun(! #unique_point l : pb_in_t)(! #unique_point sin : stdio_t)(c : char).
		(ucons <pair char stdio_t> (mkpair char stdio_t c sin) l).

Define pb_in_rm : Fun(! #unique_point l : pb_in_t) . pb_in_t :=
	fun(! #unique_point l : pb_in_t).
	match l with
		unil _ => l
	|	ucons _ p l' => l'
	end.

Define pb_cur_char : Fun(! #unique_point l : pb_in_t)(! #unique_point sin : stdio_t) . #untracked char :=
	fun(! #unique_point l : pb_in_t)(! #unique_point sin : stdio_t).
	match l with
		unil _ => (cur_char sin)
	|	ucons _ p l' => let l = (pb_in_rm l) in (fst char stdio_t p)
	end.

% like skip?
Define pb_next_char : Fun(#unique_point l : pb_in_t) . #unique_point pb_in_t :=
	fun(#unique_point l : pb_in_t).
	match l with
		unil _ => l
	|	ucons _ p l' => l'
	end.

Define pb_pushback : Fun(! #unique_point l : pb_in_t)(! #unique_point sin : stdio_t)(c : char) . pb_in_t :=
	fun(! #unique_point l : pb_in_t)(! #unique_point sin : stdio_t)(c : char).
		(pb_in_app l sin c).

%-
%Another version

Define pb_cur_char : Fun(l : pb_in_t)(sin : stdio_t) . <pair char pb_in_t> :=
        fun(l : pb_in_t)(sin : stdio_t).
        match l with
                unil _ => (mkpair char pb_in_t (cur_char sin) l)
        |       ucons _ p l' => (mkpair char pb_in_t (fst char stdio_t p) l')
        end.

Define pb_next_char : Fun(l : pb_in_t)(sin : stdio_t) . <pair char pb_in_t> :=
	fun(l : pb_in_t)(sin : stdio_t).
	match l with
		unil _ => (mkpair char pb_in_t (cur_char (next_char sin)) l)
	|	ucons _ p l' => (pb_cur_char l' sin)
	end.

Define pb_pushback : Fun(c : char)(sin : stdio_t)(l : pb_in_t) . pb_in_t :=
	fun(c : char)(sin : stdio_t)(l : pb_in_t).
		(pb_in_app c sin l).
-%