Include trusted "char.g".
Include "ulist.g".

Define string := <ulist char>.
Define stringn := (unil char).
Define stringc := (ucons char).
Define stringln := (ucons char '\n' (inc string stringn)).
Define string_app := fun(^#owned s1:string)(s2:string). (uappend char s1 s2).
Define string_app1 := fun(s1 s2:string). let ret = (uappend char (inspect string s1) s2) in do (dec string s1) ret end.
Define string_appnl := fun(s1:string)(s2:string).
                         (string_app1 (stringc Cnl s1) s2).
Define stringeq := (equlist char eqchar).

Define string_mem := (ulist_mem char eqchar).

Define stringeqEq : Forall(s1 s2:string)(u: {(stringeq s1 s2) = tt}).
                      { s1 = s2 } :=
  foralli(s1 s2:string).
    [equlistEq char s1 s2 eqchar eqchar_tot eqchar_eq].

Define stringeqTot := 
  foralli(s1 s2:string).[equlist_total char eqchar eqchar_tot s1 s2].

Define char_range
 : Fun(c1 c2 : char)(u : { (le (which_char c1) (which_char c2)) = tt }). string :=
fun char_range(c1 c2 : char)(u : { (le (which_char c1) (which_char c2)) = tt }): <ulist char>.
  match (eqchar c1 c2) by v ign with
    ff => abbrev c1_lt_c2 = [eqnat_ff_implies_lt (which_char c1) (which_char c2) 
                              [to_nat_neq1 charlen c1 c2 v] u] in
          abbrev c1_lt_CLast = [ltle_trans (which_char c1) (which_char c2) (which_char CLast)
                                 c1_lt_c2 [chars_bounded2 c2]] in
          (stringc c1 (char_range (char_inc1 c1 c1_lt_CLast) c2
                            trans cong (le * (which_char c2)) [char_inc1_lem c1 c1_lt_CLast]
                                 [lt_S_le (which_char c1) (which_char c2) c1_lt_c2]))
  | tt => stringn
  end.

Define trusted char_range_member
   : Forall (c1 d c2:char)(u:{(le (which_char c1) (which_char c2)) = tt})
            (u1 : { (le c1 d) = tt })(u2: {(le d c2) = tt}).
       { (string_mem d (char_range c1 c2)) = tt } := truei.

Define all_chars := (char_range Cc0 CLast [chars_bounded2 Cc0]).

%=============================================================================
% convert string number to word
%=============================================================================
Define string_num_to_word_h := 
	fun string_num_to_word_h(s : string)(w : word) : word.
	match s with
		unil char => w
	|	ucons char c s' =>
		let w1 = (char_num_to_word c) in
		let w2 = (word_plus (word_mult w 0xa) w1) in
		(string_num_to_word_h s' w2)
	end.

Define string_num_to_word :=
	fun(s : string) : word.
	(string_num_to_word_h s 0x0).

%=============================================================================
% convert word number to string
%=============================================================================
Define word_num_to_string_h :=
	fun word_num_to_string_h(w : word)(s : string) : string.
	match (not (eqword w 0x0)) with
		ff => s
	|	tt =>
		let w1 = (word_mod10 w) in
		let w2 = (word_div10 w) in
		let c1 = (word_num_to_char w1) in
		(word_num_to_string_h w2 (ucons char c1 s))
	end.

Define word_num_to_string :=
	fun(w : word) : string.
	match (not (eqword w 0x0)) with
		ff => (ucons char '0' (unil char))
	|	tt => (word_num_to_string_h w (unil char))
	end.
	

%=============================================================================
% more formatting functions
%=============================================================================

Define inc_word_by_nat := fun inc_word_by_nat(w:word)(^#owned n:nat) : word.
	match n with
		Z => w
	| S n' =>
			let w' = (word_inc2 w) in
			(inc_word_by_nat w' n')
	end.

Define natToString := fun(^n:nat) : string.
	let w = (inc_word_by_nat word0 (inspect nat n)) in
	do
	(consume_unowned nat n)
	(word_num_to_string w)
	end.

Define natToString' := fun(!n:nat) : string.
	let w = (inc_word_by_nat word0 (inspect nat n)) in
	(word_num_to_string w).
