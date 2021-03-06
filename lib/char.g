Include "bool.g".
Include "unit.g".
Include "pow.g".
Include "bv.g".
Include "minus.g".

% number of bits per character
Define charlen := (S (S (S (S (S (S (S Z))))))).

% number of characters.
Define num_chars := (pow2 charlen).

Define num_chars_not_Z := [pow_not_zero (S (S Z)) charlen clash (S (S Z)) Z].

Define spec char := <bv charlen>.

Untracked char.

Define spec mkchar : Fun(b6 b5 b4 b3 b2 b1 b0:bool).char := 
  fun (b6 b5 b4 b3 b2 b1 b0:bool).
    (bvc (S (S (S (S (S (S Z)))))) b6
    (bvc (S (S (S (S (S Z))))) b5
    (bvc (S (S (S (S Z)))) b4
    (bvc (S (S (S Z))) b3
    (bvc (S (S Z)) b2
    (bvc (S Z) b1
    (bvc Z b0 bvn))))))).

Define Cc0 : char := (mkchar ff ff ff ff ff ff ff). 
Define Cc1 : char := (mkchar tt ff ff ff ff ff ff). 
Define Cc2 : char := (mkchar ff tt ff ff ff ff ff). 
Define Cc3 : char := (mkchar tt tt ff ff ff ff ff). 
Define Cc4 : char := (mkchar ff ff tt ff ff ff ff). 
Define Cc5 : char := (mkchar tt ff tt ff ff ff ff). 
Define Cc6 : char := (mkchar ff tt tt ff ff ff ff). 
Define Cc7 : char := (mkchar tt tt tt ff ff ff ff). 
Define Cc8 : char := (mkchar ff ff ff tt ff ff ff). 
Define Cc9 : char := (mkchar tt ff ff tt ff ff ff).  % tab
Define C10 : char := (mkchar ff tt ff tt ff ff ff). 
Define C11 : char := (mkchar tt tt ff tt ff ff ff). 
Define C12 : char := (mkchar ff ff tt tt ff ff ff). 
Define C13 : char := (mkchar tt ff tt tt ff ff ff).  % carriage return
Define C14 : char := (mkchar ff tt tt tt ff ff ff). 
Define C15 : char := (mkchar tt tt tt tt ff ff ff). 
Define C16 : char := (mkchar ff ff ff ff tt ff ff). 
Define C17 : char := (mkchar tt ff ff ff tt ff ff). 
Define C18 : char := (mkchar ff tt ff ff tt ff ff). 
Define C19 : char := (mkchar tt tt ff ff tt ff ff). 
Define C20 : char := (mkchar ff ff tt ff tt ff ff). 
Define C21 : char := (mkchar tt ff tt ff tt ff ff). 
Define C22 : char := (mkchar ff tt tt ff tt ff ff). 
Define C23 : char := (mkchar tt tt tt ff tt ff ff). 
Define C24 : char := (mkchar ff ff ff tt tt ff ff). 
Define C25 : char := (mkchar tt ff ff tt tt ff ff). 
Define C26 : char := (mkchar ff tt ff tt tt ff ff). 
Define C27 : char := (mkchar tt tt ff tt tt ff ff). 
Define C28 : char := (mkchar ff ff tt tt tt ff ff). 
Define C29 : char := (mkchar tt ff tt tt tt ff ff). 
Define C30 : char := (mkchar ff tt tt tt tt ff ff). 
Define C31 : char := (mkchar tt tt tt tt tt ff ff). 
Define Csp : char := (mkchar ff ff ff ff ff tt ff). % ' '
Define Cba : char := (mkchar tt ff ff ff ff tt ff). % '!'
Define Cdq : char := (mkchar ff tt ff ff ff tt ff). % '"'
Define Cpo : char := (mkchar tt tt ff ff ff tt ff). % '#'
Define Cdo : char := (mkchar ff ff tt ff ff tt ff). % '$'
Define Cpe : char := (mkchar tt ff tt ff ff tt ff). % '%'
Define Cam : char := (mkchar ff tt tt ff ff tt ff). % '&'
Define Csq : char := (mkchar tt tt tt ff ff tt ff). % '''
Define Clp : char := (mkchar ff ff ff tt ff tt ff). % '('
Define Crp : char := (mkchar tt ff ff tt ff tt ff). % ')'
Define Cst : char := (mkchar ff tt ff tt ff tt ff). % '*'
Define Cpl : char := (mkchar tt tt ff tt ff tt ff). % '+'
Define Cco : char := (mkchar ff ff tt tt ff tt ff). % ','
Define Cmi : char := (mkchar tt ff tt tt ff tt ff). % '-'
Define Cpr : char := (mkchar ff tt tt tt ff tt ff). % '.'
Define Csl : char := (mkchar tt tt tt tt ff tt ff). % '/'
Define C0 : char := (mkchar ff ff ff ff tt tt ff). % '0'
Define C1 : char := (mkchar tt ff ff ff tt tt ff). % '1'
Define C2 : char := (mkchar ff tt ff ff tt tt ff). % '2'
Define C3 : char := (mkchar tt tt ff ff tt tt ff). % '3'
Define C4 : char := (mkchar ff ff tt ff tt tt ff). % '4'
Define C5 : char := (mkchar tt ff tt ff tt tt ff). % '5'
Define C6 : char := (mkchar ff tt tt ff tt tt ff). % '6'
Define C7 : char := (mkchar tt tt tt ff tt tt ff). % '7'
Define C8 : char := (mkchar ff ff ff tt tt tt ff). % '8'
Define C9 : char := (mkchar tt ff ff tt tt tt ff). % '9'
Define Ccl : char := (mkchar ff tt ff tt tt tt ff). % ':'
Define Cse : char := (mkchar tt tt ff tt tt tt ff). % ';'
Define Clt : char := (mkchar ff ff tt tt tt tt ff). % '<'
Define Ceq : char := (mkchar tt ff tt tt tt tt ff). % '='
Define Cgt : char := (mkchar ff tt tt tt tt tt ff). % '>'
Define Cqu : char := (mkchar tt tt tt tt tt tt ff). % '?'
Define Cat : char := (mkchar ff ff ff ff ff ff tt). % '@'
Define CA : char := (mkchar tt ff ff ff ff ff tt). % 'A'
Define CB : char := (mkchar ff tt ff ff ff ff tt). % 'B'
Define CC : char := (mkchar tt tt ff ff ff ff tt). % 'C'
Define CD : char := (mkchar ff ff tt ff ff ff tt). % 'D'
Define CE : char := (mkchar tt ff tt ff ff ff tt). % 'E'
Define CF : char := (mkchar ff tt tt ff ff ff tt). % 'F'
Define CG : char := (mkchar tt tt tt ff ff ff tt). % 'G'
Define CH : char := (mkchar ff ff ff tt ff ff tt). % 'H'
Define CI : char := (mkchar tt ff ff tt ff ff tt). % 'I'
Define CJ : char := (mkchar ff tt ff tt ff ff tt). % 'J'
Define CK : char := (mkchar tt tt ff tt ff ff tt). % 'K'
Define CL : char := (mkchar ff ff tt tt ff ff tt). % 'L'
Define CM : char := (mkchar tt ff tt tt ff ff tt). % 'M'
Define CN : char := (mkchar ff tt tt tt ff ff tt). % 'N'
Define CO : char := (mkchar tt tt tt tt ff ff tt). % 'O'
Define CP : char := (mkchar ff ff ff ff tt ff tt). % 'P'
Define CQ : char := (mkchar tt ff ff ff tt ff tt). % 'Q'
Define CR : char := (mkchar ff tt ff ff tt ff tt). % 'R'
Define CS : char := (mkchar tt tt ff ff tt ff tt). % 'S'
Define CT : char := (mkchar ff ff tt ff tt ff tt). % 'T'
Define CU : char := (mkchar tt ff tt ff tt ff tt). % 'U'
Define CV : char := (mkchar ff tt tt ff tt ff tt). % 'V'
Define CW : char := (mkchar tt tt tt ff tt ff tt). % 'W'
Define CX : char := (mkchar ff ff ff tt tt ff tt). % 'X'
Define CY : char := (mkchar tt ff ff tt tt ff tt). % 'Y'
Define CZ : char := (mkchar ff tt ff tt tt ff tt). % 'Z'
Define Clb : char := (mkchar tt tt ff tt tt ff tt). % '['
Define Cbs : char := (mkchar ff ff tt tt tt ff tt). % '\'
Define Crb : char := (mkchar tt ff tt tt tt ff tt). % ']'
Define Cha : char := (mkchar ff tt tt tt tt ff tt). % '^'
Define Cun : char := (mkchar tt tt tt tt tt ff tt). % '_'
Define Cfq : char := (mkchar ff ff ff ff ff tt tt). % '`'
Define Ca : char := (mkchar tt ff ff ff ff tt tt). % 'a'
Define Cb : char := (mkchar ff tt ff ff ff tt tt). % 'b'
Define Cc : char := (mkchar tt tt ff ff ff tt tt). % 'c'
Define Cd : char := (mkchar ff ff tt ff ff tt tt). % 'd'
Define Ce : char := (mkchar tt ff tt ff ff tt tt). % 'e'
Define Cf : char := (mkchar ff tt tt ff ff tt tt). % 'f'
Define Cg : char := (mkchar tt tt tt ff ff tt tt). % 'g'
Define Ch : char := (mkchar ff ff ff tt ff tt tt). % 'h'
Define Ci : char := (mkchar tt ff ff tt ff tt tt). % 'i'
Define Cj : char := (mkchar ff tt ff tt ff tt tt). % 'j'
Define Ck : char := (mkchar tt tt ff tt ff tt tt). % 'k'
Define Cl : char := (mkchar ff ff tt tt ff tt tt). % 'l'
Define Cm : char := (mkchar tt ff tt tt ff tt tt). % 'm'
Define Cn : char := (mkchar ff tt tt tt ff tt tt). % 'n'
Define Co : char := (mkchar tt tt tt tt ff tt tt). % 'o'
Define Cp : char := (mkchar ff ff ff ff tt tt tt). % 'p'
Define Cq : char := (mkchar tt ff ff ff tt tt tt). % 'q'
Define Cr : char := (mkchar ff tt ff ff tt tt tt). % 'r'
Define Cs : char := (mkchar tt tt ff ff tt tt tt). % 's'
Define Ct : char := (mkchar ff ff tt ff tt tt tt). % 't'
Define Cu : char := (mkchar tt ff tt ff tt tt tt). % 'u'
Define Cv : char := (mkchar ff tt tt ff tt tt tt). % 'v'
Define Cw : char := (mkchar tt tt tt ff tt tt tt). % 'w'
Define Cx : char := (mkchar ff ff ff tt tt tt tt). % 'x'
Define Cy : char := (mkchar tt ff ff tt tt tt tt). % 'y'
Define Cz : char := (mkchar ff tt ff tt tt tt tt). % 'z'
Define Clc : char := (mkchar tt tt ff tt tt tt tt). % '{'
Define Cbr : char := (mkchar ff ff tt tt tt tt tt). % '|'
Define Crc : char := (mkchar tt ff tt tt tt tt tt). % '}'
Define Cti : char := (mkchar ff tt tt tt tt tt tt). % '~'
Define Cdel : char := (mkchar tt tt tt tt tt tt tt).

Define CLast : char := Cdel.

Define Cnl : char := C10.

Define spec eqchar : Fun(c1 c2:char).bool := (eqbv charlen).

Define is_whitespace :=
 fun(a:char).
   (or (eqchar a Cnl)
   (or (eqchar a Csp) 
   (or (eqchar a Cc9)
       (eqchar a C13)))).

Define spec print_char := fun(c:char).unit.

Inductive char_inc_t : type :=
  mk_char_inc_t : Fun(c:char)(carry:bool).char_inc_t.

Define spec char_inc :=
  fun(c:char).
    let r = (bv_inc charlen c) in
    match r with
      mk_bv_inc_t l' v' carry => 
        (mk_char_inc_t cast v' by cong <bv *> symm inj <bv_inc_t *> r_Eq 
           carry)
      end.

Define char_inc_tot : Forall(c:char).Exists(r:char_inc_t).{(char_inc c) = r} :=
  foralli(c:char).
    existse [bv_inc_tot charlen c]
    foralli(r:<bv_inc_t charlen>)
           (ur:{(bv_inc c) = r}).
    case r with
      mk_bv_inc_t l' v' carry =>
      existsi (mk_char_inc_t cast v' by cong <bv *> symm inj <bv_inc_t *> r_Eq 
                  carry) 
        { (char_inc c) = * }
      hypjoin (char_inc c) (mk_char_inc_t v' carry)
      by ur r_eq end
    end.

Define spec which_char : Fun(c:char).nat := (to_nat charlen). 

Define eqchar_tot : Forall(c1 c2:char).Exists(b:bool).
                         { (eqchar c1 c2) = b } := 
  [eqbv_tot charlen].

Define eqchar_eq : Forall(c1 c2:char)(u:{(eqchar c1 c2) = tt}).
                   { c1 = c2 } := 
  [eqbv_eq charlen].

Define chars_bounded
 : Forall(c:char). { (lt (which_char c) num_chars) = tt } :=
   foralli(c:char). [lt_to_nat charlen c].  

Define chars_bounded2
 : Forall(c:char). { (le (which_char c) (which_char CLast)) = tt } :=
   foralli(c:char).
   [lt_pred
      terminates (which_char CLast) by to_nat_tot
      terminates num_chars by pow_total
      terminates (which_char c) by to_nat_tot
      join num_chars (S (which_char CLast))
      [chars_bounded c]].

Define char_inc_notfull
  : Forall(c d:char)(carry:bool)
          (u1: { (lt (which_char c) (to_nat CLast)) = tt})
          (u2: { (char_inc c) = (mk_char_inc_t d carry) }).
     { carry = ff } :=
  foralli(c d:char)(carry:bool)
         (u1: { (lt (which_char c) (to_nat CLast)) = tt})
         (u2: { (char_inc c) = (mk_char_inc_t d carry) }).
  abbrev r = terminates (bv_inc spec charlen c) by bv_inc_tot in
  case r with
    mk_bv_inc_t l' v' carry' =>
    abbrev P = 
       trans symm u2
         hypjoin (char_inc c) (mk_char_inc_t v' carry')
         by r_eq end in
    abbrev carry_eq = inj (mk_char_inc_t ** *) P in
    trans carry_eq
      [bv_inc_notfull charlen c 
         cast v' by cong <bv *> symm inj <bv_inc_t *> r_Eq 
         carry' trans cong (lt (which_char c) (to_nat *)) 
                         join (bv_full charlen) (CLast) 
                  u1
         r_eq]
  end.

Define char_inc_lt 
  : Forall(c d next:char)(carry:bool)
          (u1: { (lt (which_char c) (which_char d)) = tt})
          (u2: { (char_inc c) = (mk_char_inc_t next carry) }).
     { carry = ff } := 
  foralli(c d next:char)(carry:bool)
         (u1: { (lt (which_char c) (which_char d)) = tt})
         (u2: { (char_inc c) = (mk_char_inc_t next carry) }).
    [char_inc_notfull c next carry 
       [ltle_trans
          terminates (which_char c) by to_nat_tot
          terminates (which_char d) by to_nat_tot
          terminates (which_char CLast) by to_nat_tot
          u1 [chars_bounded2 d]]
       u2].

Define to_nat_char_inc : Forall(c d:char)(carry:bool)
                             (u: { (char_inc c) = (mk_char_inc_t d carry) }).
                             { (S (to_nat c)) = (condplus carry (pow2 charlen)
                                                  (to_nat d)) } :=
   foralli(c d:char)(carry:bool)
          (u: { (char_inc c) = (mk_char_inc_t d carry) }).
   abbrev r = terminates (bv_inc spec charlen c) by bv_inc_tot in
     case r with
       mk_bv_inc_t l' v' carry' =>
       abbrev P = trans hypjoin (mk_char_inc_t v' carry') (char_inc c)
                        by r_eq end
                    u in
       trans
         [to_nat_bv_inc charlen c 
            cast v' by cong <bv *> symm inj <bv_inc_t *> r_Eq
            carry' r_eq]
       trans
         cong (condplus * (pow2 charlen) (to_nat v'))
           inj (mk_char_inc_t ** *) P
         cong (condplus carry (pow2 charlen) (to_nat *))
           inj (mk_char_inc_t * **) P
     end.

Define minus_which_char_Z :
  Forall(c d:char)(m:{(minus (which_char c) (which_char d)) = Z}).
    { c = d } :=
  foralli(c d:char)(m:{(minus (which_char c) (which_char d)) = Z}).
    [to_nat_inj charlen c d
      [minus_eq_Z 
         terminates (which_char c) by to_nat_tot
         terminates (which_char d) by to_nat_tot
         m]].
