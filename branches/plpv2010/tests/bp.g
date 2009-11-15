%Set "print_parsed".
Include "../lib/stdio.g".

%Set "Debug_compiler".

%Set "debug_check_refs".

Define check_parens := 
  fun check_parens(unique stdin:stdin_t)(num_open:nat):bool.
    match (next_char stdin) with
      getc_none stdin => 
        dec stdin
        match num_open with
          Z => tt
        | S n => dec n ff
        end
    | getc_char a stdin =>
        match (eqchar Clp a) with
          ff => match (eqchar Crp a) with
                  ff => (check_parens stdin num_open)
                | tt => match num_open with
                          Z => dec stdin ff
                        | S n' => (check_parens stdin n')
                        end
                end
        | tt => (check_parens stdin (S num_open))
        end
    end.

Define thm1 : Forall(l:stdin_t)(n:nat)
                    (u:{ (check_parens l n) = tt }).
                    { (length (filter l (eqchar Crp))) =
                      (plus n (length (filter l (eqchar Clp)))) } :=
  induction(l:stdin_t) by ul vl IH 
  return Forall(n:nat)
               (u:{ (check_parens l n) = tt }).
               { (length (filter l (eqchar Crp))) =
                 (plus n (length (filter l (eqchar Clp)))) } with
    nil A' => 
      induction(n:nat) by un vn ign 
      return Forall(u:{ (check_parens l n) = tt }).
                   { (length (filter l (eqchar Crp))) =
                     (plus n (length (filter l (eqchar Clp)))) } with
        Z => foralli(u:{ (check_parens l n) = tt }).
                hypjoin (length (filter l (eqchar Crp)))
                        (plus n (length (filter l (eqchar Clp))))
                by ul un end
      | S n' => foralli(u:{ (check_parens l n) = tt }).
                contra
                  trans
                    trans symm u
                    trans cong (check_parens * n) ul
                    trans cong (check_parens (nil !) *) un
                          join (check_parens (nil !) (S n'))
                               ff
                  clash ff tt
                { (length (filter l (eqchar Crp))) =
                     (plus n (length (filter l (eqchar Clp)))) }
      end
  | cons A' a' l' => 
      abbrev P = symm inj <list *> vl in
      abbrev a = cast a' by P in
      abbrev cl' = cast l' by symm vl in
      foralli(n:nat)(u:{ (check_parens l n) = tt }).
      abbrev F = { (length (filter l (eqchar Crp))) =
                   (plus n (length (filter l (eqchar Clp)))) } in
        existse [eqchar_tot Clp a] 
        induction(blp:bool) by u1 ign ign1 return 
          Forall(alp : { (eqchar Clp a) = blp }).F with
          ff => 
            foralli(alp : { (eqchar Clp a) = blp }).
            abbrev alpv = trans alp u1 in
            existse cinv (eqchar Clp) 
               trans symm cong (* a) eval (eqchar Clp) alpv
             foralli(Elp:Fun(c:char).bool)(Elpu:{(eqchar Clp) = Elp}).
             abbrev Alpv = trans cong (* a) symm Elpu alpv in
             abbrev skiplp = trans cong (filter cl' *) Elpu
                             trans symm [filter_skip char a cl' Elp
                                          Alpv]
                             trans symm cong (filter * Elp) ul
                                   symm cong (filter l *) Elpu in
             existse [eqchar_tot Crp a] 
             induction(brp:bool) by u2 ign ign2 
             return Forall(arp : { (eqchar Crp a) = brp }).F with
               ff => foralli(arp : { (eqchar Crp a) = brp }).
                 abbrev arpv = trans arp u2 in
                 existse cinv (eqchar Crp) 
                    trans symm cong (* a) eval (eqchar Crp) arpv
                 foralli(Erp:Fun(c:char).bool)(Erpu:{(eqchar Crp) = Erp}).
                 abbrev Arpv = trans cong (* a) symm Erpu arpv in
                 trans cong (length *)
                         trans cong (filter l *) Erpu
                         trans cong (filter * Erp) ul
                         trans [filter_skip char a cl' Erp Arpv]
                               cong (filter cl' *) symm Erpu
                 trans [IH cl' n 
                          symm trans symm u 
                                     hypjoin (check_parens l n)
                                             (check_parens cl' n)
                                     by ul arpv alpv end]
                       cong (plus n (length *))
                            skiplp

            | tt => foralli(arp : { (eqchar Crp a) = brp }).
                    abbrev arpv = trans arp u2 in
                    [induction(nn:nat) by unn vn ign 
                     return Forall(un:{n = nn}). F with
                       Z => foralli(un:{n = nn}).
                            abbrev unv = trans un unn in
                              contra
                                trans 
                                  trans symm u
                                        hypjoin (check_parens l n)
                                                ff 
                                        by unv arpv ul alpv end
                                clash ff tt
                              F
                     | S nn' => 
                        foralli(un:{n = nn}).
                          abbrev unv = trans un unn in
                          trans hypjoin
                                  (length (filter l (eqchar Crp)))
                                  (S (length (filter cl' (eqchar Crp))))
                                by arpv alpv unv ul end
                          trans cong (S *) 
                                   trans [IH cl' nn' 
                                           symm
                                           trans symm u
                                                 hypjoin (check_parens l n)
                                                         (check_parens cl' nn')
                                                 by unv ul arpv alpv end]
                                         cong (plus nn' (length *)) skiplp
                                hypjoin (S (plus nn' (length 
                                                   (filter l (eqchar Clp)))))
                                        (plus n (length 
                                                   (filter l (eqchar Clp))))
                                by unv end
                     end
                     n join n n]
            end
        | tt => 
            foralli(alp : { (eqchar Clp a) = blp }).
            abbrev alpv = trans alp u1 in
            existse cinv (eqchar Clp) 
             trans symm cong (* a) eval (eqchar Clp) alpv
             foralli(Elp:Fun(c:char).bool)(Elpu:{(eqchar Clp) = Elp}).
              existse [filter_tot char cl' Elp 
                         foralli(a:char). 
                         existse [eqchar_tot Clp a]
                         foralli(x:bool)(ux:{(eqchar Clp a) = x}).
                           existsi x {(Elp a) = *}
                             trans cong (* a) symm Elpu
                                   ux]
              foralli(Fi:<list char>)
                     (Fiu:{ (filter char cl' Elp) = Fi}).
              existse [length_tot char Fi]
              foralli(L:nat)(Lu:{(length char Fi) = L}).
              existse [eqchar_tot Crp a]
              foralli(brp:bool)(brpu:{(eqchar Crp a) = brp}).
              existse cinv (eqchar Crp) 
                 trans symm cong (* a) eval (eqchar Crp) brpu
              foralli(Erp:Fun(a:char).bool)(Erpu:{(eqchar Crp) = Erp}).
              
              trans cong (length (filter l *)) Erpu
              trans cong (length (filter * Erp)) ul
              trans cong (length *)
                      [filter_skip char a cl' Erp
                         trans cong (Erp *) symm [eqchar_eq Clp a alpv]
                         trans cong (* Clp) symm Erpu
                               join (eqchar Crp Clp) ff]
              trans cong (length (filter cl' *)) symm Erpu
              trans [IH cl' (S n) 
                     symm trans symm u 
                                hypjoin (check_parens l n)
                                        (check_parens cl' (S n))
                                by ul alpv end]
              abbrev go = trans cong (length (filter cl' *)) Elpu
                          trans cong (length *) Fiu
                          Lu in
              trans cong (plus (S n) *) go
              trans [plusS_hop n L]
              trans cong (plus n (S *)) symm go
                    cong (plus n *)
                      hypjoin (S (length (filter cl' (eqchar Clp))))
                              (length (filter l (eqchar Clp)))
                      by ul alpv end
        end
  end.

Define test1 := join (check_parens
                        (cons Clp
                        (cons Ca
                        (cons Clp
                        (cons Cb
                        (cons Crp
                        (cons Crp (nil !))))))) Z) tt.

Define test2 := join (check_parens
                        (cons Clp
                        (cons Ca
                        (cons Clp
                        (cons Cb
                        (cons Clp
                        (cons Crp (nil !))))))) Z) ff.

Define main :=
  fun(unique stdin:stdin_t).
    let fin = fun(ret:char). let ign = (print_char ret) in 
                             let ign = (print_char Cnl) in Z
    in
    match (check_parens stdin Z) with
      ff => (fin CF)
    | tt => (fin CT)
    end.
 
Compile main to "bp.c".

%CheckTrusted.
