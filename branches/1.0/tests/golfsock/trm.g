Include "../../lib/string.g".
Include "../../lib/stdio.g".
Include "../../lib/pair.g".
Include "var.g".

Inductive trm : type :=
  sym : Fun(n:var).trm
| app : Fun(t1 t2:trm).trm
| lam : Fun(n:var)(t:trm).trm
| pi : Fun(n:var)(T1 T2:trm).trm.

Define knd := word0.
Define tp := match (word_inc knd) with
             mk_word_inc_t n carry => n end.

Define knde := (sym knd).

Define issym :=
  fun(n:var)(owned t:trm). 
    match t with
      sym n' => (eqvar n' n)
    | app t1 t2 => ff
    | lam n t1 => ff
    | pi n T1 T2 => ff
    end.

Define istp := (issym tp).

Define isknd := (issym knd).

Define issym_tot : Forall(n:var)(t:trm).Exists(b:bool).{(issym n t) = b} :=
  foralli(n:var).
  induction(t:trm) return Exists(b:bool).{(issym n t) = b} with
    sym n' => 
    abbrev r = (eqvar n' n) in
      existsi r { (issym n t) = * }
        hypjoin (issym n t) r
        by t_eq end
  | app t1 t2 => 
    existsi ff { (issym n t) = *}
      hypjoin (issym n t) ff by t_eq end
  | lam n1 t1 => 
    existsi ff { (issym n t) = *}
      hypjoin (issym n t) ff by t_eq end
  | pi n1 t1 t2 => 
    existsi ff { (issym n t) = *}
      hypjoin (issym n t) ff by t_eq end
  end.

Total issym issym_tot.

Define istp_tot := 
  foralli(t:trm). 
    existsi (issym tp t) { (istp t) = *}
    join (istp t) (issym tp t).

Total istp istp_tot.

Define isknd_tot := 
  foralli(t:trm). 
    existsi (issym knd t) { (isknd t) = *}
    join (isknd t) (issym knd t).

Total isknd isknd_tot.

%Set "debug_def_eq".
Define issymEq : Forall(n:var)(t:trm)(u:{(issym n t) = tt}).{t = (sym n)} :=
  foralli(n:var).
  induction(t:trm) return Forall(u:{(issym n t) = tt}).{t = (sym n)} with
    sym n' => 
    foralli(u:{(issym n t) = tt}).
      trans t_eq 
            cong (sym *)
             [eqvar_eq n' n
               symm
               trans symm u
                     hypjoin (issym n t) (eqvar n' n)
                     by t_eq end]
  | app t1 t2 => 
    foralli(u:{(issym n t) = tt}).
    contra
      trans
        trans symm u
              hypjoin (issym n t) ff
              by t_eq end
        clash ff tt
    { t = (sym n) }
  | lam n1 t1 => 
    foralli(u:{(issym n t) = tt}).
    contra
      trans
        trans symm u
              hypjoin (issym n t) ff
              by t_eq end
        clash ff tt
    { t = (sym n) }
  | pi n1 t1 t2 => 
    foralli(u:{(issym n t) = tt}).
    contra
      trans
        trans symm u
              hypjoin (issym n t) ff
              by t_eq end
        clash ff tt
    { t = (sym n) }
  end.

Define istpEq :=
 foralli(t:trm)(u:{(istp t) = tt}).
   [issymEq tp t trans join (istp t) (issym tp t) u].
Define iskndEq := 
 foralli(t:trm)(u:{(isknd t) = tt}).
   [issymEq knd t trans join (isknd t) (issym knd t) u].

Define eqtrm :=
  fun eqtrm(owned t1 t2:trm):bool.
  match t1 with
    sym n1 => 
    match t2 with
      default => ff
    | sym n2 => (eqvar n1 n2)
    end
  | app t1a t1b =>
    match t2 with
      default => ff
    | app t2a t2b => (and (eqtrm t1a t2a) (eqtrm t1b t2b))
    end
  | lam n1 t1a =>
    match t2 with
      default => ff
    | lam n2 t2a => (and (eqtrm t1a t2a) (eqvar n1 n2))
    end
  | pi n1 t1a t1b =>
    match t2 with
      default => ff
    | pi n2 t2a t2b => (and (and (eqtrm t1a t2a) (eqtrm t1b t2b))  
                            (eqvar n1 n2))
    end
  end.

Define eqtrm_tot : Forall(t1 t2:trm). Exists(b:bool). { (eqtrm t1 t2) = b } :=
  induction(t1:trm)
  return Forall(t2:trm). Exists(b:bool). { (eqtrm t1 t2) = b }
  with
    sym n1 =>
    foralli(t2:trm).
      case t2 with
        default => 
        existsi ff { (eqtrm t1 t2) = *}
          hypjoin (eqtrm t1 t2) ff by t1_eq t2_eq end
      | sym n2 =>
        abbrev ret = (eqvar n1 n2) in
        existsi ret { (eqtrm t1 t2) = *}
        hypjoin (eqtrm t1 t2) ret by t1_eq t2_eq end
     end
  | app t1a t1b => 
    foralli(t2:trm).
      case t2 with
        default => 
        existsi ff { (eqtrm t1 t2) = *}
        hypjoin (eqtrm t1 t2) ff by t1_eq t2_eq end
      | app t2a t2b =>
        abbrev ret = 
          terminates
            (and terminates (eqtrm t1a t2a) by [t1_IH t1a t2a]
                 terminates (eqtrm t1b t2b) by [t1_IH t1b t2b])
          by and_tot in
               
        existsi ret { (eqtrm t1 t2) = *}
        hypjoin (eqtrm t1 t2) ret by t1_eq t2_eq end
      end
  | lam n1 t1a => 
    foralli(t2:trm).
      case t2 with
        default => 
        existsi ff { (eqtrm t1 t2) = *}
        hypjoin (eqtrm t1 t2) ff by t1_eq t2_eq end
      | lam n2 t2a =>
        abbrev ret = 
          terminates
            (and terminates (eqtrm t1a t2a) by [t1_IH t1a t2a]
                 (eqvar n1 n2)) 
          by and_tot in
        existsi ret { (eqtrm t1 t2) = *}
        hypjoin (eqtrm t1 t2) ret by t1_eq t2_eq end
      end
  | pi n1 t1a t1b => 
    foralli(t2:trm).
      case t2 with
        default => 
        existsi ff { (eqtrm t1 t2) = *}
        hypjoin (eqtrm t1 t2) ff by t1_eq t2_eq end
      | pi n2 t2a t2b =>
        abbrev ret = 
        terminates
          (and 
             terminates 
               (and terminates (eqtrm t1a t2a) by [t1_IH t1a t2a]
                    terminates (eqtrm t1b t2b) by [t1_IH t1b t2b])
             by and_tot
             (eqvar n1 n2))
        by and_tot in
        existsi ret { (eqtrm t1 t2) = *}
        hypjoin (eqtrm t1 t2) ret by t1_eq t2_eq end
      end
  end.

Total eqtrm eqtrm_tot.

Define eqtrm_eq : Forall(t1 t2:trm)(u:{(eqtrm t1 t2) = tt}).
                    { t1 = t2 } := 
  induction(t1:trm) 
  return Forall(t2:trm)(u:{(eqtrm t1 t2) = tt}). { t1 = t2 }
  with
    sym n1 => 
    foralli(t2:trm)(u:{(eqtrm t1 t2) = tt}).
    case t2 with
      default =>
      contra
       trans trans symm u hypjoin (eqtrm t1 t2) ff by t1_eq t2_eq end
             clash ff tt
      { t1 = t2 }
    | sym n2 => 
      case (eqvar n1 n2) by v ign with
        ff => 
        contra 
          trans trans symm u hypjoin (eqtrm t1 t2) ff by t1_eq t2_eq v end
                clash ff tt
        { t1 = t2 }
      | tt => hypjoin t1 t2 by t1_eq t2_eq [eqvar_eq n1 n2 v] end
      end
    end
  | app t1a t1b => 
    foralli(t2:trm)(u:{(eqtrm t1 t2) = tt}).
    case t2 with
      default => 
      contra
       trans trans symm u hypjoin (eqtrm t1 t2) ff by t1_eq t2_eq end
             clash ff tt
      { t1 = t2 }
    | app t2a t2b => 
      abbrev e1 = (eqtrm t1a t2a) in
      abbrev e2 = (eqtrm t1b t2b) in
      abbrev P = trans hypjoin (and e1 e2) (eqtrm t1 t2)
                       by t1_eq t2_eq end
                    u in
      hypjoin t1 t2 by t1_eq t2_eq
        [t1_IH t1a t2a [and_eq_tt1 e1 e2 P]]
        [t1_IH t1b t2b [and_eq_tt2 e1 e2 P]]
      end
    end
  | lam n1 t1a => 
    foralli(t2:trm)(u:{(eqtrm t1 t2) = tt}).
    case t2 with
      default => 
      contra
       trans trans symm u hypjoin (eqtrm t1 t2) ff by t1_eq t2_eq end
             clash ff tt
      { t1 = t2 }
    | lam n2 t2a => 
      abbrev e1 = (eqtrm t1a t2a) in
      abbrev e2 = (eqvar n1 n2) in
      abbrev P = trans hypjoin (and e1 e2) (eqtrm t1 t2)
                       by t1_eq t2_eq end
                    u in
      hypjoin t1 t2 by t1_eq t2_eq
        [t1_IH t1a t2a [and_eq_tt1 e1 e2 P]]
        [eqvar_eq n1 n2 [and_eq_tt2 e1 e2 P]]
      end
    end
  | pi n1 t1a t1b => 
    foralli(t2:trm)(u:{(eqtrm t1 t2) = tt}).
    case t2 with
      default => 
      contra
       trans trans symm u hypjoin (eqtrm t1 t2) ff by t1_eq t2_eq end
             clash ff tt
      { t1 = t2 }
    | pi n2 t2a t2b => 
      abbrev e1 = (eqtrm t1a t2a) in
      abbrev e2 = (eqtrm t1b t2b) in
      abbrev e3 = (eqvar n1 n2) in
      abbrev e12 = (and e1 e2) in
      abbrev P = trans hypjoin (and e12 e3) (eqtrm t1 t2)
                       by t1_eq t2_eq end
                    u in
      abbrev P1 = [and_eq_tt1 e12 e3 P] in
      hypjoin t1 t2 by t1_eq t2_eq
        [t1_IH t1a t2a [and_eq_tt1 e1 e2 P1]]
        [t1_IH t1b t2b [and_eq_tt2 e1 e2 P1]]
        [eqvar_eq n1 n2 [and_eq_tt2 e12 e3 P]]
      end
    end
  end.

% just skipping for now
Define trusted eqtrm_refl : Forall(t1:trm). { (eqtrm t1 t1) = tt } := 
  induction(t1:trm) return {(eqtrm t1 t1) = tt}
  with
    sym n1 =>
    hypjoin (eqtrm t1 t1) tt by t1_eq [eqvar_refl n1] end
  | app t1a t1b => 
    hypjoin (eqtrm t1 t1) tt by t1_eq [t1_IH t1a] [t1_IH t1b] end
  | lam n1 t1a => 
    hypjoin (eqtrm t1 t1) tt by t1_eq [t1_IH t1a] [eqvar_refl n1] end
  | pi n1 t1a t1b => 
    hypjoin (eqtrm t1 t1) tt by t1_eq [t1_IH t1a] [t1_IH t1b] [eqvar_refl n1] end
  end.

Define neqtrm_neq
  : Forall(t1 t2:trm)(u:{(eqtrm t1 t2) = ff}).
      { t1 != t2 } := 
  foralli(t1 t2:trm)(u1:{(eqtrm t1 t2) = ff}).
  diseqi
  foralli(u2:{ t1 = t2 }).
  contra
    trans symm u1
    trans cong (eqtrm t1 *) symm u2
    trans [eqtrm_refl t1]
          clash tt ff
  False.    

Define sym_to_string :=
  fun(v:var). "sym".

Define pi_char := Cba.
Define lam_char := Csl.

Define trm_to_string :=
  fun trm_to_string(owned t:trm):string.
    match t with
      sym n => match (eqvar n tp) with
                 ff => match (eqvar n knd) with
                         ff => (sym_to_string n)
                       | tt => "kind"
                       end
               | tt => "type"
               end
    | app t1 t2 => (stringc Clp
                   (string_app (trm_to_string t1)
                   (stringc Csp
                   (string_app (trm_to_string t2)
                   (stringc Crp inc stringn)))))
    | lam n t1 => (stringc Clp
                  (stringc lam_char
                  (stringc Csp
                  (string_app (sym_to_string n)
                  (stringc Csp
                  (string_app (trm_to_string t1)
                  (stringc Crp inc stringn)))))))
    | pi n T1 T2 => (stringc Clp
                    (stringc pi_char
                    (stringc Csp
                    (string_app (sym_to_string n)
                    (stringc Csp
                    (string_app (trm_to_string T1)
                    (stringc Csp
                    (string_app (trm_to_string T2)
                    (stringc Crp inc stringn)))))))))
    end.

Define tpknd := fun(b:bool). match b with ff => knd | tt => tp end.

Define tpknd_tot : Forall(b:bool). Exists(n:var). { (tpknd b) = n } :=
  induction(b:bool) 
    return Exists(n:var). { (tpknd b) = n } with
    ff => existsi knd { (tpknd b) = * }
            hypjoin (tpknd b) knd by b_eq end
  | tt => existsi tp { (tpknd b) = * }
            hypjoin (tpknd b) tp by b_eq end
  end.

Total tpknd tpknd_tot.

Define istpkndEq : Forall(T:trm)
                         (Tistpknd:{(or (istp T) (isknd T)) = tt}).
                    { T = (sym (tpknd (istp T)))} :=
  foralli(T:trm)
         (Tistpknd:{(or (istp T) (isknd T)) = tt}).
    abbrev Tistp = terminates (istp T) by istp_tot in
    abbrev Tisknd = terminates (isknd T) by isknd_tot in
      case Tistp with
        ff => 
          case Tisknd with
            ff => 
              contra
                trans
                  trans symm Tistpknd
                        hypjoin (or Tistp Tisknd) ff
                        by Tistp_eq Tisknd_eq end
                  clash ff tt
              { T = (sym (tpknd Tistp)) }
          | tt =>
             trans [iskndEq T Tisknd_eq]
                   hypjoin (sym knd) (sym (tpknd Tistp))
                   by Tistp_eq end
          end
        | tt => 
          trans [istpEq T Tistp_eq]
                hypjoin (sym tp) (sym (tpknd Tistp))
                by Tistp_eq end
        end.