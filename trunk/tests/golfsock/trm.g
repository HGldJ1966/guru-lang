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
    abbrev r = terminates (eqvar n' n) by eqvarTot in
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

Define istp_tot := 
  foralli(t:trm). 
    existse [issym_tot tp t]
    foralli(b:bool)(ub:{(issym tp t) = b}).
      existsi b { (istp t) = * }
        trans join (istp t) (issym tp t)
              ub.

Define isknd_tot := 
  foralli(t:trm). 
    existse [issym_tot knd t]
    foralli(b:bool)(ub:{(issym knd t) = b}).
      existsi b { (isknd t) = * }
        trans join (isknd t) (issym knd t)
              ub.

%Set "debug_def_eq".
Define issymEq : Forall(n:var)(t:trm)(u:{(issym n t) = tt}).{t = (sym n)} :=
  foralli(n:var).
  induction(t:trm) return Forall(u:{(issym n t) = tt}).{t = (sym n)} with
    sym n' => 
    foralli(u:{(issym n t) = tt}).
      trans t_eq 
            cong (sym *)
             [eqvarEq n' n
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
      sym n2 => (eqvar n1 n2)
    | app t2a t2b => ff
    | lam n2 t2a => ff
    | pi n2 t2a t2b => ff
    end
  | app t1a t1b =>
    match t2 with
      sym n2 => ff
    | app t2a t2b => (and (eqtrm t1a t2a) (eqtrm t1b t2b))
    | lam n2 t2a => ff
    | pi n2 t2a t2b => ff
    end
  | lam n1 t1a =>
    match t2 with
      sym n2 => ff
    | app t2a t2b => ff
    | lam n2 t2a => (and (eqtrm t1a t2a) (eqvar n1 n2))
    | pi n2 t2a t2b => ff
    end
  | pi n1 t1a t1b =>
    match t2 with
      sym n2 => ff
    | app t2a t2b => ff
    | lam n2 t2a => ff
    | pi n2 t2a t2b => (and (and (eqtrm t1a t2a) (eqtrm t1b t2b))  
                            (eqvar n1 n2))
    end
  end.

Define trusted eqtrmEq : Forall(t1 t2:trm)(u:{(eqtrm t1 t2) = tt}).
                          { t1 = t2 } := truei.

Define trusted neqtrmNeq : Forall(t1 t2:trm)(u:{(eqtrm t1 t2) = ff}).
                          { t1 != t2 } := truei.

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