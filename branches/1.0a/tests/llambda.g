Include "../lib/nat.g".
Include "../lib/bool.g".
Include "../lib/pair.g".
Include "../lib/removeAll.g".

%Set "print_parsed".

%-
 - Untyped Lambda With Free Variables
 -%


Inductive lterm : Fun(l:<list nat>).type :=
  var : Fun(v:nat).<lterm (cons nat v (nil nat))>
| abs : Fun(a:nat)(spec l:<list nat>)(b:<lterm l>).<lterm (removeAll nat eqnat a l)>
| app : Fun(spec l1 l2:<list nat>)(x1:<lterm l1>)(x2:<lterm l2>).<lterm (appendf nat l1 l2)>.

Define lterm_subst : Fun(n:nat)(spec l:<list nat>)(e1:<lterm l>)(e2:<lterm (nil nat)>).<lterm (removeAll nat eqnat n l)> :=
  fun lterm_subst(n:nat)(spec l:<list nat>)(e1:<lterm l>)(e2:<lterm (nil nat)>):<lterm (removeAll nat eqnat n l)>.
    match e1 by u v with
      var n' => match (eqnat n n') by u' v' with
                  ff => cast e1 by trans v
                                         cong <lterm *>
                                         symm trans cong (removeAll nat eqnat n *)
                                                      inj <lterm *> v
                                                    hypjoin (removeAll nat eqnat n (cons nat n' (nil nat)))
                                                            (cons nat n' (nil nat)) by u' end
                | tt => cast e2 by cong <lterm *>
                                   symm trans cong (removeAll nat eqnat n *)
                                                inj <lterm *> v
                                        trans cong (removeAll nat eqnat n (cons nat * (nil nat)))
                                                symm [eqnatEq n n' u'] 
                                              hypjoin (removeAll nat eqnat n (cons nat n (nil nat)))
                                                      (nil nat) by [eqnat_refl n] end
                end
    | abs a l' b => match (eqnat n a) by u' v' with
                     ff => cast (abs a (removeAll nat eqnat n l') (lterm_subst n l' b e2)) by cong <lterm *>
                                                                                                trans [removeAll_comm nat eqnat eqnatTot a n l']
                                                                                                      cong (removeAll nat eqnat n *) symm inj <lterm *> v
                   | tt => cast (abs a l' b) by cong <lterm *>
                                                     trans symm [removeAll_idem nat eqnat eqnatTot a l']
                                                     trans cong (removeAll nat eqnat a *) symm inj <lterm * > v
                                                           cong (removeAll nat eqnat * l) symm [eqnatEq n a u']
                   end
    | app l1 l2 x1 x2 => cast (app (removeAll nat eqnat n l1) (removeAll nat eqnat n l2) (lterm_subst n l1 x1 e2) (lterm_subst n l2 x2 e2)) by
                              cong <lterm *>
                                   %-abbrev cl1 = cast l1 by inj <lterm *> symm v in
                                   abbrev cl2 = cast l2 by inj <lterm *> symm v in-%
                                   existse [removeAllTot nat eqnat eqnatTot n l2]
                                    foralli(lll:<list nat>)(lllu:{(removeAll nat eqnat n l2) = lll}).
                                      existse [neqconsPartialAppTot nat eqnat eqnatTot n]
                                        foralli(f:Fun(owned a:nat)(l':<list nat>).<list nat>)(uf:{(neqcons nat eqnat n) = f}).
                                          trans cong (appendf nat (removeAll nat eqnat n l1) *) lllu
                                          trans symm [removeAll_appendf nat eqnat eqnatTot n lll l1]
                                          trans cong (foldr nat <list nat> (neqcons nat eqnat n) * l1) symm lllu
                                          trans cong (foldr nat <list nat> (neqcons nat eqnat n) * l1)
                                                join (removeAll nat eqnat n l2) (foldr nat <list nat> (neqcons nat eqnat n) (nil nat) l2)
                                          trans cong (foldr nat <list nat> * (foldr nat <list nat> * (nil nat) l2) l1) uf
                                          trans symm [foldr_appendf nat <list nat> f (nil nat) l1 l2]
                                          trans cong (foldr nat <list nat> * (nil nat) (appendf nat l1 l2)) symm uf
                                          trans cong (foldr nat <list nat> (neqcons nat eqnat n) (nil nat) *) inj <lterm *> symm v
                                                join (foldr nat <list nat> (neqcons nat eqnat n) (nil nat) l) (removeAll nat eqnat n l)
                                             
    end.

Define lterm_eval : Fun(e1:<lterm (nil nat)>).<lterm (nil nat)> :=
  fun lterm_eval(e1:<lterm (nil nat)>):<lterm (nil nat)>.
    match e1 by u v return <lterm (nil nat)> with
      var n => abort <lterm (nil nat)>
    | abs a l b => cast (abs a l b) by symm v
    | app l1 l2 x1 x2 => abbrev cx1 = cast x1 by cong <lterm *> [appendf_eq_nil1 nat l1 l2 symm inj <lterm *> v] in
                         abbrev cx2 = cast x2 by cong <lterm *> [appendf_eq_nil2 nat l1 l2 symm inj <lterm *> v] in
                         match (lterm_eval cx1) by u' v' return <lterm (nil nat)> with
                           var n' => abort <lterm (nil nat)>
                         | abs a' l' b' => (lterm_eval cast (lterm_subst a' l' b' (lterm_eval cx2)) by symm v')
                         | app l1' l2' x1' x2' => abort <lterm (nil nat)>
                         end
    end.
                           

%- 
   We define a datatype of pre-lterms, which lterms without the 
   annotations for lists of variables.  Then to_lterm converts
   a pre_lterm to an lterm (actually, a list of vars and an
   lterm with that list of vars -- hence the to_lterm_t type). 

   Then it becomes more reasonable to write a simple test  
   below.
-%

Inductive pre_lterm : type :=
  pvar : Fun(v:nat).pre_lterm
| pabs : Fun(a:nat)(b:pre_lterm).pre_lterm
| papp : Fun(x1 x2 : pre_lterm). pre_lterm.

Inductive to_lterm_t : type :=
  mk_to_lterm : Fun(l:<list nat>)(t:<lterm l>).to_lterm_t.

Define to_lterm := 
  fun to_lterm(x:pre_lterm):to_lterm_t.
   match x by u v return to_lterm_t with
     pvar v => (mk_to_lterm (cons nat v (nil nat)) (var v))
   | pabs a b => match (to_lterm b) by uu vv return to_lterm_t with
                   mk_to_lterm lb tb => (mk_to_lterm (removeAll nat eqnat a lb) 
                                           (abs a lb tb))
                 end
   | papp x1 x2 => match (to_lterm x1) by uu vv return to_lterm_t with
                     mk_to_lterm l1 t1 => 
                       match (to_lterm x2) by uu vv return to_lterm_t with
                         mk_to_lterm l2 t2 => 
                           (mk_to_lterm (appendf nat l1 l2) (app l1 l2 t1 t2))
                         end
                   end
   end.

Define test := (to_lterm (papp (papp (pabs Z (pabs (S Z) (papp (pvar (S Z)) (pvar Z))))
                                (pabs Z (pvar Z)))
                          (pabs Z (pabs (S (S Z)) (pvar (S (S Z))))))).
    
% Set "print_parsed".
% Set "printing_expand_consts".

Define test2 := match test by uu vv return <lterm (nil nat)> with
                  mk_to_lterm l t => 
                    match l by uu vv return <lterm (nil nat)> with
                      nil A' => (lterm_eval cast t by cong <lterm *> uu)
                    | cons A' x' l' => abort <lterm (nil nat)>
                    end
                 end.

Interpret test2.

Define eval_cutoff :  Fun(owned n:nat)(e1:<lterm (nil nat)>).<lterm (nil nat)> :=
  cutoff lterm_eval.

% Check for possible name collision issues
Define eval_cutoff_1 :  Fun(owned n:nat)(e1:<lterm (nil nat)>).<lterm (nil nat)> :=
  cutoff lterm_eval.

% Check for anonymous function support
Define eval_cutoff_2 :  Fun(owned n:nat)(e1:<lterm (nil nat)>).<lterm (nil nat)> :=
  cutoff fun(e1:<lterm (nil nat)>):<lterm (nil nat)>.(lterm_eval e1).

% This should not work, created to test context scope for intermediate cutoff terms
% Define eval_cutoff_3 :  Fun(owned n:nat)(e1:<lterm (nil nat)>).<lterm (nil nat)> := Cutoff_of_lterm_eval.

% Set "debug_eval".

Define sanity_check : Fun(e1:<lterm (nil nat)>)(n:nat).<lterm (nil nat)> :=
  fun sanity_check(e1:<lterm (nil nat)>)(n:nat):<lterm (nil nat)>.
    (eval_cutoff n e1).

Define test3 := match test by uu vv return <lterm (nil nat)> with
                  mk_to_lterm l t => 
                    match l by uu vv return <lterm (nil nat)> with
                      nil A' => (sanity_check cast t by cong <lterm *> uu (S (S (S Z))))
                    | cons A' x' l' => abort <lterm (nil nat)>
                    end
                 end.

Interpret test3.

% Set "comment_vars".

Define cutoff_lterm_eval_nils_to_abs :
  Forall (n:nat)(e1 e2:<lterm (nil nat)>)(p:{(cutoff lterm_eval n e1) = e2}).
    Exists (a:nat)(l:<list nat>)(b:<lterm l>)(u:{(removeAll nat eqnat a l) = (nil nat)}).{(cutoff lterm_eval n e1) = (abs a b)} :=
      induction (n:nat) by nterm ntype nIH return
          Forall(e1 e2:<lterm (nil nat)>)(p:{(cutoff lterm_eval n e1) = e2}).
            Exists(a:nat)(l:<list nat>)(b:<lterm l>)(u:{(removeAll nat eqnat a l) = (nil nat)}).
              {(cutoff lterm_eval n e1) = (abs a b)} with
        Z =>
          foralli(e1 e2:<lterm (nil nat)>)(p:{(cutoff lterm_eval n e1) = e2}).
            contra trans p
                         symm trans hypjoin (cutoff lterm_eval n e1) abort ! by nterm end
                   aclash e2
              Exists(a:nat)(l:<list nat>)(b:<lterm l>)(u:{(removeAll nat eqnat a l) = (nil nat)}).
                {(cutoff lterm_eval n e1) = (abs a b)}
      | S m =>
          induction(e1:<lterm (nil nat)>) by e1term e1type e1IH return
              Forall(e2:<lterm (nil nat)>)(p:{(cutoff lterm_eval n e1) = e2}).
                Exists(a:nat)(l:<list nat>)(b:<lterm l>)(u:{(removeAll nat eqnat a l) = (nil nat)}).
                  {(cutoff lterm_eval n e1) = (abs a b)} with
            var a' =>
              contra trans inj <lterm *> e1type
                     clash (cons nat a' (nil nat)) (nil nat)
                     Forall(e2:<lterm (nil nat)>)(p:{(cutoff lterm_eval n e1) = e2}).
                       Exists(a:nat)(l:<list nat>)(b:<lterm l>)(u:{(removeAll nat eqnat a l) = (nil nat)}).
                         {(cutoff lterm_eval n e1) = (abs a b)}
          | abs a' l' b' =>
              foralli (e2:<lterm (nil nat)>)(p:{(cutoff lterm_eval n e1) = e2}).
              existsi a' Exists (l:<list nat>)(b:<lterm l>)(u:{(removeAll nat eqnat * l) = (nil nat)}). 
                          {(cutoff lterm_eval n e1) = (abs * b)}
              existsi l' Exists (b:<lterm *>)(u:{(removeAll nat eqnat a' *) = (nil nat)}).{(cutoff lterm_eval n e1) = (abs a' b)}
              existsi b' Exists (u:{(removeAll nat eqnat a' l') = (nil nat)}).{(cutoff lterm_eval n e1) = (abs a' *)}
              existsi symm inj <lterm *> e1type {(cutoff lterm_eval n e1) = (abs a' b')}
              hypjoin (cutoff lterm_eval n e1) (abs a' b') by nterm e1term end
          | app l1 l2 x1 x2 =>
              abbrev cx1 = cast x1 by cong <lterm *> [appendf_eq_nil1 nat l1 l2 symm inj <lterm *> e1type] in
              abbrev cx2 = cast x2 by cong <lterm *> [appendf_eq_nil2 nat l1 l2 symm inj <lterm *> e1type] in
              foralli(e2:<lterm (nil nat)>)(p:{(cutoff lterm_eval n e1) = e2}).
                abbrev before_match = symm trans symm p
				           trans cong (cutoff lterm_eval * e1) nterm
                                                 cong (cutoff lterm_eval (S m) *) e1term
                                                 
                                  in
                existse cinv 
                             (cutoff lterm_eval m cx1) 
                             trans symm eval (cutoff lterm_eval (S m) (app cx1 cx2)) before_match
                foralli(hd:<lterm (nil nat)>)(hdu:{(cutoff lterm_eval m cx1) = hd}).
                existse [nIH m cx1 hd hdu]
                foralli(hda:nat)(hdl:<list nat>)(hdb:<lterm hdl>)(hdr:{(removeAll nat eqnat hda hdl) = (nil nat)})
                       (hdg:{(cutoff lterm_eval m cx1) = (abs hda hdb)}).
                abbrev to_cut = symm trans symm before_match
                                           hypjoin (cutoff lterm_eval (S m) (app cx1 cx2))
                                                   (cutoff lterm_eval m (lterm_subst hda hdb (cutoff lterm_eval m cx2)))
                                           by hdg end
                                in
                existse cinv 
                             (cutoff lterm_eval m cx2) 
                             trans cong (cutoff lterm_eval m (lterm_subst hda hdb *)) symm eval (cutoff lterm_eval m cx2) to_cut
                foralli(rg:<lterm (nil nat)>)(rgu:{(cutoff lterm_eval m cx2) = rg}).
                existse [nIH m cx2 rg rgu]
                foralli(rga:nat)(rgl:<list nat>)(rgb:<lterm rgl>)(rgr:{(removeAll nat eqnat rga rgl) = (nil nat)})
                       (rgg:{(cutoff lterm_eval m cx2) = (abs rga rgb)}).
                existse cinv
                             (lterm_subst hda hdl hdb rg)
                             trans cong (cutoff lterm_eval m *) symm eval (lterm_subst hda hdb rg) 
                                   symm trans symm to_cut
                                          cong (cutoff lterm_eval m (lterm_subst hda hdb *)) rgu 
                foralli(ne:<lterm (removeAll nat eqnat hda hdl)>)(neu:{(lterm_subst hda hdb rg) = ne}).
                abbrev cast_ne = cast ne by cong <lterm *> hdr in
                abbrev from_match = symm trans symm to_cut
                                         trans cong (cutoff lterm_eval m (lterm_subst hda hdb *)) rgu
                                               cong (cutoff lterm_eval m *) neu
                                    in
                existse [nIH m cast_ne e2 from_match]
                foralli(nea:nat)(nel:<list nat>)(neb:<lterm nel>)(ner:{(removeAll nat eqnat nea nel) = (nil nat)})
                       (neg:{(cutoff lterm_eval m cast_ne) = (abs nea neb)}).
                existsi nea Exists (l:<list nat>)(b:<lterm l>)(u:{(removeAll nat eqnat * l) = (nil nat)}).
                             {(cutoff lterm_eval n e1) = (abs * b)}
                existsi nel Exists (b:<lterm *>)(u:{(removeAll nat eqnat nea *) = (nil nat)}).{(cutoff lterm_eval n e1) = (abs nea b)}
                existsi neb Exists (u:{(removeAll nat eqnat nea nel) = (nil nat)}).{(cutoff lterm_eval n e1) = (abs nea *)}
                existsi ner {(cutoff lterm_eval n e1) = (abs nea neb)}
                trans p
                trans symm from_match
                      neg
          end
      end.          

Define lterm_eval_nils_to_abs :
  Forall (e1 e2:<lterm (nil nat)>)(p:{(lterm_eval e1) = e2}).
    Exists (a:nat)(l:<list nat>)(b:<lterm l>). { e2 = (abs a b) } :=
      foralli(e1 e2:<lterm (nil nat)>)(p:{(lterm_eval e1) = e2}).
        existse cind p
          foralli(n:nat)(nu:{(cutoff lterm_eval n e1) = e2}).
            existse [cutoff_lterm_eval_nils_to_abs n e1 e2 nu]
              foralli(aa:nat)(ll:<list nat>)(bb:<lterm ll>)
                     (ru:{(removeAll nat eqnat aa ll) = (nil nat)})
                     (uu:{(cutoff lterm_eval n e1) = (abs aa bb)}).
                existsi aa Exists (l:<list nat>)(b:<lterm l>). { e2 = (abs * b) }
                existsi ll Exists (b:<lterm *>). { e2 = (abs aa b) }
                existsi bb { e2 = (abs aa *) }
                  trans symm nu
                        uu.

%-
Define neqconsPartialAppTot2 :
  Forall(A:type)
        (eqfun: Fun(p q:A).bool)
        (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
        (n:A).
  Exists(f: Fun(owned a:A)(l:<list A>).<list A>).{(neqcons A eqfun n) = f} :=
  foralli(A:type)
         (eqfun: Fun(p q:A).bool)
         (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
         (n:A).
      abbrev p = terminates (neqcons A eqfun n n  (nil A)) by [neqconsTot A eqfun eqfunTot n n (nil A)] in
        cinv (neqcons A eqfun n) join p p.

-%