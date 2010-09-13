Inductive uholder : Fun(A:type).type :=
  mk_uholder : Fun(A:type)(#untracked a:A).<uholder A>.

%- not working
Define unhold :=
  fun(spec A:type)(h:<uholder A>): #untracked A.
  match h with
    mk_uholder _ a => cast a by symm inj <uholder *> h_Eq %mean trick that is required
  end.
-%
