Include trusted "../lib/word.g".
Include trusted "../lib/list.g".
Include trusted "../lib/uwarray.g".
Include trusted "../lib/warray.g".

Define node := word.

% use list_all in list.g, vec_forall in vec.g
% Define spec nodes_bounded := 

Inductive graph : Fun(N:word).type :=
  mkgraph : Fun(N:word)(arr : <warray <list node> N>)
%               (u : { (nodes_bounded N arr) = tt })
.
            <graph N>.

Define connected :=
  fun connected(x y:node)(N:word)(g:<graph N>)(mv : <uwarray bool N>)
               (ux : { (ltword x N) = tt })
               (uy : { (ltword y N) = tt }):bool.
      abort bool.
