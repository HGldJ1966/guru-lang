Include trusted "../lib/word.g".
Include trusted "../lib/list.g".
Include trusted "../lib/pair.g".
Include trusted "../lib/pow.g".
Include trusted "../lib/minus.g".
Include trusted "../lib/uwarray.g".
Include trusted "../lib/warray.g".

Define node := word.

% test if all nodes in a list of adjacent ones are bounded.
Define spec adjlist_bounded :=
  fun(l:<list node>)(N:word).
   (list_all node fun(n:node):bool.(ltword n N) l).

% use list_all in list.g, vec_all in vec.g
Define spec nodes_bounded :=
  fun(N:word)(arr:<warray <list node> N>):bool.
    (vec_all <list node> (word_to_nat N) fun(l:<list node>):bool.
       (adjlist_bounded l N) arr).

Inductive graph : Fun(N:word).type :=
  mkgraph : Fun(N:word)(arr : <warray <list node> N>)
               (u : { (nodes_bounded N arr) = tt })
.
            <graph N>.

Define get_neighbors :=
  fun(x:node)(N:word)(g:<graph N>)(u : { (ltword x N) = tt }):<list node>.
    match g with
      mkgraph _ arr _ => (warray_get <list node> N arr x u)
    end.

Define get_neighbors_bounded 
  : Forall(x:node)(N:word)(g:<graph N>)(u : { (ltword x N) = tt }).
          { (adjlist_bounded (get_neighbors x N g) N) = tt } :=
    foralli(x:node)(N:word)(g:<graph N>)(u : { (ltword x N) = tt }).
    case g with
      mkgraph _ arr g_u =>
          abbrev p1 = hypjoin (get_neighbors x N g) (vec_get arr (to_nat x)) by g_eq end in

	  abbrev p2_u1 = trans symm [ltword_to_lt x N] u in	  
	  abbrev p2_u2 = hypjoin (vec_all <list node> fun(l:<list node>):bool.(adjlist_bounded l N) arr) tt by g_eq g_u end in
          abbrev p2 = [vec_all_get <list node> (word_to_nat N) (word_to_nat x) arr fun(l:<list node>):bool.(adjlist_bounded l N) p2_u1 p2_u2] in
	  abbrev p3 = join (fun(l:<list node>):bool.(adjlist_bounded l N) (vec_get arr (word_to_nat x)))
	                       (adjlist_bounded (vec_get arr (word_to_nat x)) N) in

	  trans cong (adjlist_bounded * N) p1
	  trans symm p3 p2
    end.

Define spec adjacent_h := fun(x:node)(l:<list node>). (member node x l eqword).

Define spec adjacent :=
  fun(x y:node)(N:word)(g:<graph N>)
     (ux : { (ltword x N) = tt })
     (uy : { (ltword y N) = tt }):bool.
    (or (eqword x y) (adjacent_h y (get_neighbors x N g ux))).

% add directed edge
 Define spec add_edge :=
   fun(x y:node)(N:word)(g:<graph N>)
                (ux : { (ltword x N) = tt })
                (uy : { (ltword y N) = tt }):<graph N>.
     match (adjacent x y N g ux uy) with
       ff => abbrev x_ns = (cons node y (get_neighbors x N g ux)) in % add y as a neighbor of x

           match g with
            mkgraph _ arr g_u => 
                (mkgraph N (warray_set <list word> x x_ns N arr ux) 

		abbrev p1 = join (vec_all fun(l:<list node>):bool.(adjlist_bounded l N) (warray_set x x_ns arr))
		                 (nodes_bounded N (warray_set x x_ns arr)) in
		abbrev p2_u2 = hypjoin (vec_all fun(l:<list node>):bool.(adjlist_bounded l N) arr) tt by g_u end in
		abbrev p2_u3 = hypjoin (fun(l:<list node>):bool.(adjlist_bounded l N) x_ns) tt by [get_neighbors_bounded x N g ux] uy end in
		abbrev p2 = [warray_all_set <list word> x x_ns N arr
		                     fun(l:<list node>):bool.(adjlist_bounded l N)
				     ux
				     p2_u2
				     p2_u3] in

	        symm trans symm p2 p1
                )
           end
     | tt => g
     end.

Define no_edge_graph :=
  fun(N:word):<graph N>. 
    abbrev arr = (warray_new <list word> N (nil word)) in
      (mkgraph N arr
               abbrev v = (mkvec <list word> (nil word) (word_to_nat N)) in
	       abbrev v_eq = join v (mkvec <list word> (nil word) (word_to_nat N)) in
               abbrev p1 = join (fun(l:<list node>):bool.(adjlist_bounded l N) nil) tt in
	       hypjoin (nodes_bounded N arr) tt by [mkvec_implies_vec_all <list word> (nil word) (word_to_nat N) v fun(l:<list node>):bool.(adjlist_bounded l N) v_eq p1] end
	       ). 

Inductive edge : Fun(N:word).type :=
  mkedge : Fun(N:word)(x y:word)
              (ux : { (ltword x N) = tt })
              (uy : { (ltword y N) = tt }).
           <edge N>.

Define spec graph_from_edges_h :=
  fun(N:word)(l:<list <edge N>>)(g:<graph N>):<graph N>.
    match g with
      mkgraph _ arr g_u =>
        match l with
	  nil _ => g
	| cons _ v l' =>
	    match v with
	      mkedge _ x y ux uy => (add_edge x y N g ux uy)
	    end
        end
    end.
  
Define spec graph_from_edges :=
  fun(N:word)(l:<list <edge N>>):<graph N>.
    (graph_from_edges_h N l (no_edge_graph N)).
    
Define graph_to_warray :=
  fun(N:word)(g:<graph N>):<warray <list node> N>.
    match g with
      mkgraph _ arr _ => cast arr by cong <warray <list node> *> 
                                       symm inj <graph *> g_Eq 
    end.


Define remove_edge_h :=
  fun remove_edge_h(x:node)(l:<list word>):<list word>.
    match l with
      nil _ => (nil word)
    | cons _ v l' =>
      match (eqword x v) with
        ff => (cons word v (remove_edge_h x l'))
      | tt => l'
    end
  end.
    
%- Define remove_edge :=
 fun(x y:node)(N:word)(g:<graph N>)
              (ux : { (ltword x N) = tt })
              (uy : { (ltword y N) = tt }):<graph N>.
   match (adjacent x y N g ux uy) with
     ff => g
   | tt => let x_ns = (remove_edge_h y (get_neighbors x N g ux)) in % remove edge pointing from x to y
       match g with
         mkgraph _ arr _ => 
           (mkgraph N (warray_set <list word> x x_ns N arr ux)) % prove nodes are still bounded
       end
  end. -%

Define spec connected_h :=
  fun connected_h(x y:node)(N:word)(g:<graph N>)(mv : <uwarray bool N>)
                 (l:<list node>)
		 (ux : { (ltword x N) = tt })
		 (uy : { (ltword y N) = tt })
		 (uz : { (adjlist_bounded l N) = tt }):bool.
    match (eqword x y) with
      ff =>
        match l with
          nil _ => ff
        | cons _ v l' =>
            abbrev uv_u = hypjoin (list_all fun(n:node):bool.(ltword n N) (cons v l')) tt by l_eq uz end in
            abbrev uv = hypjoin (ltword v N) tt by [list_all_cons_tt_head node fun(n:node):bool.(ltword n N) v l' uv_u] end in
	    abbrev uz' = [get_neighbors_bounded v N g uv] in
	    abbrev uz'' = hypjoin (adjlist_bounded l' N) tt by [list_all_cons_tt_tail node fun(n:node):bool.(ltword n N) v l' uv_u] end in
	    match (uwarray_get bool N mv v uv) with
	      ff => (connected_h v y N g (uwarray_set bool N mv v tt uv) (get_neighbors v N g uv) uv uy uz')
	    | tt => (connected_h v y N g mv l' uv uy uz'')
	    end
        end
    | tt => tt
    end.

Define spec connected :=
  fun connected(x y:node)(N:word)(g:<graph N>)(mv : <uwarray bool N>)
               (ux : { (ltword x N) = tt })
	       (uy : { (ltword y N) = tt }):bool.
    abbrev x_ns = (get_neighbors x N g ux) in
      (connected_h x y N g mv x_ns ux uy [get_neighbors_bounded x N g ux]).

Define connected2_h :=
  fun connected2_h(x y:node)(l:<list node>)(N:word)(g:<graph N>)(mv : <uwarray bool N>)
                 (connected2_f : Fun(x y:node)(N:word)(g:<graph N>)
		 (mv : <uwarray bool N>)
		 (ux : { (ltword x N) = tt })
		 (uy : { (ltword y N) = tt }).bool)
		 (ux : { (ltword x N) = tt })
		 (uy : { (ltword y N) = tt })
		 (u : { (adjlist_bounded l N) = tt }):bool.

    match l with
      nil _ => ff
    | cons _ v l' =>
      	abbrev p1_u = hypjoin (list_all fun(n:node):bool.(ltword n N) (cons v l')) tt by l_eq u end in
	abbrev p1 = trans join (ltword v N) (fun(n:node):bool.(ltword n N) v) [list_all_cons_tt_head node fun(n:node):bool.(ltword n N) v l' p1_u] in
        let keep_searching = 
            match (uwarray_get bool N mv v p1) with
              ff => (not (connected2_f v y N g (uwarray_set bool N mv v tt p1) p1 uy))
            | tt => tt
            end
        in
          match keep_searching with
            ff => tt % (connected2_f v y ...) returned true
          | tt => (connected2_h x y l' N g mv connected2_f ux uy
                              hypjoin (adjlist_bounded l' N) tt by [list_all_cons_tt_tail node fun(n:node):bool.(ltword n N) v l' p1_u] end)
          end
    end.

Define spec connected2 :=
  fun connected2(x y:node)(N:word)(g:<graph N>)(mv : <uwarray bool N>)
               (ux : { (ltword x N) = tt })
               (uy : { (ltword y N) = tt }):bool.
    abbrev x_ns = (get_neighbors x N g ux) in
    match (member node y x_ns eqword) with
      ff => (connected2_h x y x_ns N g mv connected2 ux uy
	      [get_neighbors_bounded x N g ux])
    | tt => tt
    end.
%-
Define spec mk_complete_bintree_h :=
  fun mk_complete_bintree_h(N:word)(l:<list <edge N>>)(n:nat)
			   (u1:{ (lt n (to_nat N)) = tt }) % n is bounded
			   (u2:{ (lt (mult2 n) (to_nat N)) = tt }) % the nodes n are pointing to are bounded
			   (u3:{ (le n (to_nat word_max)) = tt}):
			   <list <edge N>>.
    abbrev u' = hypjoin (ltword (nat_to_word n) N) tt by u [word_to_nat_to_word N] end in
    match n with
          Z => l
	| S n' => % node n' has two edges one to node 2n'+1 and another to node 2n'+2
	  (mk_complete_bintree_h N (cons edge (mkedge N (nat_to_word n') (nat_to_word (S (mult2 n')))
	                             % (nat_to_word n') < N
			             % (nat_to_word (S (mult2 n'))) < N
			             )
				     (cons (mkedge N (nat_to_word n') (nat_to_word (S (S (mult2 n'))))
	                                % (nat_to_word n') < N
				        % (nat_to_word (S (S (mult2 n')))) < N
				     ) l))
	    n'
	    % n' < (to_nat N)
	    % (mult2 n) < (to_nat N)
           )
    end.	          

% constructs a complete binary-tree of height h
Define spec mk_complete_bintree := 
  fun mk_complete_bintree(h:nat)
                         (u:{ (le (minus (pow two (S h)) one) (to_nat word_max)) = tt }):
    <graph (nat_to_word (minus (pow two (S h)) one))>.
    abbrev num_nodes = (minus (pow two (S h)) one) in % number of nodes in the tree
    abbrev N = (nat_to_word num_nodes) in

    abbrev nonleaf_nodes = (minus (pow two h) one) in % number of nodes without the leaves
    abbrev nonleaf_nodes_lt_num_nodes =
      hypjoin (lt nonleaf_nodes num_nodes) tt by
	[minus_lt one (pow two (S h)) (pow two h)
	  hypjoin (le one (pow two h)) tt by [lt_S_le Z (pow two h) [pow_gt_zero two h clash two Z]] end
  	  [pow_lt two h join (lt one two) tt]] end in

    %abbrev m2nonleaf_nodes_lt_num_nodes = 
    
    abbrev nonleaf_nodes_le_word_max = [lt_implies_le nonleaf_nodes (to_nat word_max)
      [ltle_trans nonleaf_nodes num_nodes (to_nat word_max) nonleaf_nodes_lt_num_nodes u]] in

    let edge_list = (mk_complete_bintree_h N (nil <edge N>) nonleaf_nodes
      trans cong (lt nonleaf_nodes *) [nat_to_word_to_nat num_nodes u]
        nonleaf_nodes_lt_num_nodes
      % m2nonleaf < N
      nonleaf_nodes_le_word_max) in


      (graph_from_edges (nat_to_word num_nodes) edge_list).
-%
    
%Set "print_parsed".
%Set "debug_hypjoin_normalize".

%- will not compile when uncommented -%
%- Define spec is_cyclic_h :=
  fun is_cyclic_h(N:word)(g:<graph N>)(n:nat)
                 (u : { (ltword (nat_to_word n) N) = tt }):bool.
    match (connected (nat_to_word n) (nat_to_word n) N g (uwarray_new bool N ff) u u) with
      ff =>
        match n with
          Z => ff
	| S n' => (is_cyclic_h N g n'
	           hypjoin (ltword (nat_to_word n') N) tt by u n_eq end)
        end
    | tt => tt
    end. 
  
Define spec is_cyclic :=
  fun is_cyclic(N:word)(g:<graph N>):bool.
    match (word_to_nat N) with
      Z => ff
    | S n' => (is_cyclic_h N g (word_to_nat n')
                  join (ltword (nat_to_word n') N) tt)
    end.
-%
  

%%%%%%
%  below we construct the following graph for testing:
%
%      0    3
%       \
%        v
%  1 <-- 2
%
%%%%%

Define spec g := (add_edge word2 word1
                      word4
                 (add_edge word0 word2
		      word4 (no_edge_graph word4)
		      join (ltword word0 word4) tt
		      join (ltword word2 word4) tt)
		 join (ltword word2 word4) tt
		 join (ltword word1 word4) tt).

Define edge_list := (cons <edge word4> (mkedge word4 word2 word1
                                  join (ltword word2 word4) tt
				  join (ltword word1 word4) tt)
		          (cons <edge word4> (mkedge word4 word0 word2
			          join (ltword word0 word4) tt
				  join (ltword word2 word4) tt) (nil <edge word4>))).
				  
Define spec g2 := (graph_from_edges word4 edge_list).

% this should be true
Interpret (connected word0 word1 word4 g (uwarray_new bool word4 ff)
                     join (ltword word0 word4) tt
		     join (ltword word1 word4) tt).

% this should be false
Interpret (connected word2 word3 word4 g (uwarray_new bool word4 ff)
                     join (ltword word2 word4) tt
		     join (ltword word3 word4) tt).

%%%%% Ideas %%%%%
% Define cyclic :=
% Define bipartite :=
% Define tree := % connected acyclic graph
% Define shortest_path :=    

