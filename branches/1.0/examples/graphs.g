Include trusted "../lib/word.g".
Include trusted "../lib/boxedword.g".
Include trusted "../lib/list.g".
Include trusted "../lib/pair.g".
Include trusted "../lib/pow.g".
Include trusted "../lib/minus.g".
Include trusted "../lib/uwarray.g".
Include trusted "../lib/warray.g".
Include trusted "../lib/unique_owned.g".
Include trusted "../lib/unique.g".
Include trusted "../lib/unowned.g".

Set "trust_hypjoins".
% Set "debug_eta_expand".
%Set "debug_to_carraway".
%- change to boxedWord, so that nodes will be tracked, and thus can
   be stored in lists. -%
Define node := boxedWord.


% test if all nodes in a list of adjacent ones are bounded.
Define spec adjlist_bounded :=
  fun(l:<list node>)(N:word).
    (list_all node fun(n:node):bool.(ltword (unboxWord n) N) l).

% use list_all in list.g, vec_all in vec.g
Define spec nodes_bounded :=
  fun(N:word)(arr:<warray <list node> N>):bool.
    (vec_all <list node> (word_to_nat N) fun(l:<list node>):bool.
       (adjlist_bounded l N) arr).


Inductive graph : Fun(N:word).type :=
 mkgraph : Fun(N:word)(#unique arr : <warray <list node> N>)
              (u : {(nodes_bounded N arr) = tt }).
  	        #unique <graph N>.

Define graph_to_warray :=
  fun(N:word)(! #unique g:<graph N>): #<unique g> <warray <list node> N>.
    match g with
      mkgraph _ arr _ => cast arr by cong <warray <list node> *> 
                                       symm inj <graph *> g_Eq 
    end.
	       
Define get_neighbors :=
  fun(x:word)(N:word)(^ #unique_owned g:<graph N>)
     (u : { (ltword x N) = tt }): <list node>.
    match g with
      mkgraph _ arr _ =>
        let ret = @ (warray_get <list node> N arr x u) in
          do (consume_unique_owned <warray <list node> N> arr)
             (owned_to_unowned <list node> ret) 
          end
    end.

Define get_neighbors_bounded 
  : Forall(x:word)(N:word)(g:<graph N>)(u : { (ltword x N) = tt }).
          { (adjlist_bounded (get_neighbors x N g) N) = tt } :=
    foralli(x:word)(N:word)(g:<graph N>)(u : { (ltword x N) = tt }).
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

Define adjacent_h :=
  fun(^#owned x:node)(l:<list node>):bool.
    let ret = (member node x (inspect <list node> l) boxedWord_eq) in
    do
      (consume_unowned <list node> l)
      ret
    end.



Define adjacent :=
  fun(x:word)(^#owned y:node)(N:word)(^ #unique_owned g:<graph N>)
     (ux : { (ltword x N) = tt })
     (uy : { (ltword (unboxWord y) N) = tt }):bool.
       let y_c = (clone_owned node y) in
       (or (eqword x (unboxWord y_c)) (adjacent_h y (get_neighbors x N g ux))).

% add directed edges
Define add_edge :=
   fun(x:word)(^#owned y:node)(N:word)(#unique g:<graph N>)
      (ux : { (ltword x N) = tt })
      (uy : { (ltword (unboxWord y) N) = tt }): #unique <graph N>.
     let g_i = (inspect_unique <graph N> g) in
     match (adjacent x (clone_owned node y) N (clone_unique_owned <graph N> g_i) ux 
              trans cong (ltword (unboxWord *) N) 
                      join (clone_owned node y) y
                    uy) with
       ff =>
         let x_ns =
	   (cons node (inc_owned node y)
	     (get_neighbors x N g_i ux)) in % add y as a neighbor of x
         match g with
           mkgraph _ arr g_u =>
             (mkgraph N (warray_set <list node> x x_ns N arr ux) 
             abbrev p1 =
	       join (vec_all fun(l:<list node>):bool.
	         (adjlist_bounded l N) (warray_set x x_ns arr))
		   (nodes_bounded N (warray_set x x_ns arr)) in
	     abbrev p2_u2 =
	       hypjoin (vec_all fun(l:<list node>):bool.
	         (adjlist_bounded l N) arr) tt by g_u end in
	     abbrev p2_u3 =
	       hypjoin (fun(l:<list node>):bool.
	         (adjlist_bounded l N) x_ns) tt by
		   [get_neighbors_bounded x N g ux] uy end in
	     abbrev p2 =
	       [warray_all_set <list node> x x_ns N arr
		fun(l:<list node>):bool.(adjlist_bounded l N)
                ux
                p2_u2
		p2_u3] in
	        symm trans symm p2 p1
             )
         end
     | tt =>
         let ret = g in
	 do (consume_unique_owned <graph N> g_i)
	    ret
	 end
     end.

Define no_edge_graph :=
  fun(N:word): #unique <graph N>.
    let n = (nil node) in
    let n_i = (inspect <list node> n) in
    abbrev arr = (warray_new <list node> N n_i) in
    let ret = (mkgraph N arr
                 abbrev v = (mkvec <list node> (nil node) (word_to_nat N)) in
	         abbrev v_eq = join v (mkvec <list node> (nil node) (word_to_nat N)) in
                 abbrev p1 = join (fun(l:<list node>):bool.(adjlist_bounded l N) nil) tt in
	         hypjoin (nodes_bounded N arr) tt
		   by [mkvec_implies_vec_all <list node> (nil node)
		      (word_to_nat N) v fun(l:<list node>):bool.
		      (adjlist_bounded l N) v_eq p1] end) in
    do (consume_unowned <list node> n)
       ret
    end. 

Inductive edge : Fun(N:word).type :=
  mkedge : Fun(N:word)(x:word)(y:node)
              (ux : { (ltword x N) = tt })
              (uy : { (ltword (unboxWord y) N) = tt }).
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
    


% Define remove_edge_h :=
%   fun remove_edge_h(x:node)(l:<list word>):<list word>.
%     match l with
%       nil _ => (nil word)
%     | cons _ v l' =>
%       match (eqword x v) with
%         ff => (cons word v (remove_edge_h x l'))
%       | tt => l'
%     end
%   end.


% Define remove_edge :=
%   fun(x y:node)(N:word)(g:<graph N>)
%                (ux : { (ltword x N) = tt })
%       	       (uy : { (ltword y N) = tt }):<graph N>.
%     match g with
%       mkgraph _ arr _ =>
%         let x_ns = (filter word nat Z % Z is a dummy variable
%                      fun(c:nat)(a:word).(not (eqnat a y))
% 		     (get_neighbors x N g ux)) in
		     
%         (mkgraph N (warray_set <list word> x x_ns N arr ux [ltxy y N]))
%     end.


 % fun(x y:node)(N:word)(g:<graph N>)
 %              (ux : { (ltword x N) = tt })
 %              (uy : { (ltword y N) = tt }):<graph N>.
 %   match (adjacent x y N g ux uy) with
 %     ff => g
 %   | tt => let x_ns = (remove_edge_h y (get_neighbors x N g ux)) in % remove edge pointing from x to y
 %       match g with
 %         mkgraph _ arr _ => 
 %           (mkgraph N (warray_set <list word> x x_ns N arr ux)) % prove nodes are still bounded
 %       end
 %  end. 

%Unset "trust_hypjoins".

Define connected_h :=
  fun connected_h(x:word)(^ #owned y:node)(N:word)
                 (! #unique_owned g:<graph N>)
		 (#unique mv : <uwarray bool N>)
                 (l:<list node>)
		 (ux : { (ltword x N) = tt })
		 (uy : { (ltword (unboxWord y) N) = tt })
		 (uz : { (adjlist_bounded l N) = tt }):bool.
    match (eqword x (unboxWord (clone_owned node y))) with
      ff =>
        match l with
          nil _ => 
          do
            (consume_unique <uwarray bool N> mv)
            ff
          end
        | cons _ v l' =>
            let mv_i = (inspect_unique <uwarray bool N> mv) in
	    let wv = (unboxWordu v) in
            abbrev uv_u = hypjoin (list_all fun(n:node):bool.
	      (ltword (unboxWord n) N) (cons v l')) tt by l_eq uz end in
            abbrev uv = hypjoin (ltword wv N) tt by
	      [list_all_cons_tt_head node fun(n:node):bool.
	        (ltword (unboxWord n) N) v l' uv_u] wv_eq end in
            abbrev nbors = (get_neighbors wv N (clone_unique_owned <graph N> g) uv) in
	    abbrev uz' = trans cong (adjlist_bounded * N) 
                                 join nbors
                                      (get_neighbors wv N g uv)
                               [get_neighbors_bounded wv N g uv] in
	    abbrev uz'' = hypjoin (adjlist_bounded l' N) tt by
	      [list_all_cons_tt_tail node fun(n:node):bool.
	        (ltword (unboxWord n) N) v l' uv_u] end in
	    match (uwarray_get bool N mv_i wv uv) with
	      ff =>
		  do (consume_unique_owned <uwarray bool N> mv_i)
		     (consume_unowned <list node> l')
                     (connected_h wv y N g (uwarray_set bool N mv wv tt uv)
		                  nbors uv uy uz')
		   end
	    | tt =>
	           do (consume_unique_owned <uwarray bool N> mv_i)
	              (connected_h wv y N g mv l' uv uy uz'')
		   end
	    end
        end
    | tt =>
          do 
	    (consume_unowned <list node> l)
            (consume_unique <uwarray bool N> mv)
 	    tt
	  end
    end.

Define connected :=
  fun connected(x:word)(^ #owned y:node)(N:word)(! #unique_owned g:<graph N>)(#unique mv : <uwarray bool N>)
               (ux : { (ltword x N) = tt })
	       (uy : { (ltword (unboxWord y) N) = tt }):bool.
    abbrev x_ns = (get_neighbors x N (clone_unique_owned <graph N> g) ux) in
      (connected_h x y N g mv x_ns ux uy trans cong (adjlist_bounded * N) 
                                                 join x_ns (get_neighbors x N g ux)
                                         [get_neighbors_bounded x N g ux]).

%-      
Define connected2_h :=
  fun connected2_h(x:word)(y:node)(l:<list node>)(N:word)(g:<graph N>)(mv : <uwarray bool N>)
                 (connected2_f : Fun(x:word)(y:node)(N:word)(g:<graph N>)
		 (mv : <uwarray bool N>)
		 (ux : { (ltword x N) = tt })
		 (uy : { (ltword (unboxWord y) N) = tt }).bool)
		 (ux : { (ltword x N) = tt })
		 (uy : { (ltword (unboxWord y) N) = tt })
		 (u : { (adjlist_bounded l N) = tt }):bool.

    match l with
      nil _ => ff
    | cons _ v l' =>
      	abbrev p1_u = hypjoin (list_all fun(n:node):bool.(ltword (unboxWord n) N) (cons v l')) tt by l_eq u end in
	abbrev p1 = trans join (ltword v N) (fun(n:node):bool.(ltword (unboxWord n) N) v) [list_all_cons_tt_head node fun(n:node):bool.(ltword (unboxWord n) N) v l' p1_u] in
        let keep_searching = 
            match (uwarray_get bool N mv (unboxWord v) p1) with
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
  fun connected2(x:word)(y:node)(N:word)(g:<graph N>)(mv : <uwarray bool N>)
               (ux : { (ltword x N) = tt })
               (uy : { (ltword (unboxWord y) N) = tt }):bool.
    abbrev x_ns = (get_neighbors x N g ux) in
    match (member node y x_ns eqword) with
      ff => (connected2_h x y x_ns N g mv connected2 ux uy
	      [get_neighbors_bounded x N g ux])
    | tt => tt
    end.

-%

%Set "print_parsed".
%Set "debug_hypjoin_normalize".
%-
Define spec mk_complete_bintree_h :=
  fun mk_complete_bintree_h(N:word)(g:<graph N>)(n:nat)
			   (u1:{ (lt n (to_nat N)) = tt }) % n is bounded
			   (u2:{ (lt (mult two n) (to_nat N)) = tt }): % the nodes n is pointing to are bounded
			   <graph N>.
    match n with
      Z => g
    | S n' => % node n' has two edges one to node 2n'+1 and another to node 2n'+2

          abbrev x = (nat_to_word n') in
	  abbrev y1 = (nat_to_boxedWord (plus (mult two n') one)) in
	  abbrev y2 = (nat_to_boxedWord (plus (mult two n') two)) in

	  %---- x is bounded ----%
          abbrev p1 = [ltle_trans n' (S n') n [lt_S n'] [eq_le (S n') n symm n_eq]] in % n' <= n
	  abbrev u1' = [lt_trans n' n (word_to_nat N) p1 u1] in
	  abbrev x_bounded = [lt_to_nat_ltword n' N u1'] in

	  %---- y2 is bounded ----%	  
	  abbrev p2 = [minusS3 n n' n_eq] in % n' = n-1
	  abbrev p3 = trans [mult_dist_minus two n one]
	                cong (minus (mult two n) *) [multOne two] in % 2(n-1) = 2n-2

	  abbrev p4 =  trans cong (plus (mult two *) two) p2 % 2n'+2 = 2(n-1)+2
	                  trans cong (plus * two) p3 % 2(n-1)+2 = 2n-2+2
			  trans [plus_comm (minus (mult two n) two) two] % (2n-2)+2 = 2+(2n-2)
                          trans symm [minus_plus_order two (mult two n) two] % 2+(2n-2) = (2+2n)-2
			  [minus_plus1 two (mult two n)] in % (2+2n)-2 = 2n
	  abbrev p5 = [eq_le (plus (mult two n') two) (mult two n) p4] in % y2 <= 2n
	  
	  abbrev y2_bounded_nat = [lelt_trans (plus (mult two n') two) (mult two n) (word_to_nat N) p5 u2] in  % y2 < N
	  abbrev y2_bounded = [lt_to_nat_ltword (plus (mult two n') two) N y2_bounded_nat] in

	  %---- y1 is bounded ----%
	  abbrev p6 = [plus_lt (mult two n') one two join (lt one two) tt] in % 2n'+1 < 2n'+2
	  
	  abbrev y1_bounded_nat = [lt_trans (plus (mult two n') one) (plus (mult two n') two) (word_to_nat N) p6 y2_bounded_nat] in
	  abbrev y1_bounded = [lt_to_nat_ltword (plus (mult two n') one) N y1_bounded_nat] in

	  %---- 2*n' is bounded ----%
	  abbrev p9 = [plus_lt (mult two n') Z one join (lt Z one) tt] in % 2n'+0 < 2n'+1
	  abbrev p10 = [eq_le (mult two n') (plus (mult two n') Z) symm [plusZ (mult two n')]] in % 2n' <= 2n'+0
	  abbrev p11 = [lelt_trans (mult two n') (plus (mult two n') zero) (plus (mult two n') one) p10 p9] in % 2n' < 2n'+1

	  abbrev u2' = [lt_trans (mult two n') (plus (mult two n') one) (word_to_nat N) p11 y1_bounded_nat] in
	  
	  (mk_complete_bintree_h N
	    (add_edge x y1 N 
	      (add_edge x y2 N g
	        x_bounded
		y2_bounded
	      )
	      x_bounded
	      y1_bounded
            )
	    n'
	    u1'
	    u2'
           )
    end.

% constructs a complete binary-tree of height h
Define spec mk_complete_bintree := 
  fun mk_complete_bintree(h:nat)
                         (u1:{ (le (minus (pow two (S h)) one) (to_nat word_max)) = tt })
			 (u2:{ h != Z }):
    <graph (nat_to_word (minus (pow two (S h)) one))>.
    
    % number of nodes in the tree
    abbrev num_nodes = (minus (pow two (S h)) one) in 
    abbrev N = (nat_to_word num_nodes) in

    % number of nodes without leaves
    abbrev nonleaf_nodes = (minus (pow two h) one) in 

    %---- non-leaf nodes are bounded by num_nodes ----%
    abbrev nonleaf_bounded = 
      hypjoin (lt nonleaf_nodes num_nodes) tt by
	[minus_lt one (pow two (S h)) (pow two h)
	  hypjoin (le one (pow two h)) tt by [lt_S_le Z (pow two h) [pow_gt_zero two h clash two Z]] end
  	  [pow_lt two h join (lt one two) tt]] end in 
	  
    %---- 2*(nonleaf_nodes) is bounded by num_nodes ----%
    abbrev p1 = trans cong (minus (mult * (pow two h)) one) symm [first_power two]
      cong (minus * one) [pow_mult h two one] in % 2(2^h)-1 = 2^(h+1)-1 
    abbrev p2 = symm [mult_dist_minus two (pow two h) one] in % 2(2^h)-2 = 2((2^h)-1)
    
    abbrev p3 = [pow_lt2 two h u2] in % 2 <= 2^h
    abbrev p4 = [ltle_trans one two (pow two h) join (lt one two) tt p3] in % 1 < 2^h
    abbrev p5 = [mult_lt2 (pow two h) two [pow_not_zero two h clash two Z] p4] in % 2^h < 2(2^h)
    abbrev p6 = [lelt_trans two (pow two h) (mult two (pow two h)) p3 p5] in % 2 < 2(2^h)
    abbrev p7 = [lt_trans one two (mult two (pow two h)) join (lt one two) tt p6] in % 1 < 2(2^h)
    abbrev p8 = [minusS2 (mult two (pow two h)) one p7] in % 2(2^h)-1 is the successor of 2(2^h)-2

    % 2(2^h)-2 < 2(2^h)-1    
    abbrev p9 = hypjoin (lt (mult two nonleaf_nodes) num_nodes) tt by
      p1 p2 p8
      [lt_S (minus (mult two (pow two h)) two)] end in

    % rephrase proof in terms of N
    abbrev m2nonleaf_bounded = trans cong (lt (mult two nonleaf_nodes) *) [nat_to_word_to_nat num_nodes u1] p9 in
    
    (mk_complete_bintree_h N (no_edge_graph N) nonleaf_nodes
      trans cong (lt nonleaf_nodes *) [nat_to_word_to_nat num_nodes u1]
        nonleaf_bounded
        m2nonleaf_bounded).

-%
%---- TODO ---
Define spec is_cyclic_h :=
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
  

%======
%  below we construct the following graph for testing:
%
%      0    3
%       \
%        v
%  1 <-- 2
%
%======

Define g := (add_edge word2 (inspect boxedWord (boxWord word1))
              word4
              (add_edge word0 (boxWord word2)
		word4 (no_edge_graph word4)
	        join (ltword word0 word4) tt
		hypjoin (ltword (unboxWord (boxWord word2)) word4) tt by
		  [word_to_boxedWord_to_word word2]
	          join (ltword word2 word4) tt end)
	      join (ltword word2 word4) tt
	      hypjoin (ltword (unboxWord (boxWord word1)) word4) tt by
		[word_to_boxedWord_to_word word1]
		join (ltword word1 word4) tt end).

% Define edge_list := (cons <edge word4> (mkedge word4 word2 word1
%                                   join (ltword word2 word4) tt
% 				  join (ltword word1 word4) tt)
% 		          (cons <edge word4> (mkedge word4 word0 word2
% 			          join (ltword word0 word4) tt
% 				  join (ltword word2 word4) tt) (nil <edge word4>))).
				  
% Define spec g2 := (graph_from_edges word4 edge_list).

% this should be true
Define test1 := (connected word0 (boxWord word1) word4 g (uwarray_new bool word4 ff)
                     join (ltword word0 word4) tt
		     hypjoin (ltword (unboxWord (boxWord word1)) word4) tt by [word_to_boxedWord_to_word word1] join (ltword word1 word4) tt end).

Compile test1 to "test1.c".

% this should be false
Define spec test2 := (connected word2 word3 word4 g (uwarray_new bool word4 ff)
                     join (ltword word2 word4) tt
		     join (ltword word3 word4) tt).

% get a "java.lang.StackOverflowError" when the code below is run
%-Define spec test3 := (mk_complete_bintree one 
  trans cong (lt * (word_to_nat word_max)) [first_power two]
   join (lt two (word_to_nat word_max)) tt
  clash one Z).-%
  
%--- Ideas ---%
% Define cyclic :=
% Define bipartite :=
% Define tree := (connected acyclic graph)
% Define shortest_path :=