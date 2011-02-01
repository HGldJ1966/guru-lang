Include trusted "../lib/word.g".
Include trusted "../lib/list.g".
Include trusted "../lib/uwarray.g".
Include trusted "../lib/warray.g".

Define node := word.

% use list_all in list.g, vec_all in vec.g
Define spec nodes_bounded :=
  fun(N:word)(arr:<warray <list node> N>):bool.
    (vec_all <list node> (word_to_nat N) fun(l:<list node>):bool.
       (list_all node fun(n:node):bool.(ltword n N) l) arr).

Inductive graph : Fun(N:word).type :=
  mkgraph : Fun(N:word)(arr : <warray <list node> N>)
               (u : { (nodes_bounded N arr) = tt })
.
            <graph N>.

% complains : "The classifier computed for the body of a case contains pattern variables from that case."
% Define graph_to_warray :=
%   fun(N:word)(g:<graph N>):<warray <list node> N>.
%     match g with
%       mkgraph _ arr _ => arr
%     end.
    
Define get_neighbors :=
  fun(x:node)(N:word)(g:<graph N>)(u : { (ltword x N) = tt }):<list node>.
    match g with
      mkgraph _ arr _ => (warray_get <list node> N arr x u)
    end.


Define adjacent_h := 
  fun adjacent_h(x:node)(l:<list node>):bool.
    match l with
      nil _ => ff
    | cons _ v l' => (or (eqword x v) (adjacent_h x l'))
    end.

Define adjacent :=
  fun(x y:node)(N:word)(g:<graph N>)
     (ux : { (ltword x N) = tt })
     (uy : { (ltword y N) = tt }):bool.
    (or (eqword x y) (adjacent_h y (get_neighbors x N g ux))).

% prove nodes are still bounded after adding an edge
% Define add_edge :=
%   fun(x y:node)(N:word)(g:<graph N>)
%                (ux : { (ltword x N) = tt })
%                (uy : { (ltword y N) = tt }):<graph N>.
%     match (adjacent x y N g ux uy) with
%       ff => let x_ns = (cons node y (get_neighbors x N g ux)) in % add y as a nieghbor of x
%         let y_ns = (cons node x (get_neighbors y N g uy)) in % add x as a nieghbor of y
%           match g with
%            mkgraph _ arr _ => 
%              let add_to_x = (warray_set <list word> x x_ns N arr ux) in
%                (mkgraph N (warray_set <list word> y y_ns N add_to_x uy)) % prove nodes are still bounded
%           end
%     | tt => g
%     end.

% Define remove_edge :=

% Define connected_h :=
%   fun connected_h(x y:node)(l:<list node>)(N:word)(g:<graph N>)(mv : <uwarray bool N>)
%     (connected_f : Fun(x' y':node)(N':word)(g':<graph N>)(mv' : <uwarray bool N>)(ux : { (ltword x N) = tt })(uy : { (ltword y N) = tt }).bool):bool.
%     match l with
%       nil _ => ff
%     | cons _ v l' => match (eqbool (uwarray_get bool N mv v) tt) with % prove v < N 
%                        ff => (connected_f x y N g (uwarray_set bool N mv v tt)) % prove v < N
%                      | tt => (connected_h x y l' N g mv)
%                      end
%     end.

% Define connected :=
%   fun connected(x y:node)(N:word)(g:<graph N>)(mv : <uwarray bool N>)
%                (ux : { (ltword x N) = tt })
%                (uy : { (ltword y N) = tt }):bool.
%     match (eqword x y) with

%       ff => let neighbors = (get_neighbors x N g) in
%               (connected_h x y neighbors N g mv connected)
%     | tt => tt
%     end.
                                         
% create 2 warrays; one which satisfies the nodes_bounded property,
% one which does not
Define warray_bounded := let l = (cons word word0 (cons word word2 (nil word))) in 
  (warray_new <list word> word3 l).
Define warray_unbounded := let l = (cons word word0 (cons word word3 (nil word))) in 
  (warray_new <list word> word3 l).

% test nodes_bounded
Interpret (nodes_bounded word3 warray_bounded).      
Interpret (nodes_bounded word3 warray_unbounded).


%%%%%%
%  below we construct the following graph for testing:
%
%     0    3
%      \
%  1 -- 2
%
%%%%%
% make lists of neighbors (adjacent nodes) for each the nodes of our graph
Define node0_list := (cons word word2 (nil word)).
Define node1_list := (cons word word2 (nil word)).
Define node2_list := (cons word word2 (cons word word1 (nil word))).
Define node3_list := (nil word).

% populate an warray with lists of neighboring nodes
Define nodes := let set_node0 = (warray_new <list word> word4 node0_list) in
  let set_node1 = (warray_set <list word> word1 node1_list word4 set_node0 join (ltword word1 word4) tt) in
    let set_node2 = (warray_set <list word> word2 node2_list word4 set_node1 join (ltword word2 word4) tt) in
      (warray_set <list word> word3 node3_list word4 set_node2 join (ltword word3 word4) tt).

Define test_graph := (mkgraph word4 nodes join (nodes_bounded word4 nodes) tt).

% test get_neighbors
Interpret (get_neighbors word0 word4 test_graph join (ltword word0 word4) tt). 

% test adjacent
Interpret (adjacent word0 word0 word4 test_graph).
Interpret (adjacent word0 word2 word4 test_graph).
Interpret (adjacent word0 word1 word4 test_graph).

% test connected
% Interpret (let mv = (uwarray_new bool word4 ff) in
%   (connected word0 word2 word4 g mv 
%     join (ltword word0 word4) tt 
%     join (ltword word2 word4) tt)).

%%%%% Ideas %%%%%
% Define cyclic :=
% Define bipartite :=
% Define tree := % connected acyclic graph
% Define shortest_path :=    
