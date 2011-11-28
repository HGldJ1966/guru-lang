Include trusted "../lib/list.g".

% member (early terminating one)
Define member2 : Fun(A:type)
                    (eqA:Fun(^#owned x1 x2:A).bool)
                    (^#owned x:A)
                    (^#owned l:<list A>).bool :=
  fun(A:type)
     (eqA:Fun(^#owned x1 x2:A).bool)
     (^#owned x:A)
     (^#owned l:<list A>).
  (list_any A (eqA x) l).
