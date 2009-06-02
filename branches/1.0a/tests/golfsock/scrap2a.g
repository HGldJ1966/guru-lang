                  abbrev symctxt_nothing = 
                    foralli(us:{ (trie_interp symbols) = (append L1 L2) }).
                      trans join G
                                 (map unit fun(u).snd 
                                    (trie_interp symbols))
                      trans cong (map unit fun(u).snd *) us
                            [map_append <pair string <pair nat trm>>
                               <pair nat trm> Unit unit 
                               fun(u:Unit).(snd string <pair nat trm>)
                               L1 L2] in

