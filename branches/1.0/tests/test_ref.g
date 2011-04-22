Include "../lib/ref.g".
Include "../lib/pb_stdio.g".

Define onea := (S Z).
Define twoa := (S (S Z)).

Define test :=
  let r = (mk_ref nat onea) in 
  match (get_uniquew <ref nat> r) with
    mk_get_uniquew_t _ pinned r1  =>
      let r2 = (write_ref nat twoa pinned r1) in
      do
        (consume_uniquew <ref nat> r2) 
        let r3 = (unpin_unique <ref nat> pinned) in
        let rr = (inspect_unique <ref nat> r3) in
        let x = (read_ref nat rr) in
        do
          (consume_unique <pb_stdio_t tt> (pb_print_nat pb_stdio x))
          (consume_unique <ref nat> r3)
        end
      end
  end.

%Set "debug_to_carraway".
%Set "debug_eta_expand".
Set "debug_stages".
Set "debug_simulate".
Set "debug_refs".
%Set "debug_carraway_app".
%Set "debug_carraway_match".

Compile test to "test_ref.c".
      