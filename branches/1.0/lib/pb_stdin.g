Include "reader.g".

% we would need higher kinds to build a pushback reader from any reader.

Inductive pb_stdin_t : type :=
 mk_pb_stdin : Fun(s:string)(unique stdin:stdin_t).pb_stdin_t.

Define pb_next_char :=
  fun(unique pb_stdin : pb_stdin_t):unique <getc_t pb_stdin_t>.
    match pb_stdin with
      mk_pb_stdin str stdin =>
        match str with
          nil ign => 
          match (next_char stdin) with
            getc_none ign stdin => 
              (getc_none pb_stdin_t 
                 (mk_pb_stdin inc stringn stdin))
          | getc_char ign a stdin => 
              (getc_char pb_stdin_t a
                (mk_pb_stdin inc stringn stdin))
          end
        | cons ign a str => 
          (getc_char pb_stdin_t a 
             (mk_pb_stdin str stdin))
        end
    end.
            
Define pb_push :=
  fun(unique pb_stdin:pb_stdin_t)(c:char):unique pb_stdin_t.
    match pb_stdin with
      mk_pb_stdin str stdin =>
        (mk_pb_stdin (stringc c str) stdin)
    end.
    

Define pb_stdin_reader := (mk_reader pb_stdin_t pb_next_char).