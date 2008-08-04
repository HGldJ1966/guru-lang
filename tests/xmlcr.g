Include "../lib/stdio.g".

Set "print_parsed".

Define check_XML :=
 fun check_XML(unique stdin:stdin_t)(stack:<list <list char>>)(current: <list char>)(flag:char):bool.
 match (next_char stdin) with 
       getc_none stdin=> dec current dec stdin 
                   match stack with
                     nil A => tt
                   | cons A a l => dec a dec l ff
                   end
 | getc_char a stdin =>
 match (eqchar flag Co) with %If Openbracket is found, check next char for type of tag
   ff => match (eqchar flag Cd) with %If the end of a string has been found, wait until bracket is closed
      ff => match (eqchar flag Cc) with %If a slash has been found in a tag, make sure it is closing a tag
          ff => match (eqchar flag Cp) with %If a slash has been found starting a tag, compare against the stack
             ff => match (eqchar flag Cb) with %If a bash tag has been found, find out what kind
                ff => match (eqchar flag Cw) with %First check for comment
                   ff => match (eqchar flag Cx) with %Second check for comment
                      ff => match (eqchar flag Cy) with %Third check for comment
                         ff => match (eqchar flag Cz) with %Fourth check for comment
                            ff => match (eqchar flag Cq) with %If in ? tag, look for ? until close
                               ff => match (eqchar flag Cr) with %If a ? is found in a ? tag, make sure it is closing
                                  ff => match (eqchar flag Ce) with %Check for a ! on the stack if a closing tag is found
                                     ff => match (eqchar flag Cs) with %Check for the space at the end of a string
                                        ff => match (eqchar a Clt) with
                                           ff => match (eqchar a Cgt) with
                                              ff => (check_XML stdin stack current Cn)
                                            | tt => (check_XML stdin stack current Ce)
                                            end
                                         | tt => (check_XML stdin stack current Co)
                                         end
                                      | tt => match (eqchar a Csp) with
                                           ff => match (eqchar a Csl) with
                                              ff => match (eqchar a Cgt) with
                                                 ff => (check_XML stdin stack (cons char a current) Cs)
                                               | tt => (check_XML stdin (cons <list char> current stack) (nil char) Cn)
                                               end
                                            | tt => (check_XML stdin stack current Cc)
                                            end
                                         | tt => (check_XML stdin stack current Cd)
                                         end
                                      end
                                   | tt => dec current
                                           match stack by x y return bool with
                                        nil A  => dec stdin ff
                                      | cons A a l => let s = (cons char Cba (nil char)) in
					  match (eqlist char cast a by symm inj <list *> y s eqchar) by x' y' return bool with
					     ff => dec a dec l dec stdin dec s ff
                                           | tt => dec a dec s 
                                                   (check_XML stdin cast l by cong <list *> symm inj <list *> y (nil char) Cn)
			                   end
                                       end
                                   end
                                | tt => match (eqchar a Cgt) with
                                     ff => (check_XML stdin stack current Cq)
                                   | tt => dec current (check_XML stdin stack (nil char) Cn)
                                   end
                                end
                             | tt => match (eqchar a Cqu) with
                                  ff => (check_XML stdin stack current Cq)
                                | tt => (check_XML stdin stack current Cr)
                                end 
                             end
                          | tt => match (eqchar a Cgt) with
                               ff => (check_XML stdin stack current Cx)
                             | tt => dec current (check_XML stdin stack (nil char) Cn)
                             end
                          end
                       | tt => match (eqchar a Cmi) with
                            ff => (check_XML stdin stack current Cx)
                          | tt => (check_XML stdin stack current Cz)
                          end
                       end
                    | tt => match (eqchar a Cmi) with
                         ff => (check_XML stdin stack current Cx)
                       | tt => (check_XML stdin stack current Cy)
                       end
                    end
                 | tt => match (eqchar a Cmi) with
                      ff => (check_XML stdin stack current Cb)
                    | tt => (check_XML stdin stack current Cx)
                    end
                 end
              | tt => match (eqchar a Cmi) with
                   ff => match (eqchar a Clt) with
                      ff => match (eqchar a Cgt) with
                         ff =>  (check_XML stdin stack current Cb)
                       | tt => dec current (check_XML stdin stack (nil char) Cn)
                       end
                    | tt => (check_XML stdin (cons <list char> (cons char Cba (nil char)) stack) current Co)
                    end
                 | tt => (check_XML stdin stack current Cw)
                 end
              end
           | tt => match (eqchar a Cgt) with
                ff => (check_XML stdin stack (cons char a current) Cp)
	      | tt => match stack by x y return bool with
                   nil A => dec current dec stdin ff
                 | cons A a l => match (eqlist char cast a by symm inj <list *> y current eqchar) with
                      ff => dec current dec a dec l dec stdin ff
                    | tt => dec current dec a (check_XML stdin cast l by cong <list *> symm inj <list *> y (nil char) Cn)
                    end
                 end
              end
           end
        | tt => dec current match (eqchar a Cgt) with
             ff => dec stack dec stdin ff
           | tt => (check_XML stdin stack (nil char) Cn)
           end
        end
     | tt => match (eqchar a Cgt) with
         ff => match (eqchar a Csl) with
            ff => (check_XML stdin stack current Cd)
          | tt => (check_XML stdin stack current Cc)
          end
       | tt => (check_XML stdin (cons <list char> current stack) (nil char) Cn)
       end
     end
 | tt => match (eqchar a Cqu) with
      ff => match (eqchar a Cba) with
         ff => match (eqchar a Csl) with
            ff => (check_XML stdin stack (cons char a current) Cs)
          | tt => (check_XML stdin stack current Cp)
          end
       | tt => (check_XML stdin stack current Cb)
       end
    | tt => (check_XML stdin stack current Cq)
    end
  end
end.

%-
Define main := fun main(unique stdin:stdin_t).
	let fin = fun(ret:char). let ign = (print_char ret) in let ign = (print_char Cnl) in nil in
	match (check_XML stdin nil <list <list char>> nil <list char> Cn) with
		ff => (fin CF)
	      | tt => (fin CT)
	      end.
-%

Define main :=
  fun(unique stdin:stdin_t).
    let fin = fun(ret:char). let ign = (print_char ret) in 
                             let ign = (print_char Cnl) in Z
    in
    match (check_XML stdin (nil <list char>) (nil char) Cn) with
      ff => (fin CF)
    | tt => (fin CT)
    end.

Compile main to "xmlcr.c".
