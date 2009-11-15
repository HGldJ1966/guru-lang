Include "list.g".
Include "fiber.g".

Define type_family_abbrev vec := fun( A : type )( n : nat ). <fiber <list A> nat (length A) n>.



%(mk_homomorphism <list A> nat length append plus ...)